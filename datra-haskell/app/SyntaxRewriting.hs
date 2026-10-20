{-# LANGUAGE LambdaCase #-}

-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Source layout has disappeared at this boundary: application spines are
-- matched directly, while an 'AtlasMap' supplies the contextual boundary for
-- block captures.
module SyntaxRewriting
  ( SyntaxContext (..)
  , SyntaxRewriteFailure (..)
  , rewriteExplicitSyntax
  , rewriteImplicitSyntax
  ) where

import Control.Applicative ((<|>))
import DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , bindingNames
  , dependentDeclaration
  , dependentDeclarationNameExpression
  )
import Data.List (nub, nubBy)
import Data.Maybe (maybeToList)
import Data.Set qualified as Set
import DatraLanguage.AST
import DatraLanguage.AST.Source (renderSourceExpression)
import Parsing (inferredFunction)
import DatraTypes
  ( EvaluatedFunction (functionBody)
  , EvaluatedFunctionBody (EvaluatedSyntaxFunctionBody)
  , InterpretedValue
  , booleanCondition
  , eitherValue
  , interpretedFunction
  , interpretedSemanticResult
  , subfederationValues
  )
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , syntaxHoleValue
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , DependentSyntaxRule (..)
  , DependentSyntaxInvocation (..)
  , contextualSyntaxRulesFor
  , declarationRules
  , normalizeSyntaxExpansion
  , syntaxDependentRule
  , syntaxRuleAdapter
  , syntaxTemplateLiteralPrefix
  )
import SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , matchSyntaxRulesWith
  )
import SyntaxTemplateAdmissibility
  ( syntaxTemplatesOverlap )
import SyntaxTemplateProjection
  ( applicationFrom
  , applicationFromMaybe
  , applicationPhrase
  , applicationSpine
  , directApplicationSplit
  , leftInfixContext
  , literalExpression
  , matchesLiteral
  , rightInfixContext
  , stripTrailingLiteralAssignment
  , syntaxProjectionCandidates
  )

data SyntaxRewriteFailure
  = MissingImplicitBlockResult
  | InvalidPrivateOptionalArgumentName
  | AmbiguousBareSkipApplication
  | OverlappingDependentDeclarations String String
  | NonInjectiveDependentDeclaration String
  deriving (Eq, Show)

-- Evaluation callbacks share a lexical scope. Entering a contextual expression
-- creates a child scope for every callback, including typed hole validation.
data SyntaxContext = SyntaxContext
  { contextClassify :: ClassifyHoles
  , contextCapture :: CaptureHole
  , contextScopeRules :: ScopeRules
  , contextEvaluate :: [Expression] -> Expression -> Maybe InterpretedValue
  , contextEnter :: [Expression] -> Maybe Expression -> SyntaxContext
  }

data RewriteEnvironment = RewriteEnvironment
  { rewriteContext :: SyntaxContext
  , rewriteRules :: [RewriteRule]
  , rewriteDeclarations :: [Expression]
  , rewriteStrictCaptures :: Bool
  , rewriteClassifyHoles :: ClassifyHoles
  , rewriteScopeRules :: ScopeRules
  , rewriteEvaluate :: [Expression] -> Expression -> Maybe InterpretedValue
  }

-- Cache template shapes and retain the implementation's lexical evaluator.
-- A later contextual input must not rebind a syntax implementation's `it`.
data RewriteRule = RewriteRule
  { rewriteRule :: SyntaxRule
  , rewriteRuleLiteralPrefix :: [String]
  , rewriteRuleLiterals :: Set.Set String
  , rewriteRuleBlockShape :: Maybe ([String], String)
  , rewriteRuleSequenceFunctionBodyShape :: Maybe [String]
  , rewriteRuleContinuations :: [(String, [String])]
  , rewriteRuleEvaluation :: Maybe (Expression -> Maybe InterpretedValue)
  , rewriteRuleHoleFamilies :: [Maybe InterpretedValue]
  }

compileRewriteRule :: SyntaxRule -> RewriteRule
compileRewriteRule rule = RewriteRule
  { rewriteRule = rule
  , rewriteRuleLiteralPrefix = syntaxTemplateLiteralPrefix rule
  , rewriteRuleLiterals = Set.fromList
      [ literal | SyntaxLiteral literal <- pieces ]
  , rewriteRuleBlockShape = blockShapeFromPieces pieces
  , rewriteRuleSequenceFunctionBodyShape =
      sequenceFunctionBodyShapeFromPieces pieces
  , rewriteRuleContinuations = continuationContexts pieces
  , rewriteRuleEvaluation = Nothing
  , rewriteRuleHoleFamilies =
      [ Nothing | SyntaxHole _ <- pieces ]
  }
  where
    pieces = syntaxTemplatePieces (syntaxTemplate rule)

rewriteRuleName :: RewriteRule -> String
rewriteRuleName = syntaxName . rewriteRule

rewriteRuleImplementation :: RewriteRule -> Maybe Expression
rewriteRuleImplementation = syntaxRuleAdapter . rewriteRule

ruleHoleKinds :: RewriteRule -> [SyntaxHoleKind Expression]
ruleHoleKinds = foldr collect []
  . syntaxTemplatePieces . syntaxTemplate . rewriteRule
  where
    collect (SyntaxHole kind) remaining = kind : remaining
    collect SyntaxLiteral {} remaining = remaining

rewriteRulesOverlap :: RewriteRule -> RewriteRule -> Bool
rewriteRulesOverlap left right
  | distinctLiteralHeads leftTemplate rightTemplate = False
  | otherwise = syntaxTemplatesOverlap
      (holeOverlaps left right) leftTemplate rightTemplate
  where
    leftTemplate = syntaxTemplate (rewriteRule left)
    rightTemplate = syntaxTemplate (rewriteRule right)
    distinctLiteralHeads
        (SyntaxTemplate (SyntaxLiteral leftHead : _))
        (SyntaxTemplate (SyntaxLiteral rightHead : _)) =
      leftHead /= rightHead
    distinctLiteralHeads _ _ = False
    holeOverlaps leftRule rightRule leftHole rightHole =
      case (leftHole, rightHole) of
        (ExpressionSyntaxHole {}, _) -> True
        (_, ExpressionSyntaxHole {}) -> True
        _ | sameHoleClass leftHole rightHole ->
              case (holeFamily leftRule leftHole,
                    holeFamily rightRule rightHole) of
                (Just leftValue, Just rightValue) ->
                  case eitherValue leftValue rightValue of
                    Right _ -> False
                    Left _ -> True
                _ -> True
          | otherwise -> False
    holeFamily compiled kind = lookup kind
      (zip (ruleHoleKinds compiled) (rewriteRuleHoleFamilies compiled)) >>= id

sameHoleClass
  :: SyntaxHoleKind value
  -> SyntaxHoleKind other
  -> Bool
sameHoleClass ExpressionSyntaxHole {} ExpressionSyntaxHole {} = True
sameHoleClass BlockSyntaxHole {} BlockSyntaxHole {} = True
sameHoleClass FunctionBodySyntaxHole {} FunctionBodySyntaxHole {} = True
sameHoleClass DeclarationSyntaxHole {} DeclarationSyntaxHole {} = True
sameHoleClass DependentIdentifierSyntaxHole {}
    DependentIdentifierSyntaxHole {} = True
sameHoleClass ValueSyntaxHole {} ValueSyntaxHole {} = True
sameHoleClass _ _ = False

-- Contextual surface names exist only inside syntax nodes whose evaluator
-- installs the corresponding private binding. Entering such a node replaces
-- an outer rule with the node's fresh contextual binding; declarations within
-- the node may still shadow it through 'advanceScope'.
withContextualSyntax :: [String] -> RewriteEnvironment -> RewriteEnvironment
withContextualSyntax surfaces environment = environment
  { rewriteRules = contextual <> filter (not . contextualName) existing }
  where
    contextual = map compileRewriteRule (contextualSyntaxRulesFor surfaces)
    existing = rewriteRules environment
    names = map rewriteRuleName contextual
    contextualName rule = rewriteRuleName rule `elem` names

type ClassifyHoles =
  [Expression]
  -> [SyntaxHoleKind Expression]
  -> [(SyntaxHoleKind Expression, Maybe InterpretedValue)]

type CaptureHole =
  Bool
  -> [Expression]
  -> [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

-- Rules exported by the value on the left of a scope access. They are active
-- only while rewriting that access's right operand.
type ScopeRules = [Expression] -> Expression -> [SyntaxRule]

rewriteEnvironment
  :: SyntaxContext -> [SyntaxRule] -> [Expression] -> RewriteEnvironment
rewriteEnvironment context rules declarations = RewriteEnvironment
  context (map compileRewriteRule rules) declarations True
  (contextClassify context) (contextScopeRules context) (contextEvaluate context)

rewriteExplicitSyntax
  :: SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteExplicitSyntax context rules declarations =
  rewriteStandalone (contextCapture context)
    (rewriteEnvironment context rules declarations)

rewriteImplicitSyntax
  :: SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
rewriteImplicitSyntax context rules declarations entries = do
  let capture = contextCapture context
      initial = rewriteEnvironment context rules declarations
  -- Discover recursive declarations through the same block pass used by
  -- explicit resources, but retain the raw syntax for the implicit delimiter
  -- pass. In particular, operators surrounding @yield@ must be rewritten only
  -- after that boundary has been identified.
  (discovered, _) <- rewriteSequence capture initial entries
  resolveImplicitBlock capture
    (recursiveRewriteEnvironment True initial discovered) [] entries

-- Keep visible syntax rules, while moving the declarations they depend on into
-- the evaluator's parent scope. RHS declarations belong to the new scope.
enterContext :: Maybe Expression -> RewriteEnvironment -> RewriteEnvironment
enterContext value environment = withContextualSyntax ["it"] environment
  { rewriteContext = nested
  , rewriteDeclarations = []
  , rewriteClassifyHoles = contextClassify nested
  , rewriteScopeRules = contextScopeRules nested
  , rewriteEvaluate = contextEvaluate nested
  }
  where
    nested = contextEnter (rewriteContext environment)
      (rewriteDeclarations environment) value

resolveImplicitBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
resolveImplicitBlock capture initial = go initial
  where
    go environment rewrittenPrefix remaining =
      tryRules environment rewrittenPrefix remaining
        >>= \case
          Just expressionValue -> Right expressionValue
          Nothing -> case remaining of
            [] -> case rewrittenPrefix of
              [scoped@ScopeAccess {}] -> Right scoped
              [imported@Import {}] -> Right imported
              [block@Begin {}] -> Right (Begin [] block)
              _ -> Right (Begin rewrittenPrefix (AtlasMap []))
            entry : rest -> do
              (rewritten, trailing) <-
                rewriteWithTail False capture environment entry rest
              let next = advanceScope environment rewritten
              go next (rewrittenPrefix <> [rewritten]) trailing

    tryRules environment rewrittenPrefix remaining =
      firstSuccessful
        [ implicitRule environment rewrittenPrefix remaining rule shape
        | rule <- rewriteRules environment
        , Just shape <- [rewriteRuleBlockShape rule]
        ]

    firstSuccessful [] = Right Nothing
    firstSuccessful (candidate : rest) = do
      result <- candidate
      case result of
        Just value -> Right (Just value)
        Nothing -> firstSuccessful rest

    implicitRule environment rewrittenPrefix remaining rule
        (prefix, delimiter) =
      consumeBlock capture environment delimiter [] remaining >>= \case
        Nothing -> Right Nothing
        Just (rewrittenSuffix, nested, rawResult, trailing) -> do
          (result, finalTrailing) <-
            rewriteWithTail True capture nested rawResult trailing
          let blockEntries = rewrittenPrefix <> rewrittenSuffix
              candidate = applicationFrom
                (map literalExpression prefix
                  <> [ AtlasMap blockEntries
                     , literalExpression delimiter
                     , result
                     ])
              captureInScope previous kind captured =
                capture (rewriteStrictCaptures nested)
                  (rewriteDeclarations nested) previous kind captured
          case matchSyntaxRulesWith captureInScope
              [rewriteRule rule] candidate of
            Right matched ->
              directSyntaxFunctionExpansion nested (Just rule) matched >>= \case
                Begin bindings finalResult
                  | null finalTrailing ->
                      Right (Just (if explicitBlockAtHead
                        then Begin rewrittenPrefix (Begin bindings finalResult)
                        else Begin bindings finalResult))
                _ -> Right Nothing
            Left NoMatchingSyntaxTemplate -> Right Nothing
      where
        explicitBlockAtHead = case remaining of
          first : _ -> 0 `elem`
            matchingStarts writtenHead (applicationPhrase first)
          [] -> False
        writtenHead
          | null prefix = [rewriteRuleName rule]
          | otherwise = prefix

rewriteSequence
  :: CaptureHole
  -> RewriteEnvironment
  -> [Expression]
  -> Either SyntaxRewriteFailure ([Expression], RewriteEnvironment)
rewriteSequence capture initial rawEntries = do
  -- A recursive syntax modifier can itself be declared using syntax that is
  -- still being bootstrapped in the same block. Run one disposable discovery
  -- pass with declaration-shaped application operands provisionally visible;
  -- only declarations that actually rewrite to @Let@ survive into the real
  -- fixed point below.
  (provisional, _) <- pass [] discoveryEnvironment rawEntries
  let recursive = filter isLetDeclarationExpression provisional
  fixedPoint provisional recursive
  where
    discoveryEnvironment = foldl introduceCandidates initial rawEntries
    introduceCandidates environment entry =
      foldl advanceScope environment (declarationCandidates entry)
    declarationCandidates expressionValue =
      if maybe False (const True) (dependentDeclaration expressionValue)
        then [expressionValue]
        else case expressionValue of
          FunctionApplication function argument ->
            declarationCandidates function <> declarationCandidates argument
          SyntaxBoundary inner -> declarationCandidates inner
          _ -> []

    fixedPoint stable recursiveDeclarations = do
      (rewritten, tentativeEnvironment) <-
        pass [] (recursiveRewriteEnvironment False initial stable) rawEntries
      let discovered = filter isLetDeclarationExpression rewritten
      if discovered == recursiveDeclarations
        then if not (rewriteStrictCaptures initial)
          then do
            validateDependentDeclarations rewritten
            Right (rewritten, tentativeEnvironment)
          else do
            (strictlyRewritten, strictEnvironment) <-
              strictPass rewritten 0 []
                (recursiveRewriteEnvironment True initial rewritten) rawEntries
            validateDependentDeclarations strictlyRewritten
            Right (strictlyRewritten, strictEnvironment)
        else fixedPoint rewritten discovered

      where
        -- Let declarations are visible throughout their block, but they retain
        -- their source positions when their lexical scopes are assembled.
        -- Moving them in front of preceding ordinary declarations makes a
        -- recursive target such as Int lose access to an earlier Maybe.
        strictPass _ _ reversed environment [] =
          Right (reverse reversed, environment)
        strictPass stableEntries position reversed environment
            (entry : remaining) = do
          let scoped = environment
                { rewriteDeclarations =
                    scopedBlockDeclarations initial position stableEntries
                }
          (rewrittenEntry, trailing) <-
            rewriteWithTail False capture scoped entry remaining
          let next = advanceScope scoped rewrittenEntry
          strictPass stableEntries (position + 1)
            (rewrittenEntry : reversed) next trailing

    validateDependentDeclarations = go initial []
      where
        go _ _ [] = Right ()
        go environment earlier (entry : remaining) = do
          let resolved = resolveDependentDeclarationHead environment entry
              currentRules = declarationRules resolved
              currentDeclaration = dependentDeclaration resolved
              currentFamily = compileScopedRewriteRules environment
                (rewriteDeclarations environment) currentRules
          case currentDeclaration of
            Nothing -> pure ()
            Just declaration -> mapM_
              (validateFamily
                (declarationLabel declaration)
                (greedyDeclaration declaration)
                currentFamily)
              earlier
          if isValDependentDeclaration resolved
            then mapM_ (validateInjective environment)
              [ (rule, dependent)
              | rule <- currentRules
              , Just dependent <- [syntaxDependentRule rule]
              , DependentSyntaxLookup {} <-
                  [dependentSyntaxInvocation dependent]
              ]
            else Right ()
          let retained = case currentDeclaration of
                Nothing -> earlier
                Just declaration -> earlier <>
                  [ ( declarationLabel declaration
                    , greedyDeclaration declaration
                    , currentFamily
                    )
                  ]
          go (advanceScope environment entry) retained remaining

        declarationLabel = renderSourceExpression
          . dependentDeclarationNameExpression

        greedyDeclaration declaration = case
            dependentDeclarationNameExpression declaration of
          GreedyStringTemplate {} -> True
          SyntaxBoundary (GreedyStringTemplate {}) -> True
          _ -> False

        validateFamily currentLabel currentGreedy currentFamily
            (previousLabel, previousGreedy, previousFamily) =
          if currentGreedy || previousGreedy || and
              [ branchesCompatible previous current
              | previous <- previousFamily
              , current <- currentFamily
              ]
            then Right ()
            else Left (OverlappingDependentDeclarations
              previousLabel currentLabel)

        branchesCompatible previous current =
          not (rewriteRulesOverlap previous current)

        validateInjective environment (rule, dependent)
          | null captures = Right ()
          | identityImplementation implementation = Right ()
          | otherwise =
              case (evaluate input, evaluate output) of
                (Just inputValue, Just outputValue)
                  | equivalentFederations inputValue outputValue -> Right ()
                _ -> Left (NonInjectiveDependentDeclaration
                  (syntaxName rule))
          where
            captures = dependentSyntaxCaptures dependent
            implementation = dependentSyntaxImplementation dependent
            input = ArgumentMap (zipWith captureMember captures
              (templateCaptureTypes rule))
            output = In input implementation
            evaluate = rewriteEvaluate environment
              (rewriteDeclarations environment)

        captureMember (Just (name, annotation)) _ =
          IdentifierOperation name annotation Nothing
        captureMember Nothing annotation = annotation

        templateCaptureTypes = foldr captureType []
          . syntaxTemplatePieces . syntaxTemplate
        captureType (SyntaxHole kind) rest = syntaxHoleValue kind : rest
        captureType SyntaxLiteral {} rest = rest

        equivalentFederations left right =
          interpretedSemanticResult left == interpretedSemanticResult right
            || (isSubfederation left right && isSubfederation right left)
        isSubfederation source target =
          case subfederationValues source target >>= booleanCondition of
            Right accepted -> accepted
            Left _ -> False

        identityImplementation expressionValue = case expressionValue of
          IdentifierReference (IdentifierString "it") -> True
          InModule _ value -> identityImplementation value
          SyntaxBoundary value -> identityImplementation value
          _ -> isContextualAccessOf
            (IdentifierString "_it") expressionValue

    pass reversed environment [] = Right (reverse reversed, environment)
    pass reversed environment (entry : remaining) = do
      (rewritten, trailing) <-
        rewriteWithTail False capture environment entry remaining
      let next = advanceScope environment rewritten
      pass (rewritten : reversed) next trailing
    isValDependentDeclaration expressionValue = case expressionValue of
      Val value -> maybe False (const True) (dependentDeclaration value)
      Let value -> isValDependentDeclaration value
      In _ value -> isValDependentDeclaration value
      _ -> False

isLetDeclarationExpression :: Expression -> Bool
isLetDeclarationExpression expressionValue =
  maybe False dependentDeclarationIsLet
    (dependentDeclaration expressionValue)

scopedBlockDeclarations
  :: RewriteEnvironment
  -> Int
  -> [Expression]
  -> [Expression]
scopedBlockDeclarations initial position entries =
  filter (not . shadowsOuter) (rewriteDeclarations initial) <> local
  where
    local =
      [ declaration
      | (index, declaration) <- zip [0 :: Int ..] entries
      , index < position || isLetDeclarationExpression declaration
      ]
    localNames = concatMap bindingNames local
    shadowsOuter declaration = any (`elem` localNames)
      (bindingNames declaration)

recursiveRewriteEnvironment
  :: Bool
  -> RewriteEnvironment
  -> [Expression]
  -> RewriteEnvironment
recursiveRewriteEnvironment strict initial entries =
  (foldl introduceRecursive initial
    [ (position, declaration)
    | (position, declaration) <- zip [0 :: Int ..] entries
    , isLetDeclarationExpression declaration
    ])
      { rewriteDeclarations = rewriteDeclarations initial
      , rewriteStrictCaptures = strict
      }
  where
    introduceRecursive environment (position, declaration) =
      let visible = scopedBlockDeclarations initial position entries
      in advanceScope
          (environment { rewriteDeclarations = visible })
          declaration

rewriteStandalone
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandalone capture environment value = do
  (rewritten, _) <- rewriteWithTail False capture environment value []
  pure rewritten

rewriteWithTail
  :: Bool
  -> CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
rewriteWithTail allowNestedContinuation capture environment value trailing
  | GreedyStringTemplate {} <- value = Right (value, trailing)
  | let (continued, remaining) =
          continueIncompleteExpression environment value trailing
  , length remaining < length trailing =
      rewriteWithTail allowNestedContinuation capture environment
        continued remaining
  | otherwise = do
      blockMatch <- matchEmbeddedBlock capture environment value trailing
      case blockMatch of
        Just (rewritten, remaining) ->
          rewriteAfterBlock allowNestedContinuation capture environment
            rewritten remaining
        Nothing -> do
          sequenceMatch <- matchSequenceFunctionBody
            capture environment value trailing
          case sequenceMatch of
            Just (rewritten, remaining) ->
              rewriteAfterBlock allowNestedContinuation capture environment
                rewritten remaining
            Nothing -> rewriteAfterBlock
              allowNestedContinuation capture environment value trailing

rewriteAfterBlock
  :: Bool
  -> CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
rewriteAfterBlock allowNestedContinuation capture environment value trailing =
  case value of
    ScopeAccess source body -> do
      rewritten <- rewriteScopeAccess capture environment source body
      pure (rewritten, trailing)
    SyntaxBoundary inner -> do
      rewritten <- rewriteStandalone capture environment inner
      pure (rewritten, trailing)
    MapSpecification source target
      | canReceiveFunctionBody target -> do
          let continuation = boundaryValue source : trailing
          (candidate, remaining) <-
            rewriteWithTail True capture environment target continuation
          if length remaining < length continuation
              && containsFunctionImplementation candidate
            then finish candidate remaining
            else finish value trailing
    IdentifierOperation name annotation given -> do
      let (rawAnnotation, rawGiven) =
            normalizeTrailingAssignment annotation given
      case rawGiven of
        Nothing -> do
          (rewrittenAnnotation, remaining) <-
            rewriteDeclarationPart (Just name) rawAnnotation
          finish
            (IdentifierOperation name rewrittenAnnotation Nothing)
            remaining
        Just original
          | original == rawAnnotation -> do
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart (Just name) original
              finish
                (IdentifierOperation name rewrittenValue
                  (Just rewrittenValue))
                remaining
          | otherwise -> do
              rewrittenAnnotation <-
                rewriteStandalone capture environment rawAnnotation
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart (Just name) original
              finish
                (IdentifierOperation name rewrittenAnnotation
                  (Just rewrittenValue))
                remaining
    IdentifierTemplateOperation parts annotation given -> do
      let contextual = enterContext Nothing environment
      rewrittenParts <- traverse (rewriteTemplatePart contextual) parts
      let (rawAnnotation, rawGiven) =
            normalizeTrailingAssignment annotation given
      case rawGiven of
        Nothing -> do
          (rewrittenAnnotation, remaining) <-
            rewriteDeclarationPart Nothing rawAnnotation
          finish
            (IdentifierTemplateOperation
              rewrittenParts rewrittenAnnotation Nothing)
            remaining
        Just original
          | original == rawAnnotation -> do
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart Nothing original
              finish
                (IdentifierTemplateOperation rewrittenParts rewrittenValue
                  (Just rewrittenValue))
                remaining
          | otherwise -> do
              rewrittenAnnotation <-
                rewriteStandalone capture environment rawAnnotation
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart Nothing original
              finish
                (IdentifierTemplateOperation rewrittenParts rewrittenAnnotation
                  (Just rewrittenValue))
                remaining
    FunctionApplication (Fun signature) body@FunctionBody {}
      | canReceiveFunctionBody signature ->
          finish (Fun (FunctionApplication signature body)) trailing
    FunctionApplication function@FunctionApplication {} body@FunctionBody {}
      | canReceiveFunctionBody function ->
          finish (inferredFunction body function) trailing
    FunctionApplication function argument
      | containsBlockStart environment argument
      , not (containsBlockStart environment function) -> do
          rewriteEmbeddedApplication capture environment value >>= \case
            Just rewritten -> finish rewritten trailing
            Nothing -> do
              rewrittenFunction <-
                rewriteStandalone capture environment function
              (rewrittenArgument, remaining) <-
                rewriteWithTail True capture environment argument trailing
              finish
                (FunctionApplication rewrittenFunction rewrittenArgument)
                remaining
    In input body -> do
      rewrittenInput <- rewriteStandalone capture environment input
      let nested = enterContext (Just rewrittenInput) environment
      (rewrittenBody, remaining) <- rewriteWithTail allowNestedContinuation
        (contextCapture (rewriteContext nested)) nested body trailing
      pure (In rewrittenInput rewrittenBody, remaining)
    MaybeThen optional branch
      | allowNestedContinuation -> do
          rewrittenOptional <- rewriteStandalone capture environment optional
          let contextual = enterContext Nothing environment
          (rewrittenBranch, remaining) <- rewriteWithTail True
            (contextCapture (rewriteContext contextual)) contextual branch trailing
          finish (MaybeThen rewrittenOptional rewrittenBranch) remaining
    FunctionApplication function argument
      | allowNestedContinuation
      , canReceiveFunctionBody function -> do
          (rewrittenFunction, remaining) <-
            rewriteWithTail True capture environment function trailing
          if length remaining < length trailing
              && containsFunctionImplementation rewrittenFunction
            then do
              rewrittenArgument <-
                rewriteStandalone capture environment argument
              finish
                (FunctionApplication rewrittenFunction rewrittenArgument)
                remaining
            else finish value trailing
    FunctionTypeExpression generics domain codomain
      | allowNestedContinuation || containsBlockStart environment codomain -> do
          rewrittenDomain <- rewriteStandalone capture environment domain
          (rewrittenCodomain, remaining) <-
            rewriteWithTail True capture environment codomain trailing
          finish
            (FunctionTypeExpression generics rewrittenDomain rewrittenCodomain)
            remaining
    Fun signature
      | allowNestedContinuation -> do
          let nested = withContextualSyntax ["this"] environment
          (rewrittenSignature, remaining) <-
            rewriteWithTail True capture nested signature trailing
          finish (Fun rewrittenSignature) remaining
      | otherwise -> do
          let nested = withContextualSyntax ["this"] environment
          rewrittenSignature <- rewriteStandalone capture nested signature
          finish (Fun rewrittenSignature) trailing
    AtlasMap entries -> do
      (rewritten, _) <- rewriteSequence capture environment entries
      finish (case rewritten of
        [] -> AtlasMap []
        [expressionValue] -> expressionValue
        expressions -> AtlasMap expressions) trailing
    ArgumentMap entries -> do
      rewritten <- traverse (rewriteStandalone capture environment) entries
      if all validArgumentMember rewritten
        then finish (ArgumentMap rewritten) trailing
        else Left InvalidPrivateOptionalArgumentName
    Begin bindings result -> do
      let contextual = withContextualSyntax ["this"] environment
      (rewrittenBindings, nested) <-
        rewriteSequence capture contextual bindings
      rewrittenResult <- rewriteStandalone capture nested result
      pure (Begin rewrittenBindings rewrittenResult, trailing)
    FunctionBody bindings result -> do
      let contextual = withContextualSyntax ["this"]
            (enterContext Nothing environment)
          nestedCapture = contextCapture (rewriteContext contextual)
      (rewrittenBindings, nested) <-
        rewriteSequence nestedCapture contextual bindings
      rewrittenResult <- rewriteStandalone nestedCapture nested result
      pure (FunctionBody rewrittenBindings rewrittenResult, trailing)
    _ -> finish value trailing
  where
    rewriteTemplatePart contextual part = case part of
      StringTemplateLiteral {} -> pure part
      StringTemplateInterpolation (SyntaxBoundary interpolation) ->
        StringTemplateInterpolation . SyntaxBoundary <$>
          rewriteStandalone (contextCapture (rewriteContext contextual))
            contextual interpolation
      StringTemplateInterpolation interpolation ->
        StringTemplateInterpolation <$>
          rewriteStandalone (contextCapture (rewriteContext contextual))
            contextual interpolation
    rewriteDeclarationPart declaredName selected =
      if allowNestedContinuation
        then rewriteWithTail True capture environment selected trailing
        else rewriteDeclaredValue declaredName selected
    rewriteDeclaredValue declaredName selected
      | canReceiveFunctionBody selected
          || ( not (directSelfAlias declaredName selected)
                && ( containsBlockStart environment selected
                      || startsBlockAtHead environment selected
                   )
             ) = do
          (candidate, remaining) <-
            rewriteWithTail True capture environment selected trailing
          if length remaining < length trailing
            then pure (candidate, remaining)
            else standalone selected
      | otherwise = standalone selected
    directSelfAlias (Just declared) (IdentifierReference referenced) =
      declared == referenced
    directSelfAlias _ _ = False
    standalone selected = do
      rewritten <- rewriteStandalone capture environment selected
      pure (rewritten, trailing)
    finish expressionValue remaining = do
      (matched, afterSyntax) <-
        matchOrdinarySyntaxWithTail
          False capture environment expressionValue remaining
      case matched of
        Conditional condition yes no
          | allowNestedContinuation -> do
              rewrittenCondition <-
                rewriteStandalone capture environment condition
              rewrittenYes <- rewriteStandalone capture environment yes
              (rewrittenNo, afterConditional) <-
                rewriteWithTail True capture environment no afterSyntax
              pure
                ( normalizeSyntaxExpansion
                    (Conditional rewrittenCondition rewrittenYes rewrittenNo)
                , afterConditional
                )
        _ -> do
          rewrittenChildren <- rewriteChildren capture environment matched
          let normalizedChildren = normalizeSyntaxExpansion rewrittenChildren
          matchOrdinarySyntaxWithTail
            True capture environment normalizedChildren afterSyntax
    boundaryValue (SyntaxBoundary inner) = inner
    boundaryValue inner = inner

normalizeTrailingAssignment
  :: Expression
  -> Maybe Expression
  -> (Expression, Maybe Expression)
normalizeTrailingAssignment annotation Nothing =
  case stripTrailingLiteralAssignment annotation of
    (rewritten, given) : _ -> (rewritten, Just given)
    [] -> (annotation, Nothing)
normalizeTrailingAssignment annotation given = (annotation, given)

canReceiveFunctionBody :: Expression -> Bool
canReceiveFunctionBody FunctionTypeExpression {} = True
-- A generic introduction followed by a body is the existing shorthand for an
-- inferred function type; deciding that does not require evaluating the bound.
canReceiveFunctionBody GenericIntroductionExpression {} = True
canReceiveFunctionBody (Fun signature) = canReceiveFunctionBody signature
canReceiveFunctionBody (SyntaxBoundary signature) =
  canReceiveFunctionBody signature
canReceiveFunctionBody (FunctionApplication function _) =
  canReceiveFunctionBody function
canReceiveFunctionBody _ = False

containsFunctionImplementation :: Expression -> Bool
containsFunctionImplementation MapSpecification {} = True
containsFunctionImplementation
    (FunctionApplication signature FunctionBody {}) =
  canReceiveFunctionBody signature
containsFunctionImplementation (Fun signature) =
  containsFunctionImplementation signature
containsFunctionImplementation (SyntaxBoundary inner) =
  containsFunctionImplementation inner
containsFunctionImplementation _ = False

rewriteChildren
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteChildren capture environment value =
  case value of
    In input body -> do
      rewrittenInput <- rewriteStandalone capture environment input
      let nested = enterContext (Just rewrittenInput) environment
      rewrittenBody <- rewriteStandalone
        (contextCapture (rewriteContext nested)) nested body
      pure (In rewrittenInput rewrittenBody)
    MaybeThen optional branch -> do
      rewrittenOptional <- rewriteStandalone capture environment optional
      let contextual = enterContext Nothing environment
      rewrittenBranch <- rewriteStandalone
        (contextCapture (rewriteContext contextual)) contextual branch
      pure (MaybeThen rewrittenOptional rewrittenBranch)
    ScopeAccess source body ->
      rewriteScopeAccess capture environment source body
    ReverseMapSpecification target source ->
      MapSpecification
        <$> rewriteStandalone capture environment source
        <*> rewriteStandalone capture environment target
    ReverseOverload supplied defaults ->
      Overload
        <$> rewriteStandalone capture environment defaults
        <*> rewriteStandalone capture environment supplied
    ReverseSafeOverload supplied defaults ->
      SafeOverload
        <$> rewriteStandalone capture environment defaults
        <*> rewriteStandalone capture environment supplied
    MapAccess (AtlasMap [binder, body]) insertion
      | Just declaration <- dependentBinderDeclaration binder -> do
          rewrittenBinder <- rewriteStandalone capture environment binder
          let nested = advanceScope environment declaration
          rewrittenBody <- rewriteStandalone capture nested body
          rewrittenInsertion <-
            rewriteStandalone capture environment insertion
          pure (MapAccess
            (AtlasMap [rewrittenBinder, rewrittenBody])
            rewrittenInsertion)
    -- Template declarations have already rewritten their interpolation
    -- expressions and both RHS components in 'rewriteAfterBlock'. Traversing
    -- them again here would unwrap the sole explicit 'SyntaxBoundary' which
    -- distinguishes an evaluated declaration head from an ordinary capture.
    IdentifierTemplateOperation {} -> pure value
    -- The operand describes template structure. Its ordinary sequence,
    -- either, and optional nodes are interpreted by GreedyStringTemplate and
    -- must not themselves be rewritten as executable surface syntax.
    GreedyStringTemplate {} -> pure value
    _ | Just (left, rebuild) <- leftInfixContext value -> do
      embedded <- rewriteEmbeddedApplication capture environment left
      case embedded of
        Just rewritten -> pure (rebuild rewritten)
        Nothing -> traverseExpressionChildren
          (rewriteStandalone capture environment) value
    FunctionApplication _ Skip -> Left AmbiguousBareSkipApplication
    FunctionApplication {} ->
      case directSyntaxFunctionExpansion environment Nothing value of
        Right expanded | isDirectBlockExpansion expanded ->
          rewriteDirectControlExpansion capture environment expanded
        _ -> do
          embedded <- rewriteEmbeddedApplication capture environment value
          case embedded of
            Just rewritten -> pure rewritten
            Nothing -> do
              rewritten <- rewriteApplicationSpineChildren
                (rewriteStandalone capture environment) value
              directSyntaxFunctionApplication capture environment rewritten
    _ -> traverseExpressionChildren
      (rewriteStandalone capture environment) value

-- A neutral left-associated application is one syntactic boundary. Rewriting
-- its nested function prefixes independently can execute a syntax function on
-- a token that belongs to a larger infix or template match. Parentheses remain
-- explicit 'SyntaxBoundary' nodes, so intentionally nested applications still
-- receive their own rewrite pass.
rewriteApplicationSpineChildren
  :: (Expression -> Either SyntaxRewriteFailure Expression)
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteApplicationSpineChildren rewrite value =
  applicationFrom <$> traverse rewrite (function : arguments)
  where
    (function, arguments) = applicationSpine value

-- Syntax-backed declarations are ordinary functions whose function bodies
-- can expand AST captures before runtime evaluation.
directSyntaxFunctionApplication
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
directSyntaxFunctionApplication capture environment application = do
  expanded <- directSyntaxFunctionExpansion environment Nothing application
  rewriteDirectControlExpansion capture environment expanded

directSyntaxFunctionExpansion
  :: RewriteEnvironment
  -> Maybe RewriteRule
  -> Expression
  -> Either SyntaxRewriteFailure Expression
directSyntaxFunctionExpansion environment selectedRule application =
  case syntaxApplicationSpine application of
    (_, [IdentifierReference (IdentifierString literal)])
      | Nothing <- selectedRule
      , any (Set.member literal . rewriteRuleLiterals) (rewriteRules environment) ->
          Right application
    (function, [argument]) ->
      choose adapters []
      where
        captures expected = case expected of
          Just 0 -> []
          Just 1 -> [argument]
          _ -> directSyntaxArguments argument
        adapters = do
          (expressionValue, expected, evaluate) <- case selectedRule of
            Just rule ->
              [ (implementation, Just (captureCount rule), evaluateRule rule)
              | implementation <- maybeToList
                  (rewriteRuleImplementation rule)
              ]
            Nothing -> case declaredImplementations function of
              []
                | mayResolveSyntaxFunctionBody function -> [(function, Nothing, evaluateHere)]
                | otherwise -> []
              implementations ->
                [ (implementation, Just (captureCount rule), evaluateRule rule)
                | rule <- implementations
                , implementation <- maybeToList
                    (rewriteRuleImplementation rule)
                ]
          value <- maybeToList (evaluate expressionValue)
          syntaxFunction <- maybeToList (interpretedFunction value)
          body <- maybeToList (functionBody syntaxFunction)
          case body of
            EvaluatedSyntaxFunctionBody _ expansion -> [(expansion, expected)]
            _ -> []
        choose [] successes =
          case nub successes of
            [expanded] -> Right expanded
            [] -> Right application
            _ -> Right application
        choose ((adapter, expected) : remaining) successes =
          case adapter (captures expected) of
            Just expanded -> choose remaining (expanded : successes)
            Nothing -> choose remaining successes
    _ -> Right application
  where
    evaluateHere = rewriteEvaluate environment (rewriteDeclarations environment)
    evaluateRule rule = case rewriteRuleEvaluation rule of
      Just evaluate -> evaluate
      Nothing -> evaluateHere
    declaredImplementations function =
      case directSyntaxFunctionName function of
        Nothing -> []
        Just (requestedModule, name) ->
          [ rule
          | rule <- availableRules requestedModule function
          , rewriteRuleName rule == name
          , name `notElem` rewriteRuleLiteralPrefix rule
          ]
    -- Tentative passes may reach a recursive let use before discovering its
    -- declaration. Leaving that application unchanged defers the decision;
    -- the fixed-point pass retries it after recursive declarations are in
    -- scope. Known aliases are followed without interpreting ordinary callees.
    mayResolveSyntaxFunctionBody = candidate Set.empty
      where
        candidate seen expressionValue = case expressionValue of
          ScopeAccess {} -> True
          InModule {} -> True
          In {} -> True
          FunctionApplication (IdentifierReference (IdentifierString "_it")) _ -> True
          SyntaxBoundary inner -> candidate seen inner
          IdentifierReference (IdentifierString requested)
            | requested `Set.member` seen -> False
            | otherwise -> case declaredValue requested of
                Just declared -> candidate
                  (Set.insert requested seen) declared
                Nothing -> False
          MapSpecification source _ -> candidate seen source
          ReverseMapSpecification _ source -> candidate seen source
          EitherType left right -> both seen left right
          Overload left right -> both seen left right
          ReverseOverload left right -> both seen left right
          SafeOverload left right -> both seen left right
          ReverseSafeOverload left right -> both seen left right
          _ -> False
        both seen left right = candidate seen left || candidate seen right
        declaredValue requested = firstDeclared
          (reverse (rewriteDeclarations environment))
          where
            firstDeclared [] = Nothing
            firstDeclared (entry : remaining) =
              case dependentDeclaration entry of
                Just declaration
                  | requested `elem` bindingNames entry ->
                      Just (dependentDeclarationImplementation declaration)
                _ -> firstDeclared remaining
    captureCount rule = length
      [ ()
      | SyntaxHole _ <- syntaxTemplatePieces
          (syntaxTemplate (rewriteRule rule))
      ]
    availableRules requestedModule function =
      case requestedModule of
        Nothing -> rewriteRules environment
        Just namespace -> map compileRewriteRule (rewriteScopeRules environment
          (rewriteDeclarations environment) (scopeSource namespace function))
    scopeSource _ (ScopeAccess source _) = source
    scopeSource namespace _ =
      IdentifierReference (IdentifierString namespace)

-- Inspect the adapter's AST constructor before rewriting a raw block. A
-- function body already shadows the outer input while its declarations and
-- yield expression are being collected, before the FunctionBody node exists.
blockRewriteEnvironment :: RewriteEnvironment -> RewriteRule -> RewriteEnvironment
blockRewriteEnvironment environment rule =
  case directSyntaxFunctionExpansion environment (Just rule) probe of
    Right FunctionBody {} -> withContextualSyntax ["this"]
      (enterContext Nothing environment)
    _ -> environment
  where
    probe = FunctionApplication
      (IdentifierReference (IdentifierString (rewriteRuleName rule)))
      (AtlasMap [AtlasMap [], AtlasMap []])

isDirectControlExpansion :: Expression -> Bool
isDirectControlExpansion expanded = case expanded of
  In {} -> True
  Begin {} -> True
  FunctionBody {} -> True
  ScopeAccess {} -> True
  _ -> False

isDirectBlockExpansion :: Expression -> Bool
isDirectBlockExpansion In {} = True
isDirectBlockExpansion Begin {} = True
isDirectBlockExpansion _ = False

rewriteDirectControlExpansion
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteDirectControlExpansion capture environment expanded
  | isDirectControlExpansion expanded = do
      planned <- rewriteStandalone capture
        (environment { rewriteStrictCaptures = False }) expanded
      rewriteStandalone capture environment planned
  | otherwise = Right expanded

-- A contextual selector is itself a callable expression. Its depth argument
-- belongs to the selector, not to the syntax function it returns.
syntaxApplicationSpine :: Expression -> (Expression, [Expression])
syntaxApplicationSpine (FunctionApplication function argument)
  | FunctionApplication (IdentifierReference (IdentifierString name)) _ <- function
  , name == "_it" || name == "_this" = (function, [argument])
syntaxApplicationSpine value = applicationSpine value

directSyntaxArguments :: Expression -> [Expression]
directSyntaxArguments argument = case argument of
  AtlasMap members -> members
  ArgumentMap members -> members
  MapSequence members -> members
  SyntaxBoundary inner -> directSyntaxArguments inner
  _ -> [argument]

directSyntaxFunctionName
  :: Expression
  -> Maybe (Maybe String, String)
directSyntaxFunctionName function = case function of
  IdentifierReference (IdentifierString name) -> Just (Nothing, name)
  ScopeAccess
      (IdentifierReference (IdentifierString namespace))
      (IdentifierReference (IdentifierString name)) ->
        Just (Just namespace, name)
  InModule namespace (IdentifierReference (IdentifierString name)) ->
    Just (Just namespace, name)
  _ -> Nothing

rewriteScopeAccess
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteScopeAccess capture environment source body = do
  rewrittenSource <- rewriteStandalone capture environment source
  let scopedRules = rewriteScopeRules environment
        (rewriteDeclarations environment) rewrittenSource
      nested = environment
        { rewriteRules = nubBy (\left right -> rewriteRule left == rewriteRule right)
            (rewriteRules environment <> map compileRewriteRule scopedRules) }
  -- A short access names a member; it is not an invocation of a zero-hole
  -- syntax rule with the same spelling. Arbitrary RHS expressions are
  -- rewritten once with the source module's exported syntax in scope.
  rewrittenBody <- case body of
    IdentifierReference {} -> pure body
    _ | startsWithBlockDelimiter nested body -> do
          rewritten <- resolveImplicitBlock
            capture nested [] (scopeBodyEntries body)
          pure (singleScopedExpression rewritten)
      | otherwise -> rewriteStandalone capture nested body
  pure (ScopeAccess rewrittenSource rewrittenBody)

singleScopedExpression :: Expression -> Expression
singleScopedExpression (Begin [entry] (AtlasMap [])) = entry
singleScopedExpression expressionValue = expressionValue

scopeBodyEntries :: Expression -> [Expression]
scopeBodyEntries (SyntaxBoundary body) = scopeBodyEntries body
scopeBodyEntries (AtlasMap entries) = entries
scopeBodyEntries body = [body]

startsWithBlockDelimiter :: RewriteEnvironment -> Expression -> Bool
startsWithBlockDelimiter environment body = any startsWithDelimiter
  (scopeBodyEntries body)
  where
    delimiters =
      [ delimiter
      | rule <- rewriteRules environment
      , Just (_, delimiter) <- [rewriteRuleBlockShape rule]
      ]
    startsWithDelimiter entry = case applicationPhrase entry of
      IdentifierReference (IdentifierString name) : _ -> name `elem` delimiters
      _ -> False

-- A neutral application spine does not know where one declared application
-- ends and its enclosing application resumes. Rewrite a literal-headed suffix
-- first when it is itself a complete syntax expression. The enclosing pass
-- can then flatten that rewritten value contextually and match its own rule.
-- This is what makes a composed range application depend on the declared
-- @from@ rule rather than on a parser-level range grammar.
rewriteEmbeddedApplication
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure (Maybe Expression)
rewriteEmbeddedApplication capture environment value =
  firstChanged candidatePositions
  where
    phrase = applicationPhrase value
    candidatePositions =
      [ position
      | position <- [1 .. length phrase - 1]
      , literalHeadAt position
      ]
    literalHeadAt position = case drop position phrase of
      IdentifierReference (IdentifierString literal) : _ ->
        any ((== [literal]) . take 1 . rewriteRuleLiteralPrefix)
          (rewriteRules environment)
      _ -> False
    firstChanged [] = Right Nothing
    firstChanged (position : remaining) = do
      let (prefix, suffix) = splitAt position phrase
          candidate = applicationFrom suffix
      rewritten <- rewriteStandalone capture environment candidate
      if rewritten == candidate
        then firstChanged remaining
        else Right (Just (applicationFrom (prefix <> [rewritten])))

dependentBinderDeclaration :: Expression -> Maybe Expression
dependentBinderDeclaration _ = Nothing

validArgumentMember :: Expression -> Bool
validArgumentMember _ = True

containsBlockStart :: RewriteEnvironment -> Expression -> Bool
containsBlockStart environment value = any containsStart
  (value : concatMap descendants (expressionChildren value))
  where
    -- Parentheses are an explicit syntax boundary. A block nested inside them
    -- is the enclosed operand, not a continuation of the surrounding spine.
    descendants boundary@SyntaxBoundary {} = [boundary]
    descendants child = child : concatMap descendants (expressionChildren child)
    containsStart expressionValue = any (starts expressionValue)
      (rewriteRules environment)
    starts expressionValue rule = case rewriteRuleBlockShape rule of
      Just (prefix, _) -> not (null
        (matchingStarts prefix (applicationPhrase expressionValue)))
      Nothing -> False

startsBlockAtHead :: RewriteEnvironment -> Expression -> Bool
startsBlockAtHead environment expressionValue = any starts
  (rewriteRules environment)
  where
    starts rule = case rewriteRuleBlockShape rule of
      Just (prefix, _) -> 0 `elem`
        matchingStarts prefix (applicationPhrase expressionValue)
      Nothing -> False

matchOrdinarySyntaxWithTail
  :: Bool
  -> CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
matchOrdinarySyntaxWithTail includeConcatenation
    capture environment value trailing =
  firstRule [] (rewriteRules environment)
  where
    facts = expressionFacts value
    captureInScope previous kind captured =
      capture (rewriteStrictCaptures environment)
        (rewriteDeclarations environment) previous kind captured
    firstRule _ [] = Right (value, trailing)
    firstRule earlier (rule : remaining)
      | not (ruleLiteralsPresent rule facts) =
          firstRule (rule : earlier) remaining
      | otherwise =
          firstCandidate rule
            ( literalBoundaryCandidates rule
                <> syntaxProjectionCandidates
                  (includeConcatenation || not (earlierPrefixPending earlier))
                  (syntaxTemplate (rewriteRule rule)) value
            ) >>= \case
            Just rewritten -> Right (rewritten, trailing)
            Nothing -> firstRule (rule : earlier) remaining
    firstCandidate _ [] = Right Nothing
    firstCandidate rule (candidate : remaining) =
      case matchSyntaxRulesWith captureInScope
          [rewriteRule rule] candidate of
        Right rewritten ->
          Just <$> directSyntaxFunctionExpansion
            environment (Just rule) rewritten
        Left NoMatchingSyntaxTemplate -> firstCandidate rule remaining
    earlierPrefixPending = any (\earlierRule ->
      not (null (rewriteRuleLiteralPrefix earlierRule))
        && ruleLiteralsPresent earlierRule facts)
    literalBoundaryCandidates rule = case rewriteRuleLiteralPrefix rule of
      first : _
        | rewriteRuleBlockShape rule == Nothing
        , any isHole (syntaxTemplatePieces
            (syntaxTemplate (rewriteRule rule)))
        , literalOccurrences first value > 1 ->
            maybeToList (literalBoundaryCandidate
              (syntaxTemplate (rewriteRule rule)) value)
      _ -> []
    isHole SyntaxHole {} = True
    isHole _ = False
    literalOccurrences :: String -> Expression -> Int
    literalOccurrences selected expressionValue =
      (case expressionValue of
        IdentifierReference (IdentifierString name)
          | name == selected -> 1
        _ -> 0)
        + sum (map (literalOccurrences selected)
          (expressionChildren expressionValue))

newtype ExpressionFacts = ExpressionFacts
  { expressionRenderings :: Set.Set String
  }

expressionFacts :: Expression -> ExpressionFacts
expressionFacts = ExpressionFacts . collect
  where
    collect expressionValue = Set.unions
      (surface expressionValue
        : postfixConcatenation expressionValue
        : map collect (expressionChildren expressionValue))
    surface expressionValue = Set.fromList
      (renderSourceExpression expressionValue : identifierName expressionValue)
    identifierName (IdentifierReference (IdentifierString name)) = [name]
    identifierName _ = []
    postfixConcatenation (MapConcatenation left _) = Set.singleton
      (renderSourceExpression (MapConcatenation left (AtlasMap [])))
    postfixConcatenation _ = Set.empty

ruleLiteralsPresent :: RewriteRule -> ExpressionFacts -> Bool
ruleLiteralsPresent rule facts =
  rewriteRuleLiterals rule `Set.isSubsetOf` expressionRenderings facts

-- A semicolon-separated operand reaches this pass as consecutive implicit
-- block entries.  For a declared form whose final capture is a function body,
-- collect those entries until one of the ordinary block rules produces that
-- body, then present the collected sequence to the rule as one map value.
-- Neither the surface form nor the block constructor is named here.
matchSequenceFunctionBody
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Maybe (Expression, [Expression]))
matchSequenceFunctionBody _ environment value _
  | containsBlockStart environment value = Right Nothing
matchSequenceFunctionBody capture environment value trailing =
  firstSuccessful
    [ attempt rule prefix
    | rule <- rewriteRules environment
    , Just prefix <- [rewriteRuleSequenceFunctionBodyShape rule]
    ]
  where
    firstSuccessful [] = Right Nothing
    firstSuccessful (candidate : remaining) = do
      matched <- candidate
      case matched of
        Just result -> Right (Just result)
        Nothing -> firstSuccessful remaining

    attempt rule prefix = case applicationPhrase value of
      phrase
        | and (zipWith matchesLiteral prefix phrase)
        , length prefix <= length phrase ->
            findBody rule prefix []
              (applicationFromMaybe (drop (length prefix) phrase)) trailing
      _ -> Right Nothing

    findBody _ _ _ Nothing [] = Right Nothing
    findBody rule prefix operands Nothing (next : remaining) =
      findBody rule prefix operands (Just next) remaining
    findBody rule prefix operands (Just current) remaining =
      matchEmbeddedBlockWith capture environment current remaining
        >>= \case
        Just (rewritten, afterBody)
          | Just (beforeBody, body) <- trailingFunctionBodyValue rewritten ->
              matchCollected rule prefix
                (operands <> maybe [] pure beforeBody) body afterBody
        _ -> case remaining of
          [] -> Right Nothing
          next : rest ->
            findBody rule prefix (operands <> [current]) (Just next) rest

    matchCollected rule prefix operands body remaining =
      case matchSyntaxRulesWith captureInScope
          [rewriteRule rule] candidate of
        Right expanded -> Right (Just (expanded, remaining))
        Left NoMatchingSyntaxTemplate -> Right Nothing
      where
        candidate = applicationFrom
          (map literalExpression prefix <> [AtlasMap operands, body])
        captureInScope previous kind captured =
          capture (rewriteStrictCaptures environment)
            (rewriteDeclarations environment) previous kind captured

    trailingFunctionBodyValue expressionValue =
      case applicationSpine expressionValue of
        (_, []) | body@FunctionBody {} <- expressionValue ->
          Just (Nothing, body)
        (function, arguments)
          | not (null arguments)
          , body@FunctionBody {} <- last arguments ->
              Just
                ( Just (applicationFrom (function : init arguments))
                , body
                )
        _ -> Nothing

matchEmbeddedBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Maybe (Expression, [Expression]))
matchEmbeddedBlock = matchEmbeddedBlockWith

matchEmbeddedBlockWith
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Maybe (Expression, [Expression]))
matchEmbeddedBlockWith capture environment =
  matchWithResult id
  where
    matchWithResult wrapResult value trailing = do
      let facts = expressionFacts value
      direct <- firstSuccessful
        [ attempt wrapResult value trailing rule start
        | rule <- rewriteRules environment
        , Just (prefix, _) <- [rewriteRuleBlockShape rule]
        , start <- matchingStarts prefix (applicationPhrase value)
        , not (ordinarySyntaxPrecedesBlock value facts start prefix)
        ]
      case direct of
        Just result -> Right (Just result)
        Nothing -> case value of
          FunctionTypeExpression generics domain codomain ->
            matchWithResult wrapResult codomain trailing >>= \case
              Just (FunctionApplication rewrittenCodomain body@FunctionBody {}, remaining) ->
                Right (Just
                  ( FunctionApplication
                      (FunctionTypeExpression generics domain rewrittenCodomain)
                      body
                  , remaining
                  ))
              Just (rewritten, remaining) -> Right (Just
                (FunctionTypeExpression generics domain rewritten, remaining))
              Nothing -> Right Nothing
          MapSpecification (SyntaxBoundary source) target ->
            matchWithResult id source trailing >>= \case
              Just (rewritten, remaining) -> Right (Just
                (wrapResult (MapSpecification rewritten target), remaining))
              Nothing -> Right Nothing
          ReverseMapSpecification target (SyntaxBoundary source) ->
            matchWithResult id source trailing >>= \case
              Just (rewritten, remaining) -> Right (Just
                (wrapResult
                  (ReverseMapSpecification target rewritten), remaining))
              Nothing -> Right Nothing
          _ -> case leftInfixContext value of
            Just (left, rebuildResult) ->
              matchWithResult
                (wrapResult . rebuildResult) left trailing
            Nothing -> Right Nothing

    -- An inline ordinary form owns a shared delimiter before that delimiter
    -- can begin an embedded block. This keeps an inline application ending
    -- in @do expression@ from consuming the following line as a
    -- @do ... yield@ body while leaving genuine block starts unchanged.
    ordinarySyntaxPrecedesBlock expressionValue facts blockStart blockPrefix =
      any precedes (rewriteRules environment)
      where
        precedes rule
          | Just _ <- rewriteRuleBlockShape rule = False
          | not (ruleLiteralsPresent rule facts) = False
          | not (all (`Set.member` rewriteRuleLiterals rule) blockPrefix) = False
          | otherwise = any (< blockStart)
              (matchingStarts
                (rewriteRuleLiteralPrefix rule)
                (applicationPhrase expressionValue))

    firstSuccessful [] = Right Nothing
    firstSuccessful (candidate : rest) = do
      matched <- candidate
      case matched of
        Just result -> Right (Just result)
        Nothing -> firstSuccessful rest

    attempt wrapResult value trailing rule start =
      case rewriteRuleBlockShape rule of
        Nothing -> Right Nothing
        Just (prefix, delimiter) -> do
          let phrase = applicationPhrase value
              afterPrefix = drop (start + length prefix) phrase
              before = take start phrase
              blockScope = blockRewriteEnvironment environment rule
              blockCapture = contextCapture (rewriteContext blockScope)
          consumeBlock blockCapture blockScope delimiter afterPrefix trailing
            >>= \case
            Nothing -> adjacentScopedExpression afterPrefix trailing >>= \case
              Nothing -> Right Nothing
              Just (scoped, afterScoped) -> do
                let candidate = applicationFrom
                      (map literalExpression prefix
                        <> [ AtlasMap []
                           , literalExpression delimiter
                           , wrapResult scoped
                           ])
                    captureInScope previous kind captured =
                      capture (rewriteStrictCaptures environment)
                        (rewriteDeclarations environment)
                        previous kind captured
                    match = matchSyntaxRulesWith captureInScope
                      [rewriteRule rule]
                case match candidate of
                  Left NoMatchingSyntaxTemplate -> Right Nothing
                  Right expanded -> do
                    direct <- directSyntaxFunctionExpansion
                      environment (Just rule) expanded
                    Right (Just
                      ( attachAdjacentBody before direct
                      , afterScoped
                      ))
            Just (block, nested, rawResult, afterBlock) -> do
              (result, remaining) <-
                rewriteWithTail True blockCapture nested
                  (wrapResult rawResult) afterBlock
              let candidate selectedResult = applicationFrom
                    (map literalExpression prefix
                      <> [ AtlasMap block
                         , literalExpression delimiter
                         , selectedResult
                         ])
                  captureInScope previous kind captured =
                    blockCapture (rewriteStrictCaptures nested)
                      (rewriteDeclarations nested) previous kind captured
                  match = matchSyntaxRulesWith captureInScope
                    [rewriteRule rule]
              case match (candidate result) of
                Left NoMatchingSyntaxTemplate ->
                  case match (candidate (wrapResult rawResult)) of
                    Left NoMatchingSyntaxTemplate -> Right Nothing
                    Right expanded -> do
                      direct <- directSyntaxFunctionExpansion
                        nested (Just rule) expanded
                      (rewritten, fallbackRemaining) <-
                        rewriteWithTail True blockCapture nested direct afterBlock
                      Right (Just
                        ( attachAdjacentBody before rewritten
                        , fallbackRemaining
                        ))
                Right expanded -> do
                  direct <- directSyntaxFunctionExpansion
                    nested (Just rule) expanded
                  Right (Just
                    (attachAdjacentBody before direct, remaining))

    adjacentScopedExpression afterPrefix trailing = case afterPrefix of
      [candidateScope] -> do
        rewritten <- rewriteStandalone capture environment candidateScope
        pure ((, trailing) <$> scopedProgram rewritten)
      [] -> case trailing of
        candidateScope : remaining -> do
          (rewritten, afterScoped) <- rewriteWithTail False
            capture environment candidateScope remaining
          pure ((, afterScoped) <$> scopedProgram rewritten)
        [] -> pure Nothing
      _ -> pure Nothing

    scopedProgram (SyntaxBoundary inner) = scopedProgram inner
    scopedProgram scoped@(ScopeAccess _ (Begin _ _)) = Just scoped
    scopedProgram _ = Nothing

    attachAdjacentBody before expanded =
      applicationFrom (before <> [expanded])

-- Newline separation is provisional when the current line ends at an
-- internal literal of a visible syntax template. Such a literal has syntax on
-- both sides (for example @or@ or @then@), so the expression cannot yet be
-- complete. Join the next parsed line at the open right edge and rebuild its
-- operator context exactly as the neutral reader would have done without the
-- newline. Leading literals remain complete ordinary identifiers here; block
-- heads such as @do@ are handled by 'consumeBlock'.
continueIncompleteExpression
  :: RewriteEnvironment
  -> Expression
  -> [Expression]
  -> (Expression, [Expression])
continueIncompleteExpression environment = go
  where
    rules = rewriteRules environment
    blockLiterals = nub
      [ literal
      | rule <- rules
      , Just (prefix, delimiter) <- [rewriteRuleBlockShape rule]
      , literal <- prefix <> [delimiter]
      ]
    go current (next : remaining)
      | Just literal <- trailingIdentifier current
      , any (continues current literal) rules =
          go (continueLineExpression current next) remaining
    go current remaining = (current, remaining)

    continues current trailing rule = any applies
      [ (literal, previous)
      | (literal, previous) <- rewriteRuleContinuations rule
      , literal `notElem` blockLiterals
      ]
      where
        identifiers = expressionIdentifiers current
        applies (literal, previous) =
          literal == trailing && case previous of
            [] -> current /= literalExpression literal
            _ -> all (`elem` identifiers) previous

    expressionIdentifiers expressionValue = case expressionValue of
      IdentifierReference (IdentifierString name) -> name : nested
      _ -> nested
      where
        nested = concatMap expressionIdentifiers
          (expressionChildren expressionValue)

trailingIdentifier :: Expression -> Maybe String
trailingIdentifier value = case value of
  IdentifierReference (IdentifierString name) -> Just name
  SyntaxBoundary _ -> Nothing
  -- A qualified member is a complete operand. Its final component may share
  -- a spelling with a declared infix form (notably @'datra.in_body@), but that does
  -- not leave the surrounding source line awaiting a right operand.
  ScopeAccess _ _ -> Nothing
  _ -> case reverse (expressionChildren value) of
    rightmost : _ -> trailingIdentifier rightmost
    [] -> Nothing

continueLineExpression :: Expression -> Expression -> Expression
continueLineExpression left right =
  case leftInfixContext right of
    Just (leading, rebuild) ->
      rebuild (continueLineExpression left leading)
    Nothing -> appendAtRightEdge left right

appendAtRightEdge :: Expression -> Expression -> Expression
appendAtRightEdge left right =
  case rightInfixContext left of
    Just (edge, rebuild) -> rebuild (appendAtRightEdge edge right)
    Nothing -> applicationFrom
      (applicationPhrase left <> applicationPhrase right)

blockShapeFromPieces
  :: [SyntaxPiece Expression]
  -> Maybe ([String], String)
blockShapeFromPieces pieces =
  case break isBlockHole
      pieces of
    (prefix, SyntaxHole BlockSyntaxHole {}
        : SyntaxLiteral delimiter
        : [SyntaxHole ExpressionSyntaxHole {}]) ->
      (, delimiter) <$> traverse literal prefix
    _ -> Nothing
  where
    isBlockHole (SyntaxHole BlockSyntaxHole {}) = True
    isBlockHole _ = False
    literal (SyntaxLiteral text) = Just text
    literal _ = Nothing

sequenceFunctionBodyShapeFromPieces
  :: [SyntaxPiece Expression]
  -> Maybe [String]
sequenceFunctionBodyShapeFromPieces pieces =
  case reverse pieces of
    SyntaxHole FunctionBodySyntaxHole {}
        : SyntaxHole {}
        : reversedPrefix ->
      traverse literal (reverse reversedPrefix)
    _ -> Nothing
  where
    literal (SyntaxLiteral text) = Just text
    literal _ = Nothing

continuationContexts :: [SyntaxPiece Expression] -> [(String, [String])]
continuationContexts pieces =
  [ (literal, [previous | SyntaxLiteral previous <- before])
  | (before, SyntaxLiteral literal : after) <- pieceContexts pieces
  , not (null before)
  , not (null after)
  ]
  where
    pieceContexts [] = []
    pieceContexts (piece : remaining) =
      ([], piece : remaining) :
        [ (piece : before, suffix)
        | (before, suffix) <- pieceContexts remaining
        ]

matchingStarts :: [String] -> [Expression] -> [Int]
matchingStarts prefix values =
  [ position
  | position <- [0 .. length values - length prefix]
  , and (zipWith matchesLiteral prefix (drop position values))
  ]

consumeBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> String
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure
      (Maybe ([Expression], RewriteEnvironment, Expression, [Expression]))
consumeBlock capture initial = go [] initial
  where
    go reversed environment delimiter current trailing =
      case splitAtDelimiter delimiter current of
        Just (beforeDelimiter, resultTokens)
          | not (null resultTokens) -> do
              let result = applicationFrom resultTokens
              case applicationFromMaybe beforeDelimiter of
                Just unfinished
                  | containsBlockStart environment unfinished -> do
                      let continuation =
                            applicationFrom
                              (literalExpression delimiter : resultTokens)
                              : trailing
                          tentative = environment
                            { rewriteStrictCaptures = False }
                      (rewritten, remaining) <- rewriteWithTail False
                        capture tentative unfinished continuation
                      if length remaining < length continuation
                        then go (rewritten : reversed)
                          (advanceScope tentative rewritten)
                          delimiter [] remaining
                        else complete beforeDelimiter result
                _ -> complete beforeDelimiter result
              where
                complete before result = do
                  let prefix = maybe [] (: [])
                        (applicationFromMaybe before)
                      collected = reverse reversed <> prefix
                  (rewrittenBlock, finalNested) <-
                    rewriteSequence capture initial collected
                  Right (Just
                    ( rewrittenBlock
                    , finalNested
                    , result
                    , trailing
                    ))
        _ -> case applicationFromMaybe current of
          Just entry -> do
            let tentative = environment { rewriteStrictCaptures = False }
            (rewritten, remaining) <-
              rewriteWithTail False capture tentative entry trailing
            let consumedCount = length trailing - length remaining
                consumed = entry : take consumedCount trailing
                nested = advanceScope tentative rewritten
            go (reverse consumed <> reversed) nested delimiter [] remaining
          Nothing -> case trailing of
            [] -> Right Nothing
            entry : remaining ->
              go reversed environment delimiter
                (applicationPhrase entry) remaining

splitAtDelimiter
  :: String
  -> [Expression]
  -> Maybe ([Expression], [Expression])
splitAtDelimiter literal = go []
  where
    go _ [] = Nothing
    go reversed (value : remaining) =
      case splitAtLiteral literal value of
        Just (before, suffix) -> Just
          (reverse reversed <> maybe [] (: []) before, suffix <> remaining)
        Nothing -> go (value : reversed) remaining

-- The neutral reader may place a template delimiter inside the right edge of
-- the AST immediately before it. For example, @a : 5 yield a + 1@ initially
-- has @yield@ inside the annotation of @a@. Split that source-order boundary
-- structurally: retain the declaration before the delimiter and rebuild the
-- provisional operator context around the expression after it.
splitAtLiteral
  :: String
  -> Expression
  -> Maybe (Maybe Expression, [Expression])
splitAtLiteral literal value =
  directApplicationSplit literal value
    <|> splitInfix
    <|> splitDeclaration
    <|> splitOptional
    <|> splitLet
  where
    splitInfix = do
      (left, rebuildRight) <- leftInfixContext value
      case splitAtLiteral literal left of
        Just (before, suffix) -> Just
          (before, [rebuildRight (applicationFrom suffix)])
        Nothing -> do
          (right, rebuildLeft) <- rightInfixContext value
          (before, suffix) <- splitAtLiteral literal right
          pure
            ( rebuildLeft <$> before
            , suffix
            )

    splitDeclaration = case value of
      IdentifierOperation name annotation given ->
        splitIdentifierOperation IdentifierOperation name annotation given
      IdentifierTemplateOperation parts annotation given ->
        splitIdentifierOperation IdentifierTemplateOperation
          parts annotation given
      _ -> Nothing

    splitIdentifierOperation constructor name annotation given =
      case given >>= splitAtLiteral literal of
        Just (before, suffix) ->
          let rewrittenAnnotation = case given of
                Just original
                  | original == annotation ->
                      maybe annotation id before
                _ -> annotation
          in Just
            ( Just (constructor name rewrittenAnnotation before)
            , suffix
            )
        Nothing -> do
          (before, suffix) <- splitAtLiteral literal annotation
          pure
            ( (\beforeAnnotation ->
                constructor name beforeAnnotation given) <$> before
            , suffix
            )

    splitOptional = case value of
      OptionalType inner -> do
        (before, suffix) <- splitAtLiteral literal inner
        pure (OptionalType <$> before, suffix)
      _ -> Nothing

    splitLet = case value of
      Let inner -> do
        (before, suffix) <- splitAtLiteral literal inner
        pure (Let <$> before, suffix)
      _ -> Nothing

literalBoundaryCandidate
  :: SyntaxTemplate Expression
  -> Expression
  -> Maybe Expression
literalBoundaryCandidate (SyntaxTemplate pieces) value =
  case pieces of
    SyntaxLiteral first : remaining -> do
      (Nothing, suffix) <- splitAtLiteral first value
      continue [literalExpression first] remaining (applicationFrom suffix)
    _ -> Nothing
  where
    continue built [] _ = Just (applicationFrom built)
    continue built [SyntaxHole _] current =
      Just (applicationFrom (built <> [current]))
    continue built
        (SyntaxHole _ : SyntaxLiteral delimiter : remaining) current = do
      (Just captured, suffix) <- splitAtLiteral delimiter current
      continue
        (built <> [captured, literalExpression delimiter])
        remaining
        (applicationFrom suffix)
    continue built (SyntaxLiteral literal : remaining) current = do
      (Nothing, suffix) <- splitAtLiteral literal current
      continue (built <> [literalExpression literal]) remaining
        (applicationFrom suffix)
    continue _ _ _ = Nothing

advanceScope :: RewriteEnvironment -> Expression -> RewriteEnvironment
advanceScope environment entry = environment
  { rewriteRules = retained <> introduced
  , rewriteDeclarations = retainedDeclarations <> [entry]
  }
  where
    names = bindingNames entry
    retained = filter ((`notElem` names) . rewriteRuleName)
      (rewriteRules environment)
    introduced = compileScopedRewriteRules environment retainedDeclarations
      (declarationRules (resolveDependentDeclarationHead environment entry))
    retainedDeclarations = filter
      (null . filter (`elem` names) . bindingNames)
      (rewriteDeclarations environment)

compileScopedRewriteRules
  :: RewriteEnvironment
  -> [Expression]
  -> [SyntaxRule]
  -> [RewriteRule]
compileScopedRewriteRules environment declarations rules = map compile rules
  where
    evaluate = rewriteEvaluate environment declarations
    kinds = nub
      [ kind
      | rule <- rules
      , SyntaxHole kind <- syntaxTemplatePieces (syntaxTemplate rule)
      ]
    classifications = zip kinds
      (rewriteClassifyHoles environment declarations kinds)
    classify kind = case lookup kind classifications of
      Just classified -> classified
      Nothing -> (kind, Nothing)
    compile rule = compiled
      { rewriteRuleEvaluation = Just evaluate
      , rewriteRuleHoleFamilies = holeFamilies
      }
      where
        specializedRule = rule
          { syntaxTemplate = SyntaxTemplate specializedPieces }
        (specializedPieces, holeFamilies) = foldr classifyPiece ([], [])
          (syntaxTemplatePieces (syntaxTemplate rule))
        compiled = compileRewriteRule specializedRule
        classifyPiece piece (pieces, families) = case piece of
          SyntaxLiteral literal ->
            (SyntaxLiteral literal : pieces, families)
          SyntaxHole kind ->
            let (specialized, family) = classify kind
            in (SyntaxHole specialized : pieces, family : families)

-- Resolve the explicitly parenthesized declaration head against declarations
-- visible at this block position. Bare identifiers never take this path, so
-- @abc := value@ continues to declare the literal name @abc@.
resolveDependentDeclarationHead
  :: RewriteEnvironment
  -> Expression
  -> Expression
resolveDependentDeclarationHead environment expressionValue =
  case expressionValue of
    Let value -> Let (resolveDependentDeclarationHead environment value)
    Val value -> Val (resolveDependentDeclarationHead environment value)
    In contextual value -> In contextual
      (resolveDependentDeclarationHead environment value)
    IdentifierTemplateOperation
        [StringTemplateInterpolation headExpression]
        annotation
        given ->
      case resolvedParts headExpression of
        Just parts -> IdentifierTemplateOperation parts annotation given
        Nothing -> expressionValue
    _ -> expressionValue
  where
    resolvedParts (SyntaxBoundary inner) = resolvedParts inner
    resolvedParts (GreedyStringTemplate operand) = Just
      [ StringTemplateInterpolation
          (SyntaxBoundary (GreedyStringTemplate (resolveGreedy operand)))
      ]
    resolvedParts (StringTemplate parts) = Just parts
    resolvedParts (AsciiStringLiteral literal) =
      Just [StringTemplateLiteral literal]
    resolvedParts (IdentifierReference (IdentifierString name)) = do
      declaration <- firstDeclaration name
        (reverse (rewriteDeclarations environment))
      resolvedParts (dependentDeclarationImplementation declaration)
    resolvedParts _ = Nothing

    resolveGreedy greedyPart = case greedyPart of
      SyntaxBoundary inner -> SyntaxBoundary (resolveGreedy inner)
      AtlasMap members -> AtlasMap (map resolveGreedy members)
      MapSequence members -> MapSequence (map resolveGreedy members)
      EitherType left right ->
        EitherType (resolveGreedy left) (resolveGreedy right)
      OptionalType operand -> OptionalType (resolveGreedy operand)
      reference@(IdentifierReference (IdentifierString name)) ->
        if any (elem name . bindingNames) (rewriteDeclarations environment)
          then reference
          else AsciiStringLiteral name
      atom -> atom

    firstDeclaration _ [] = Nothing
    firstDeclaration requested (candidate : remaining) =
      case dependentDeclaration candidate of
        Just declaration
          | requested `elem` bindingNames candidate ->
              Just declaration
        _ -> firstDeclaration requested remaining
