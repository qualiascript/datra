{-# LANGUAGE LambdaCase #-}
-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Source layout has disappeared at this boundary: application spines are
-- matched directly, while an 'AtlasMap' supplies the contextual boundary for
-- block captures.
module SyntaxRewriting
  ( SyntaxContext (..)
  , SyntaxRewriteFailure (..)
  , rewriteStandaloneSyntax
  , rewriteResourceSyntax
  , rewriteResourceSyntaxLocated
  ) where
import Control.Applicative ((<|>))
import Control.Monad.Trans.State.Strict (State, runState, state)
import DatraLanguage.DependentDeclaration
  ( bindingNames
  , dependentDeclaration
  , invalidDependentDeclarationModifiers
  , dependentDeclarationNameFamilyExpression
  , dependentDeclarationNameExpression
  )
import Data.List (nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe, maybeToList)
import Data.Set qualified as Set
import DatraLanguage.AST
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Diagnostics.Application
  ( SyntaxRewriteFailure (..)
  , SyntaxTemplateAdmissibilityFailure (..)
  )
import DatraLanguage.Diagnostics
  ( Located (..)
  , SourceSpan
  )
import Parsing (ResourceEnvelope (..))
import DatraTypes
  ( EvaluatedFunction (functionBody, functionCodomain)
  , EvaluatedFunctionBody
      ( EvaluatedSyntaxFunctionBody )
  , SyntaxFunctionExpansion (..)
  , SyntaxFunctionInsertion (..)
  , InterpretedValue
  , booleanCondition
  , eitherValue
  , interpretedFunction
  , interpretedFunctionBody
  , interpretedRuntimeFunctionInsertion
  , interpretedSemanticResult
  , makeArgumentativeMapPreservingSingleton
  , ordinalIndexedProductFamily
  , simpleIdentifierTypeValue
  , subfederationValues
  )
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , SyntaxTemplateCompilationFailure (..)
  , DependentSyntaxRule (..)
  , DependentSyntaxInvocation (..)
  , declarationRuleFailures
  , declarationRuleBranches
  , expandSyntax
  , syntaxApplicationImplementation
  , syntaxDependentRule
  , syntaxRuleAdapter
  )
import SyntaxTemplateMatching
  ( SyntaxMatch (..) )
import SyntaxTemplateAdmissibility
  ( syntaxTemplatesOverlap )
import SyntaxTemplateProjection
  ( applicationFrom
  , applicationSpine
  , directApplicationSplit
  , leftInfixContext
  , literalExpression
  , rightInfixContext
  , syntaxProjectionCandidates
  )
import SyntaxRewriting.Types
  ( CandidateRejection
  , CandidateTypingContext (..)
  , CaptureHole
  , RewriteEnvironment (..)
  , PreparedExpansion (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , SelectedCandidate (..)
  , StructuralCandidate (..)
  , SyntaxContext (..)
  )
import SyntaxRewriting.Candidates
  ( compileDependentRewriteRule
  , compileRewriteRule
  , enumerateRuleStructuralCandidates
  , structuralCandidateMatch
  )
import SyntaxRewriting.Diagnostics
  ( candidateRejectionAt
  , reportCandidateRejections
  )
import SyntaxRewriting.Stack
  ( RewriteStackOperations (..)
  , runRewriteStack
  )

rewriteRuleName :: RewriteRule -> String
rewriteRuleName = syntaxName . rewriteRule

rewriteRuleImplementation :: RewriteRule -> Maybe Expression
rewriteRuleImplementation = syntaxRuleAdapter . rewriteRule

resolvedRuleReturnType
  :: (Expression -> Maybe InterpretedValue)
  -> SyntaxRule
  -> Maybe InterpretedValue
resolvedRuleReturnType evaluate rule =
  (syntaxRuleAdapter rule >>= evaluate
    >>= interpretedFunction >>= Just . functionCodomain)
  <|> (syntaxRuleAdapter rule >>= functionCodomainExpression >>= evaluate)

functionCodomainExpression :: Expression -> Maybe Expression
functionCodomainExpression expressionValue = case expressionValue of
  FunctionTypeExpression _ _ codomain -> Just codomain
  FunctionApplication function _ -> functionCodomainExpression function
  Fun signature -> functionCodomainExpression signature
  SyntaxBoundary inner -> functionCodomainExpression inner
  MapSpecification source _ -> functionCodomainExpression source
  ReverseMapSpecification _ source -> functionCodomainExpression source
  _ -> Nothing

syntaxFunctionInsertion
  :: (Expression -> Maybe InterpretedValue)
  -> Expression
  -> Maybe SyntaxFunctionInsertion
syntaxFunctionInsertion evaluate implementation = do
  value <- evaluate implementation
  syntaxFunctionInsertionFromValue value

syntaxFunctionInsertionFromValue
  :: InterpretedValue
  -> Maybe SyntaxFunctionInsertion
syntaxFunctionInsertionFromValue value = do
  body <- interpretedFunctionBody value
    <|> (interpretedFunction value >>= functionBody)
  case body of
    EvaluatedSyntaxFunctionBody _ insertion -> Just insertion
    _ -> Nothing

prepareSelectedSyntaxMatch
  :: RewriteEnvironment
  -> RewriteRule
  -> SyntaxMatch
  -> PreparedExpansion
prepareSelectedSyntaxMatch environment rule matched = PreparedExpansion
  { preparedExpansionSyntax = case directExpansion of
      Just value -> value
      Nothing -> directSyntaxFunctionExpansion environment rule fallback
  , preparedExpansionRemaining = syntaxMatchRemaining matched
  }
  where
    selection = syntaxMatchSelection matched
    captures = templateSelectionCaptures selection
    fallback = expandSyntax (syntaxMatchRule matched) selection
    evaluate = case rewriteRuleEvaluation rule of
      Just selected -> selected
      Nothing -> rewriteEvaluate environment
        (rewriteDeclarations environment)
    -- A zero-hole declaration is an exact dependent lookup. Speculatively
    -- evaluating its implementation is unnecessary; only declarations with
    -- captures can provide a syntax-function insertion.
    directExpansion
      | any isHole (syntaxTemplatePieces
          (syntaxTemplate (rewriteRule rule))) = do
          implementation <- rewriteRuleImplementation rule
          insertion <- case rewriteRuleEvaluation rule of
            Just _ -> rewriteRuleSyntaxInsertion rule
            Nothing -> syntaxFunctionInsertion evaluate implementation
          applySyntaxFunction insertion (insertionCaptures rule captures)
      | otherwise = Nothing
    isHole SyntaxHole {} = True
    isHole SyntaxLiteral {} = False

insertionCaptures :: RewriteRule -> [Expression] -> [Expression]
insertionCaptures rule captures
  | Just _ <- syntaxApplicationImplementation (rewriteRule rule) =
      concatMap directSyntaxArguments captures
  | otherwise = captures

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
sameHoleClass DependentArgumentSyntaxHole {}
    DependentArgumentSyntaxHole {} = True
sameHoleClass ValueSyntaxHole {} ValueSyntaxHole {} = True
sameHoleClass _ _ = False

isValueSubfederation :: InterpretedValue -> InterpretedValue -> Bool
isValueSubfederation source target =
  case subfederationValues source target >>= booleanCondition of
    Right accepted -> accepted
    Left _ -> False

rewriteEnvironment
  :: Maybe SourceSpan
  -> SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> RewriteEnvironment
rewriteEnvironment sourceSpan context rules declarations = RewriteEnvironment
  context sourceSpan (map compile rules) declarations
  (contextClassify context) (contextScopeRules context)
  (contextEvaluate context) (contextResultType context)
  (contextEvaluateWithInput context)
  (contextApply context)
  where
    evaluate = contextEvaluate context declarations
    compile = compileRuleWith evaluate

compileRuleWith
  :: (Expression -> Maybe InterpretedValue)
  -> SyntaxRule
  -> RewriteRule
compileRuleWith evaluate rule = (compileRewriteRule rule)
  { rewriteRuleSyntaxInsertion = insertion
  , rewriteRuleReturnType = resolvedRuleReturnType evaluate rule
  }
  where
    insertion = syntaxRuleAdapter rule >>= syntaxFunctionInsertion evaluate

compileRuleIn :: RewriteEnvironment -> SyntaxRule -> RewriteRule
compileRuleIn environment = compileRuleWith
  (rewriteEvaluate environment (rewriteDeclarations environment))

-- | Rewrite one already-delimited expression with the same declaration
-- environment used by resource rewriting.  Canonical values cross this
-- boundary after rendering and parsing, so they must recover dependent
-- declaration invocations before closure collection inspects references.
rewriteStandaloneSyntax
  :: SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandaloneSyntax context rules declarations =
  runRewriteExpression (contextCapture context)
    (rewriteEnvironment Nothing context rules declarations)

rewriteResourceSyntax
  :: ResourceEnvelope
  -> SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntax envelope context rules declarations raw =
  rewriteResourceSyntaxWithSpan Nothing envelope context rules declarations raw

rewriteResourceSyntaxLocated
  :: ResourceEnvelope
  -> SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> Located Expression
  -> Either SyntaxRewriteFailure (Located Expression)
rewriteResourceSyntaxLocated envelope context rules declarations
    (Located sourceSpan raw) =
  Located sourceSpan <$> rewriteResourceSyntaxWithSpan
    (Just sourceSpan) envelope context rules declarations raw

rewriteResourceSyntaxWithSpan
  :: Maybe SourceSpan
  -> ResourceEnvelope
  -> SyntaxContext
  -> [SyntaxRule]
  -> [Expression]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntaxWithSpan sourceSpan envelope context rules declarations raw =
  case (envelope, raw) of
    (ExplicitMapEnvelope, expressionValue) ->
      runRewriteExpression capture initial expressionValue
    (ImplicitBlockEnvelope, AtlasMap entries) -> rewriteImplicitResource entries
    (ImplicitBlockEnvelope, expressionValue) ->
      rewriteImplicitResource [expressionValue]
  where
    capture = contextCapture context
    initial = rewriteEnvironment sourceSpan context rules declarations
    rewriteImplicitResource entries = do
      rewrittenContainer <- runRewriteExpression capture initial
        (AtlasMap entries)
      let rewritten = case rewrittenContainer of
            AtlasMap selected -> selected
            selected -> [selected]
      case reverse rewritten of
        [] -> Right (Begin [] (AtlasMap []))
        result : reversedDeclarations -> do
          blockDeclarations <- lowerBlockDeclarations
            (reverse reversedDeclarations)
          Right (Begin blockDeclarations result)

-- Keep visible syntax rules, while moving the declarations they depend on into
-- the evaluator's parent scope. RHS declarations belong to the new scope.
enterContext :: Maybe Expression -> RewriteEnvironment -> RewriteEnvironment
enterContext value environment = environment
  { rewriteContext = nested
  , rewriteDeclarations = []
  , rewriteClassifyHoles = contextClassify nested
  , rewriteScopeRules = contextScopeRules nested
  , rewriteEvaluate = contextEvaluate nested
  , rewriteResultTypeOf = contextResultType nested
  , rewriteEvaluateWithInput = contextEvaluateWithInput nested
  , rewriteApply = contextApply nested
  }
  where
    nested = contextEnter (rewriteContext environment)
      (rewriteDeclarations environment) value

publishSequenceResult
  :: RewriteEnvironment
  -> RewriteEnvironment
  -> [Expression]
  -> [(Int, RewriteResult)]
  -> Int
  -> RewriteResult
  -> Either SyntaxRewriteFailure (Maybe RewriteEnvironment)
publishSequenceResult initial environment sources earlier position result = do
  let entry = rewriteResultExpression result
      scoped = environment
        { rewriteDeclarations = scopedPublicationDeclarations
            initial sources earlier position }
      resolved = resolveDependentDeclarationHead scoped entry
  case dependentDeclaration resolved of
    Nothing -> Right Nothing
    Just declaration -> do
      let (_, introduced) = advanceScopeResolved scoped entry resolved
          currentNameFamily = declarationNameFamily scoped declaration
          currentFamily = introduced
      mapM_ (validateEarlierDeclaration scoped declaration
          currentNameFamily currentFamily . rewriteResultExpression . snd)
        earlier
      validateDeclarationRuleFailures resolved
      if isValDependentDeclaration resolved
        then mapM_ (validateValDeclaration scoped)
          [ (compiled, dependent)
          | compiled <- currentFamily
          , Just dependent <- [syntaxDependentRule (rewriteRule compiled)]
          , DependentSyntaxLookup {} <-
              [dependentSyntaxInvocation dependent]
          ]
        else Right ()
      Right (Just (advanceScopeCompiled environment entry introduced))

scopedPublicationDeclarations
  :: RewriteEnvironment
  -> [Expression]
  -> [(Int, RewriteResult)]
  -> Int
  -> [Expression]
scopedPublicationDeclarations initial sources earlier position =
  filter (not . shadowsOuter) outer <> local
  where
    outer = rewriteDeclarations initial
    finalized = Map.fromList
      [ (index, rewriteResultExpression result)
      | (index, result) <- earlier
      ]
    local =
      [ selected
      | (index, source) <- zip [0 :: Int ..]
          sources
      , index < position || isLetDeclarationExpression source
      , let selected = maybe source id
              (Map.lookup index finalized)
      ]
    localNames = concatMap bindingNames local
    shadowsOuter declaration = any (`elem` localNames)
      (bindingNames declaration)

declarationLabel :: DependentDeclaration Expression -> String
declarationLabel = renderSourceExpression . dependentDeclarationNameExpression

declarationNameFamily
  :: RewriteEnvironment
  -> DependentDeclaration Expression
  -> Maybe InterpretedValue
declarationNameFamily environment declaration =
  rewriteEvaluate environment
    (rewriteDeclarations environment)
    (dependentDeclarationNameFamilyExpression declaration)

validateEarlierDeclaration
  :: RewriteEnvironment
  -> DependentDeclaration Expression
  -> Maybe InterpretedValue
  -> [RewriteRule]
  -> Expression
  -> Either SyntaxRewriteFailure ()
validateEarlierDeclaration environment current currentNameFamily currentRules
    previousEntry = case dependentDeclaration previousResolved of
  Nothing -> Right ()
  Just previous
    | not (null previousRules)
    , not (null currentRules)
    , and
        [ not (rewriteRulesOverlap previousRule currentRule)
        | previousRule <- previousRules
        , currentRule <- currentRules
        ] -> Right ()
    | Just currentFamily <- currentNameFamily
    , Just previousFamily <- declarationNameFamily environment previous ->
        case eitherValue previousFamily currentFamily of
          Right _ -> Right ()
          Left _ -> overlapFailure previous
    | otherwise -> overlapFailure previous
  where
    previousResolved = resolveDependentDeclarationHead environment previousEntry
    (_, previousRules) = advanceScopeResolved
      environment previousEntry previousResolved
    overlapFailure previous = Left (OverlappingDependentDeclarations
      (declarationLabel previous) (declarationLabel current))

validateDeclarationRuleFailures
  :: Expression
  -> Either SyntaxRewriteFailure ()
validateDeclarationRuleFailures resolved = case declarationRuleFailures resolved of
  InadmissibleSyntaxTemplate rendered SyntaxTemplateProjectionLoss : _ ->
    Left (OverlappingDependentDeclarations rendered rendered)
  InadmissibleSyntaxTemplate rendered failure : _ ->
    Left (InvalidRewriteSyntaxTemplate rendered failure)
  [] -> Right ()

validateValDeclaration
  :: RewriteEnvironment
  -> (RewriteRule, DependentSyntaxRule)
  -> Either SyntaxRewriteFailure ()
validateValDeclaration _ (_, dependent)
  | null (dependentSyntaxCaptures dependent) = Right ()
validateValDeclaration environment pair@(compiled, _) = do
  case sequence (rewriteRuleHoleFamilies compiled) of
    Just families
      | Nothing <- ordinalIndexedProductFamily families ->
          Left (NonInjectiveDependentDeclaration
            (syntaxName (rewriteRule compiled)))
    _ -> Right ()
  validateInjectiveDeclaration environment pair

validateInjectiveDeclaration
  :: RewriteEnvironment
  -> (RewriteRule, DependentSyntaxRule)
  -> Either SyntaxRewriteFailure ()
validateInjectiveDeclaration environment (compiled, dependent)
  | null captures = Right ()
  | Just _ <- syntaxInsertion = Right ()
  | Just _ <- runtimeInsertion = Right ()
  | otherwise = case do
      families <- traverse id (rewriteRuleHoleFamilies compiled)
      inputValue <- either (const Nothing) Just
        (makeArgumentativeMapPreservingSingleton
          (zipWith captureValue captures families))
      outputValue <- rewriteEvaluateWithInput environment
          (rewriteDeclarations environment) inputValue implementation <|>
        rewriteApply environment
          (rewriteDeclarations environment) implementation inputValue
      pure (inputValue, outputValue) of
        Just (inputValue, outputValue)
          | equivalentFederations inputValue outputValue -> Right ()
        _ -> Left (NonInjectiveDependentDeclaration (syntaxName rule))
  where
    rule = rewriteRule compiled
    captures = dependentSyntaxCaptures dependent
    implementation = dependentSyntaxImplementation dependent
    syntaxInsertion = rewriteRuleSyntaxInsertion compiled
    runtimeInsertion = rewriteRuleRuntimeInsertion compiled

captureValue
  :: Maybe (IdentifierString, Expression)
  -> InterpretedValue
  -> InterpretedValue
captureValue (Just (IdentifierString name, _)) value =
  simpleIdentifierTypeValue name value
captureValue Nothing value = value

equivalentFederations :: InterpretedValue -> InterpretedValue -> Bool
equivalentFederations left right =
  interpretedSemanticResult left == interpretedSemanticResult right
    || (isSubfederation left right && isSubfederation right left)
  where
    isSubfederation source target =
      case subfederationValues source target >>= booleanCondition of
        Right accepted -> accepted
        Left _ -> False

isValDependentDeclaration :: Expression -> Bool
isValDependentDeclaration expressionValue = case expressionValue of
  Val value -> maybe False (const True) (dependentDeclaration value)
  Let value -> isValDependentDeclaration value
  Def value -> isValDependentDeclaration value
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
  :: RewriteEnvironment
  -> [Expression]
  -> (RewriteEnvironment, Map.Map Int [RewriteRule])
recursiveRewriteEnvironment initial entries =
  ( recursive
      { rewriteDeclarations = rewriteDeclarations initial
      }
  , compiledLets
  )
  where
    (recursive, compiledLets) = foldl introduceRecursive
      (initial, Map.empty)
      [ (position, declaration)
      | (position, declaration) <- zip [0 :: Int ..] entries
      , isLetDeclarationExpression declaration
      ]
    introduceRecursive (environment, compiled) (position, declaration) =
      (next, Map.insert position introduced compiled)
      where
        scoped = environment
          { rewriteDeclarations =
              scopedBlockDeclarations initial position entries
          }
        resolved = resolveDependentDeclarationHead scoped declaration
        (next, introduced) = advanceScopeResolved scoped declaration resolved

runRewriteExpression
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
runRewriteExpression capture environment value = do
  (result, rejections) <- runStructuralCandidates capture environment value
    (structuralCandidatesFor True environment value)
  case (rewriteResultSelection result, rejections) of
    (Nothing, _ : _) -> Left
      (RejectedSyntaxCandidates (reportCandidateRejections rejections))
    _ -> Right (rewriteResultExpression result)

directSyntaxFunctionExpansion
  :: RewriteEnvironment
  -> RewriteRule
  -> Expression
  -> SyntaxFunctionExpansion
directSyntaxFunctionExpansion environment selectedRule application =
  case syntaxApplicationSpine application of
    (_, [argument]) ->
      choose adapters []
      where
        captures expected = case expected of
          Just 0 -> []
          Just 1 -> [argument]
          _ -> directSyntaxArguments argument
        adapters = do
          implementation <- maybeToList
            (rewriteRuleImplementation selectedRule)
          let expected
                | Just _ <- syntaxApplicationImplementation
                    (rewriteRule selectedRule) = Nothing
                | otherwise = Just (captureCount selectedRule)
              insertion = case rewriteRuleEvaluation selectedRule of
                Just _ -> rewriteRuleSyntaxInsertion selectedRule
                Nothing -> syntaxFunctionInsertion
                  (evaluateRule selectedRule) implementation
          selected <- maybeToList insertion
          pure (applySyntaxFunction selected, expected)
        choose [] successes =
          case nub successes of
            [expanded] -> expanded
            [] -> SyntaxExpression application
            _ -> SyntaxExpression application
        choose ((adapter, expected) : remaining) successes =
          case adapter (captures expected) of
            Just expanded -> choose remaining (expanded : successes)
            Nothing -> choose remaining successes
    _ -> SyntaxExpression application
  where
    evaluateHere = rewriteEvaluate environment (rewriteDeclarations environment)
    evaluateRule rule = case rewriteRuleEvaluation rule of
      Just evaluate -> evaluate
      Nothing -> evaluateHere
    captureCount rule = length
      [ ()
      | SyntaxHole _ <- syntaxTemplatePieces
          (syntaxTemplate (rewriteRule rule))
      ]
-- Inspect the adapter's AST constructor before rewriting a raw block. A
-- function body already shadows the outer input while its declarations and
-- yield expression are being collected, before the FunctionBody node exists.
syntaxApplicationSpine :: Expression -> (Expression, [Expression])
syntaxApplicationSpine value = applicationSpine value

directSyntaxArguments :: Expression -> [Expression]
directSyntaxArguments argument = case argument of
  AtlasMap members -> members
  ArgumentativeMap members -> members
  MapSequence members -> members
  SyntaxBoundary inner -> directSyntaxArguments inner
  _ -> [argument]

containsRuntimeFunctionBody :: Expression -> Bool
containsRuntimeFunctionBody expressionValue = case expressionValue of
  FunctionApplication _ FunctionBody {} -> True
  Fun signature -> containsRuntimeFunctionBody signature
  SyntaxBoundary inner -> containsRuntimeFunctionBody inner
  _ -> False

lowerBlockDeclarations
  :: [Expression]
  -> Either SyntaxRewriteFailure [DependentDeclaration Expression]
lowerBlockDeclarations = traverse lower
  where
    lower expressionValue = maybe
      (case invalidDependentDeclarationModifiers expressionValue of
        Just (written, correct) ->
          Left (InvalidDeclarationModifiers written correct)
        Nothing -> Left (ExpectedDependentDeclaration expressionValue))
      Right
      (dependentDeclaration expressionValue)

runStructuralCandidates
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [StructuralCandidate]
  -> Either SyntaxRewriteFailure (RewriteResult, [CandidateRejection])
runStructuralCandidates capture environment source =
  runRewriteStack operations environment source
  where
    operations = RewriteStackOperations
      { stackEnumerateCandidates = structuralCandidatesFor False
      , stackCaptureHole = captureHole
      , stackExpectedHole = expectedHole
      , stackCandidateReturn = candidateReturn
      , stackTypesCompatible = isValueSubfederation
      , stackAdvanceOrdinary = advanceOrdinary
      , stackSequenceEntries = sequenceEntries
      , stackPublishDeclaration = publishSequenceResult
      , stackMaterializeSequence = materializeSequence
      , stackPrepareCandidate = prepareCandidate
      , stackExpansionWork = expansionWork
      , stackMaterializeExpansion = materializeExpansion
      , stackCandidateRejection = \selectedEnvironment details ->
          candidateRejectionAt
            (rewriteSourceSpan selectedEnvironment) details
      }
    captureHole selectedEnvironment _ previous kind captured =
      case rewriteClassifyHoles selectedEnvironment declarations [kind] of
        [(specialized, Just expected)]
          | Just actual <- rewriteResultTypeOf selectedEnvironment
              declarations captured
          , isValueSubfederation actual expected -> Just captured
          | otherwise -> captureStrict specialized
        [(specialized, _)] -> captureStrict specialized
        _ -> captureStrict kind
      where
        declarations = rewriteDeclarations selectedEnvironment
        captureStrict selected = capture
          False
          declarations previous selected captured
    expectedHole selectedEnvironment candidate context index =
      Map.lookup index (candidateTypingExpectedHoles context)
        <|> listHead (drop index (rewriteRuleHoleFamilies compiled))
        <|> classified
      where
        compiled = structuralCandidateRule candidate
        classified = case drop index
            (structuralCandidateCaptures candidate) of
          (kind, _) : _ -> case rewriteClassifyHoles selectedEnvironment
              (rewriteDeclarations selectedEnvironment) [kind] of
            [(_, family)] -> family
            _ -> Nothing
          [] -> Nothing
        listHead [] = Nothing
        listHead (selected : _) = selected
    candidateReturn selectedEnvironment candidate context =
      candidateTypingReturnType context
        <|> instantiatedReturn
        <|> rewriteRuleReturnType compiled
        <|> currentDeclaredReturn
      where
        compiled = structuralCandidateRule candidate
        currentDeclaredReturn = do
          implementation <- rewriteRuleImplementation compiled
          evaluated <- rewriteEvaluate selectedEnvironment
            (rewriteDeclarations selectedEnvironment) implementation
          functionCodomain <$> interpretedFunction evaluated
        instantiatedReturn = do
          implementation <- rewriteRuleImplementation compiled
          let inputs = map snd
                (Map.toAscList (candidateTypingInputs context))
          if length inputs /= length
              (structuralCandidateCaptures candidate)
            then Nothing
            else do
              input <- either (const Nothing) Just
                (makeArgumentativeMapPreservingSingleton inputs)
              rewriteApply selectedEnvironment
                (rewriteDeclarations selectedEnvironment)
                implementation input
    advanceOrdinary selectedEnvironment expressionValue childResults =
      case ordinaryChildSource selectedEnvironment expressionValue childResults of
        Just child -> Right (Right child)
        Nothing -> Left <$> materializeOrdinary
          selectedEnvironment expressionValue childResults
    sequenceEntries selectedEnvironment expressionValue = case expressionValue of
      AtlasMap entries -> Just
        ( selectedEnvironment
        , fst (recursiveRewriteEnvironment selectedEnvironment entries)
        , entries
        )
      Begin declarations result ->
        let entries = map DeclarationExpression declarations <> [result]
        in Just
          ( selectedEnvironment
          , fst (recursiveRewriteEnvironment selectedEnvironment entries)
          , entries
          )
      FunctionBody declarations result ->
        let contextual = enterContext Nothing selectedEnvironment
            entries = map DeclarationExpression declarations <> [result]
        in Just
          ( contextual
          , fst (recursiveRewriteEnvironment contextual entries)
          , entries
          )
      _ -> Nothing
    materializeSequence selectedEnvironment sourceExpression results = do
      expressionValue <- rebuildOrdinaryExpression sourceExpression
        (map rewriteResultExpression results)
      Right RewriteResult
        { rewriteResultExpression = expressionValue
        , rewriteResultType = rewriteResultTypeOf selectedEnvironment
            (rewriteDeclarations selectedEnvironment) expressionValue
        , rewriteResultSelection = Nothing
        }
    materializeOrdinary selectedEnvironment sourceExpression childResults = do
      expressionValue <- rebuildOrdinaryExpression
        sourceExpression (map rewriteResultExpression childResults)
      Right RewriteResult
        { rewriteResultExpression = expressionValue
        , rewriteResultType = rewriteResultTypeOf selectedEnvironment
            (rewriteDeclarations selectedEnvironment) expressionValue
        , rewriteResultSelection = Nothing
        }
    prepareCandidate selectedEnvironment selected =
      let candidate = selectedStructuralCandidate selected
          compiled = structuralCandidateRule candidate
      in prepareSelectedSyntaxMatch selectedEnvironment compiled
          (structuralCandidateMatch candidate)
    expansionWork selectedEnvironment prepared =
      case preparedExpansionSyntax prepared of
        SyntaxExpression expressionValue -> Left
          (attachRemaining prepared expressionValue)
        SyntaxBegin entries result -> Right
          ( selectedEnvironment
          , fst (recursiveRewriteEnvironment selectedEnvironment entries)
          , entries <> [result]
          )
        SyntaxFunctionBody entries result ->
          let contextual = enterContext Nothing selectedEnvironment
          in Right
            ( contextual
            , fst (recursiveRewriteEnvironment contextual entries)
            , entries <> [result]
            )
    materializeExpansion _ prepared results = do
      core <- case preparedExpansionSyntax prepared of
        SyntaxExpression expressionValue -> Right expressionValue
        SyntaxBegin entries _ -> assembleBlock Begin entries results
        SyntaxFunctionBody entries _ ->
          assembleBlock FunctionBody entries results
      pure (attachRemaining prepared core)
    assembleBlock constructor entries results = do
      let (declarationResults, resultResults) = splitAt
            (length entries) (map rewriteResultExpression results)
      declarations <- lowerBlockDeclarations declarationResults
      pure (constructor declarations (applicationFrom resultResults))
    attachRemaining prepared expressionValue = foldl FunctionApplication
      expressionValue (preparedExpansionRemaining prepared)

ordinaryChildSource
  :: RewriteEnvironment
  -> Expression
  -> [RewriteResult]
  -> Maybe (RewriteEnvironment, Expression)
ordinaryChildSource environment expressionValue results =
  case expressionValue of
    GreedyStringTemplate {} -> Nothing
    MaybeThen optional branch -> case resultCount of
      0 -> Just (environment, optional)
      1 -> Just (enterContext Nothing environment, branch)
      _ -> Nothing
    ScopeAccess source body -> case results of
      [] -> Just (environment, source)
      [sourceResult] -> Just
        ( scopedEnvironment (rewriteResultExpression sourceResult)
        , body
        )
      _ -> Nothing
    _ -> (environment,) <$> listAt resultCount
      (expressionChildren expressionValue)
  where
    resultCount = length results
    listAt selected = listHead . drop selected
    listHead [] = Nothing
    listHead (selected : _) = Just selected
    scopedEnvironment source = environment
      { rewriteRules = nubBy
          (\left right -> rewriteRule left == rewriteRule right)
          (rewriteRules environment <> map (compileRuleIn environment)
            (rewriteScopeRules environment
              (rewriteDeclarations environment) source))
      }

rebuildOrdinaryExpression
  :: Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
rebuildOrdinaryExpression source children = case source of
  GreedyStringTemplate {} -> Right source
  FunctionApplication _ Skip -> Left AmbiguousBareSkipApplication
  Begin declarations _ -> do
    let declarationCount = length declarations
        (rewrittenDeclarations, rewrittenResult) =
          splitAt declarationCount children
    lowered <- lowerBlockDeclarations rewrittenDeclarations
    Right (Begin lowered (applicationFrom rewrittenResult))
  FunctionBody declarations _ -> do
    let declarationCount = length declarations
        (rewrittenDeclarations, rewrittenResult) =
          splitAt declarationCount children
    lowered <- lowerBlockDeclarations rewrittenDeclarations
    Right (FunctionBody lowered (applicationFrom rewrittenResult))
  _ -> Right (fst (runState
      (traverseExpressionChildren replaceChild source) 0))
  where
    replacements = Map.fromList (zip [0 :: Int ..] children)
    replaceChild :: Expression -> State Int Expression
    replaceChild _ = state $ \index ->
      (replacements Map.! index, index + 1)

structuralCandidatesFor
  :: Bool
  -> RewriteEnvironment
  -> Expression
  -> [StructuralCandidate]
structuralCandidatesFor includeConcatenation environment value =
    enumerate value [] (rewriteRules environment)
      <> scopedCandidates
  where
    enumerate selectedValue = go
      where
        facts = expressionFacts selectedValue
        go _ [] = []
        go earlier (rule : remaining)
          | not (ruleLiteralsPresent rule facts) =
              go (rule : earlier) remaining
          | otherwise = enumerateRuleStructuralCandidates
                rule
                ( literalBoundaryCandidates selectedValue rule
                    <> syntaxProjectionCandidates
                      (includeConcatenation || not (earlierPrefixPending earlier))
                      (syntaxTemplate (rewriteRule rule)) selectedValue
                ) <> go (rule : earlier) remaining
        earlierPrefixPending = any (\earlierRule ->
          not (null (rewriteRuleLiteralPrefix earlierRule))
            && ruleLiteralsPresent earlierRule facts)
        literalBoundaryCandidates selected rule = case rewriteRuleLiteralPrefix rule of
          first : _
            | any isHole (syntaxTemplatePieces
                (syntaxTemplate (rewriteRule rule)))
            , literalOccurrences first selected > 1 ->
                maybeToList (literalBoundaryCandidate
                  (syntaxTemplate (rewriteRule rule)) selected)
          _ -> []
    scopedCandidates = case applicationSpine value of
      (ScopeAccess source body, arguments@(_ : _)) ->
        let scopedRules = rewriteScopeRules environment
              (rewriteDeclarations environment) source
            compiled = map (compileRuleIn environment) scopedRules
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue [] compiled
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
      Def inner -> do
        (before, suffix) <- splitAtLiteral literal inner
        pure (Def <$> before, suffix)
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

advanceScopeResolved
  :: RewriteEnvironment
  -> Expression
  -> Expression
  -> (RewriteEnvironment, [RewriteRule])
advanceScopeResolved environment entry resolved = (next, introduced)
  where
    introduced = case dependentDeclaration resolved of
      Nothing -> []
      Just _ -> compileScopedDeclarationRules environment
        retainedDeclarations (declarationRuleBranches resolved)
    retainedDeclarations = filter
      (null . filter (`elem` names) . bindingNames)
      (rewriteDeclarations environment)
    names = bindingNames entry
    next = case dependentDeclaration resolved of
      Nothing -> environment
      Just _ -> advanceScopeCompiled environment entry introduced

advanceScopeCompiled
  :: RewriteEnvironment
  -> Expression
  -> [RewriteRule]
  -> RewriteEnvironment
advanceScopeCompiled environment entry introduced = environment
  { rewriteRules = retained <> introduced
  , rewriteDeclarations = retainedDeclarations <> [entry]
  }
  where
    names = bindingNames entry
    retained = filter ((`notElem` names) . rewriteRuleName)
      (rewriteRules environment)
    retainedDeclarations = filter
      (null . filter (`elem` names) . bindingNames)
      (rewriteDeclarations environment)

compileScopedDeclarationRules
  :: RewriteEnvironment
  -> [Expression]
  -> [(DependentDeclaration Expression, Int, SyntaxRule)]
  -> [RewriteRule]
compileScopedDeclarationRules environment declarations branches =
  mapMaybe compile branches
  where
    rules = [ rule | (_, _, rule) <- branches ]
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
    compile (declaration, branch, rule)
      | Just applicationImplementation <- syntaxApplicationImplementation rule
      , containsRuntimeFunctionBody applicationImplementation = Nothing
      | Just _ <- syntaxApplicationImplementation rule
      , Nothing <- rewriteRuleSyntaxInsertion compiled = Nothing
      | otherwise = Just compiled
          { rewriteRuleEvaluation = Just evaluate
          , rewriteRuleHoleFamilies = holeFamilies
          }
      where
        specializedRule = rule
          { syntaxTemplate = SyntaxTemplate specializedPieces }
        (specializedPieces, holeFamilies) = foldr classifyPiece ([], [])
          (syntaxTemplatePieces (syntaxTemplate rule))
        compiled = (compileDependentRewriteRule
            declaration branch specializedRule)
          { rewriteRuleSyntaxInsertion = syntaxInsertion
          , rewriteRuleRuntimeInsertion = runtimeInsertion
          , rewriteRuleReturnType =
              resolvedRuleReturnType evaluate specializedRule
          }
        implementation = syntaxRuleAdapter specializedRule
        hasHoles = any isHole specializedPieces
        evaluatedImplementation
          | hasHoles = implementation >>= evaluate
          | otherwise = Nothing
        syntaxInsertion = evaluatedImplementation >>=
          syntaxFunctionInsertionFromValue
        runtimeInsertion
          | hasHoles = do
              value <- evaluatedImplementation <|> do
                selected <- implementation
                attached <- attachedFunctionImplementation selected
                evaluate attached
              interpretedRuntimeFunctionInsertion value
          | otherwise = Nothing
        isHole SyntaxHole {} = True
        isHole SyntaxLiteral {} = False
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
    Def value -> Def (resolveDependentDeclarationHead environment value)
    Val value -> Val (resolveDependentDeclarationHead environment value)
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
      atom -> atom

    firstDeclaration _ [] = Nothing
    firstDeclaration requested (candidate : remaining) =
      case dependentDeclaration candidate of
        Just declaration
          | requested `elem` bindingNames candidate ->
              Just declaration
        _ -> firstDeclaration requested remaining
