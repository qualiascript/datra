{-# LANGUAGE LambdaCase #-}
-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Source layout has disappeared at this boundary: application spines are
-- matched directly, while an 'AtlasMap' supplies the contextual boundary for
-- block captures.
module SyntaxRewriting
  ( SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , SyntaxRewriteFailure (..)
  , rewriteStandaloneSyntax
  , rewriteResourceSyntax
  , rewriteResourceSyntaxLocated
  ) where
import Control.Applicative ((<|>))
import Data.List (nub)
import Data.Map.Strict qualified as Map
import Data.Maybe (maybeToList)
import Data.Set qualified as Set
import DatraLanguage.AST
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Diagnostics.Application
  ( SyntaxRewriteFailure (..) )
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
  , interpretedFunction
  , interpretedFunctionBody
  , makeArgumentativeMapPreservingSingleton
  , subfederationValues
  )
import DatraLanguage.SyntaxTemplate
  ( SyntaxPiece (..)
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , expandSyntax
  , syntaxApplicationImplementation
  , syntaxRuleAdapter
  )
import SyntaxTemplateMatching
  ( SyntaxMatch (..) )
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
  , PreparedExpansion (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , SelectedCandidate (..)
  , StructuralCandidate (..)
  , SyntaxContext (..)
  , SyntaxRuleFamily (..)
  )
import SyntaxRewriting.Candidates
  ( compileRewriteRule
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
  :: SyntaxContext
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
      Nothing -> contextEvaluate environment
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

isValueSubfederation :: InterpretedValue -> InterpretedValue -> Bool
isValueSubfederation source target =
  case subfederationValues source target >>= booleanCondition of
    Right accepted -> accepted
    Left _ -> False

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

compileRuleFamily :: SyntaxRuleFamily -> [RewriteRule]
compileRuleFamily family =
  [ (compileRuleWith (syntaxRuleFamilyEvaluate family) rule)
      { rewriteRuleBranch = branch
      , rewriteRuleEvaluation = Just (syntaxRuleFamilyEvaluate family)
      , rewriteRuleHoleFamilies =
          [ selected
          | SyntaxHole kind <- syntaxTemplatePieces (syntaxTemplate rule)
          , let selected = case syntaxRuleFamilyClassify family [kind] of
                  [(_, value)] -> value
                  _ -> Nothing
          ]
      }
  | (branch, rule) <- syntaxRuleFamilyRules family
  ]

contextRewriteRules :: SyntaxContext -> [RewriteRule]
contextRewriteRules = concatMap compileRuleFamily . contextRuleFamilies

-- | Rewrite one already-delimited expression with the same declaration
-- environment used by resource rewriting.  Canonical values cross this
-- boundary after rendering and parsing, so they must recover dependent
-- declaration invocations before closure collection inspects references.
rewriteStandaloneSyntax
  :: SyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandaloneSyntax context =
  runRewriteExpression (contextCapture context) context

rewriteResourceSyntax
  :: ResourceEnvelope
  -> SyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntax envelope context raw =
  rewriteResourceSyntaxWithSpan Nothing envelope context raw

rewriteResourceSyntaxLocated
  :: ResourceEnvelope
  -> SyntaxContext
  -> Located Expression
  -> Either SyntaxRewriteFailure (Located Expression)
rewriteResourceSyntaxLocated envelope context
    (Located sourceSpan raw) =
  Located sourceSpan <$> rewriteResourceSyntaxWithSpan
    (Just sourceSpan) envelope context raw

rewriteResourceSyntaxWithSpan
  :: Maybe SourceSpan
  -> ResourceEnvelope
  -> SyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntaxWithSpan sourceSpan envelope context raw =
  case (envelope, raw) of
    (ExplicitMapEnvelope, expressionValue) ->
      runRewriteExpression capture initial expressionValue
    (ImplicitBlockEnvelope, AtlasMap entries) -> rewriteImplicitResource entries
    (ImplicitBlockEnvelope, expressionValue) ->
      rewriteImplicitResource [expressionValue]
  where
    capture = contextCapture context
    initial = context { contextSourceSpan = sourceSpan }
    rewriteImplicitResource entries = do
      rewrittenContainer <- runRewriteExpression capture initial
        (AtlasMap entries)
      let rewritten = case rewrittenContainer of
            AtlasMap selected -> selected
            selected -> [selected]
      contextAssembleImplicitResource initial rewritten

publishSequenceResult
  :: SyntaxContext
  -> SyntaxContext
  -> [Expression]
  -> [(Int, RewriteResult)]
  -> Int
  -> RewriteResult
  -> Either SyntaxRewriteFailure (Maybe SyntaxContext)
publishSequenceResult _initial environment _sources _earlier _position result = do
  let entry = rewriteResultExpression result
  Right (contextPublish environment entry)

runRewriteExpression
  :: CaptureHole
  -> SyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
runRewriteExpression capture environment value = do
  (result, rejections) <- runStructuralCandidates capture environment value
  case (rewriteResultSelection result, rejections) of
    (Nothing, _ : _) -> Left
      (RejectedSyntaxCandidates (reportCandidateRejections rejections))
    _ -> Right (rewriteResultExpression result)

directSyntaxFunctionExpansion
  :: SyntaxContext
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
    evaluateHere = contextEvaluate environment
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

runStructuralCandidates
  :: CaptureHole
  -> SyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure (RewriteResult, [CandidateRejection])
runStructuralCandidates capture environment source =
  runRewriteStack operations environment source
  where
    operations = RewriteStackOperations
      { stackEnumerateCandidates = structuralCandidatesFor
      , stackCaptureHole = captureHole
      , stackExpectedHole = expectedHole
      , stackCandidateReturn = candidateReturn
      , stackTypesCompatible = isValueSubfederation
      , stackOrdinaryChild = ordinaryChildSource
      , stackFinalizeOrdinary = finalizeOrdinary
      , stackAssembleSequence = contextAssembleSequence
      , stackAssembleExpansion = contextAssembleExpansion
      , stackSequenceEntries = sequenceEntries
      , stackPublishDeclaration = publishSequenceResult
      , stackPrepareCandidate = prepareCandidate
      , stackExpansionWork = expansionWork
      , stackCandidateRejection = \selectedEnvironment details ->
          candidateRejectionAt
            (contextSourceSpan selectedEnvironment) details
      }
    finalizeOrdinary selectedContext expressionValue = case expressionValue of
      FunctionApplication _ Skip -> Left AmbiguousBareSkipApplication
      _ -> Right RewriteResult
        { rewriteResultExpression = expressionValue
        , rewriteResultType = contextResultType selectedContext expressionValue
        , rewriteResultSelection = Nothing
        }
    captureHole selectedEnvironment _ previous kind captured =
      case contextClassify selectedEnvironment [kind] of
        [(specialized, Just expected)]
          | Just actual <- contextResultType selectedEnvironment captured
          , isValueSubfederation actual expected -> Just captured
          | otherwise -> captureStrict specialized
        [(specialized, _)] -> captureStrict specialized
        _ -> captureStrict kind
      where
        captureStrict selected = capture
          False
          previous selected captured
    expectedHole selectedEnvironment candidate context index =
      Map.lookup index (candidateTypingExpectedHoles context)
        <|> listHead (drop index (rewriteRuleHoleFamilies compiled))
        <|> classified
      where
        compiled = structuralCandidateRule candidate
        classified = case drop index
            (structuralCandidateCaptures candidate) of
          (kind, _) : _ -> case contextClassify selectedEnvironment [kind] of
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
          evaluated <- contextEvaluate selectedEnvironment implementation
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
              contextApply selectedEnvironment implementation input
    sequenceEntries selectedEnvironment expressionValue = case expressionValue of
      AtlasMap entries -> Just
        ( selectedEnvironment
        , contextRecursive selectedEnvironment entries
        , entries
        )
      Begin declarations result ->
        let entries = map DeclarationExpression declarations <> [result]
        in Just
          ( selectedEnvironment
          , contextRecursive selectedEnvironment entries
          , entries
          )
      FunctionBody declarations result ->
        let contextual = contextEnter selectedEnvironment Nothing
            entries = map DeclarationExpression declarations <> [result]
        in Just
          ( contextual
          , contextRecursive contextual entries
          , entries
          )
      _ -> Nothing
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
          , contextRecursive selectedEnvironment entries
          , entries <> [result]
          )
        SyntaxFunctionBody entries result ->
          let contextual = contextEnter selectedEnvironment Nothing
          in Right
            ( contextual
            , contextRecursive contextual entries
            , entries <> [result]
            )
    attachRemaining prepared expressionValue = foldl FunctionApplication
      expressionValue (preparedExpansionRemaining prepared)

ordinaryChildSource
  :: SyntaxContext
  -> Expression
  -> Int
  -> Maybe (SyntaxContext, Expression)
ordinaryChildSource environment expressionValue cursor =
  case expressionValue of
    GreedyStringTemplate {} -> Nothing
    MaybeThen optional branch -> case cursor of
      0 -> Just (environment, optional)
      1 -> Just (contextEnter environment Nothing, branch)
      _ -> Nothing
    ScopeAccess source body -> case cursor of
      0 -> Just (environment, source)
      1 -> Just (scopedEnvironment source, body)
      _ -> Nothing
    _ -> (environment,) <$> listAt cursor
      (expressionChildren expressionValue)
  where
    listAt selected = listHead . drop selected
    listHead [] = Nothing
    listHead (selected : _) = Just selected
    scopedEnvironment source =
      (contextScope environment source)
        { contextSourceSpan = contextSourceSpan environment }

structuralCandidatesFor
  :: Bool
  -> SyntaxContext
  -> Expression
  -> [StructuralCandidate]
structuralCandidatesFor includeConcatenation environment value =
    enumerate value [] (contextRewriteRules environment)
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
        let scopedEnvironment = contextScope environment source
            compiled = contextRewriteRules scopedEnvironment
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
      DependentArgument name annotation ->
        splitDependentArgument name annotation Nothing
      MapSpecification _ (DependentArgument _ Nothing) -> Nothing
      MapSpecification given (DependentArgument name annotation) ->
        splitDependentArgument name annotation (Just given)
      _ -> Nothing

    splitDependentArgument name annotation given =
      case given >>= splitAtLiteral literal of
        Just (before, suffix) ->
          Just
            ( Just (maybe
                (DependentArgument name annotation)
                (\givenValue -> MapSpecification givenValue
                  (DependentArgument name annotation))
                before)
            , suffix
            )
        Nothing -> do
          explicit <- annotation
          (before, suffix) <- splitAtLiteral literal explicit
          pure
            ( (\beforeAnnotation ->
                maybe
                  (DependentArgument name (Just beforeAnnotation))
                  (\givenValue -> MapSpecification givenValue
                    (DependentArgument name (Just beforeAnnotation)))
                  given) <$> before
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
