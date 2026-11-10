-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Source layout has disappeared at this boundary: application spines are
-- matched directly, while an 'AtlasMap' supplies the contextual boundary for
-- block captures.
module SyntaxRewriting
  ( SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , RewriteLocus (..)
  , SyntaxRewriteFailure (..)
  , rewriteStandaloneSyntax
  , rewriteResourceSyntax
  , rewriteResourceSyntaxLocated
  ) where
import Control.Applicative ((<|>))
import Data.List (nub)
import Data.Map.Strict qualified as Map
import Data.Maybe (maybeToList)
import DatraLanguage.AST
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
import StringExpression
  ( StringExpression (LiteralString)
  , TemplateSelection (..)
  )
import StringInterpolation
  ( SyntaxRule (..)
  , expandSyntax
  , syntaxApplicationImplementation
  , syntaxRuleAdapter
  )
import StringInterpolation.Matching
  ( SyntaxMatch (..) )
import StringInterpolation.Projection
  ( applicationFrom
  , applicationSpine
  )
import SyntaxRewriting.Types
  ( CandidateRejection
  , CandidateTypingContext (..)
  , CaptureHole
  , PreparedExpansion (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , RewriteLocus (..)
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
      | any isHole
          (stringInterpolationTemplate (rewriteRule rule)) = do
          implementation <- rewriteRuleImplementation rule
          insertion <- case rewriteRuleEvaluation rule of
            Just _ -> rewriteRuleSyntaxInsertion rule
            Nothing -> syntaxFunctionInsertion evaluate implementation
          applySyntaxFunction insertion (insertionCaptures rule captures)
      | otherwise = Nothing
    isHole (StringTemplateInterpolation (LiteralString _)) = False
    isHole StringTemplateInterpolation {} = True

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
          | StringTemplateInterpolation kind <- stringInterpolationTemplate rule
          , case kind of
              LiteralString {} -> False
              _ -> True
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
      | StringTemplateInterpolation kind <-
          stringInterpolationTemplate (rewriteRule rule)
      , case kind of
          LiteralString {} -> False
          _ -> True
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
      , stackRewriteScope = contextRewriteScope
      , stackFinalizeOrdinary = finalizeOrdinary
      , stackPublishChild = publishChild
      , stackPrepareCandidate = prepareCandidate
      , stackExpandCandidate = expandCandidate
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
        captureStrict selected = capture previous selected captured
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
    prepareCandidate selectedEnvironment selected =
      let candidate = selectedStructuralCandidate selected
          compiled = structuralCandidateRule candidate
      in prepareSelectedSyntaxMatch selectedEnvironment compiled
          (structuralCandidateMatch candidate)
    expandCandidate selectedEnvironment prepared = do
      expressionValue <- contextExpandSyntax selectedEnvironment
        (preparedExpansionSyntax prepared)
      pure (foldl FunctionApplication expressionValue
        (preparedExpansionRemaining prepared))

publishChild
  :: SyntaxContext
  -> Expression
  -> Int
  -> RewriteResult
  -> Either SyntaxRewriteFailure (Maybe SyntaxContext)
publishChild environment parent cursor result = Right $ case parent of
  AtlasMap {} -> contextPublish environment entry
  Begin declarations _
    | cursor < length declarations -> contextPublish environment entry
  FunctionBody declarations _
    | cursor < length declarations -> contextPublish environment entry
  _ -> Nothing
  where
    entry = rewriteResultExpression result

structuralCandidatesFor
  :: SyntaxContext
  -> Expression
  -> [StructuralCandidate]
structuralCandidatesFor environment value =
    enumerate value (contextRewriteRules environment)
      <> scopedCandidates
  where
    enumerate selectedValue = concatMap (\rule ->
      enumerateRuleStructuralCandidates rule [selectedValue])
    scopedCandidates = case applicationSpine value of
      (ScopeAccess source body, arguments@(_ : _)) ->
        let scopedEnvironment = contextScope environment source
            compiled = contextRewriteRules scopedEnvironment
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue compiled
      _ -> []
