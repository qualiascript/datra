-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Application spines retain logical line breaks until a declaration has
-- selected the extent it wants to match.
module SyntaxRewriting
  ( SyntaxType (..)
  , SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , RewriteLocus (..)
  , SyntaxRewriteFailure (..)
  , rewriteStandaloneSyntax
  , rewriteResourceSyntax
  , rewriteResourceSyntaxLocated
  ) where
import Control.Applicative ((<|>))
import Data.Map.Strict qualified as Map
import DatraLanguage.AST
import DatraLanguage.Application
  ( applicationFrom
  , applicationSpine
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxRewriteFailure (..) )
import DatraLanguage.Diagnostics
  ( Located (..)
  , SourceSpan
  )
import Parsing (ResourceEnvelope (..))
import DatraTypes
  ( Decision (..)
  , SyntaxFunctionExpansion (..)
  , SyntaxFunctionInsertion (..)
  , decideValueSubfederation
  )
import StringExpression
  ( TemplateSelection (..)
  )
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , SyntaxRule (..)
  , SyntaxRuleMode (..)
  )
import StringInterpolation.Matching
  ( SyntaxMatch (..) )
import SyntaxRewriting.Types
  ( CandidateRejection
  , CandidateTypingContext (..)
  , Compatibility (..)
  , PreparedExpansion (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , RewriteLocus (..)
  , SelectedCandidate (..)
  , StructuralCandidate (..)
  , SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , SyntaxType (..)
  )
import SyntaxRewriting.Candidates
  ( compileRewriteRule
  , enumerateRuleStructuralCandidates
  , structuralCandidateMatch
  )
import SyntaxRewriting.Capture
  ( prepareStructuralCapture )
import SyntaxRewriting.Diagnostics
  ( candidateRejectionAt
  , reportCandidateRejections
  )
import SyntaxRewriting.PostRewrite
  ( terminalFallback
  , postRewriteExpansion
  )
import SyntaxRewriting.Stack
  ( RewriteStackOperations (..)
  , runRewriteStack
  )

type RuntimeSyntaxContext = SyntaxContext SyntaxType
type RuntimeSyntaxRuleFamily = SyntaxRuleFamily SyntaxType
type RuntimeRewriteRule = RewriteRule SyntaxType
type RuntimeRewriteResult = RewriteResult SyntaxType
type RuntimeCandidateRejection = CandidateRejection SyntaxType
type RuntimeStructuralCandidate = StructuralCandidate SyntaxType

rewriteRuleImplementation :: RuntimeRewriteRule -> Expression
rewriteRuleImplementation compiled =
  case attachedFunctionImplementation implementation of
    Just adapter -> adapter
    Nothing -> implementation
  where
    implementation = syntaxRuleAdapter (rewriteRule compiled)

prepareSelectedSyntaxMatch
  :: RuntimeRewriteRule
  -> SyntaxMatch
  -> PreparedExpansion
prepareSelectedSyntaxMatch rule matched = PreparedExpansion
  { preparedExpansionSyntax = selectedExpansion
  , preparedExpansionRemaining = syntaxMatchRemaining matched
  }
  where
    selectedExpansion = case syntaxRuleMode (rewriteRule rule) of
      ExpressionMode -> SyntaxExpression
        (syntaxRuleAdapter (rewriteRule rule))
      FunctionMode -> case directExpansion of
        Just value -> value
        Nothing -> directSyntaxFunctionExpansion rule captures
    selection = syntaxMatchSelection matched
    captures = templateSelectionCaptures selection
    directExpansion = rewriteRuleSyntaxInsertion rule >>= \insertion ->
      applySyntaxFunction insertion captures

syntaxTypesCompatibility :: SyntaxType -> SyntaxType -> Compatibility
syntaxTypesCompatibility source target
  | syntaxTypeExpression source == syntaxTypeExpression target =
      CompatibilityProved
  | otherwise = case
      (syntaxTypeRuntimeValue source, syntaxTypeRuntimeValue target) of
      (Just sourceValue, Just targetValue) ->
        case decideValueSubfederation sourceValue targetValue of
          DecisionProved () -> CompatibilityProved
          DecisionRefuted -> CompatibilityRefuted
          DecisionUndecidable -> CompatibilityDeferred
      _ -> CompatibilityDeferred

compileRuleWith
  :: (Expression -> Maybe SyntaxFunctionInsertion)
  -> (Expression -> SyntaxType)
  -> SyntaxRule
  -> RuntimeRewriteRule
compileRuleWith resolveInsertion evaluate rule = compiled
  { rewriteRuleSyntaxInsertion = insertion
  }
  where
    compiled = compileRewriteRule (evaluate (syntaxRuleCodomain rule)) rule
    insertion = resolveInsertion (rewriteRuleImplementation compiled)

compileRuleFamily
  :: (Expression -> Maybe SyntaxFunctionInsertion)
  -> RuntimeSyntaxRuleFamily
  -> [RuntimeRewriteRule]
compileRuleFamily resolveInsertion family =
  [ (compileRuleWith resolveInsertion
        (syntaxRuleFamilyEvaluate family) rule)
      { rewriteRuleBranch = branch
      }
  | (branch, rule) <- syntaxRuleFamilyRules family
  ]

contextRewriteRules
  :: RuntimeSyntaxContext
  -> [RuntimeRewriteRule]
contextRewriteRules context = concatMap
  (filter activeRewriteRule
    . compileRuleFamily (contextSyntaxInsertion context))
  (contextRuleFamilies context)
  where
    activeRewriteRule compiled = case declarativeMatcherPlan
        (rewriteRule compiled) of
      LiteralExpressionMatcher {} -> True
      IdentifierApplicationMatcher {} -> case
          rewriteRuleSyntaxInsertion compiled of
        Just _ -> True
        Nothing -> False

-- | Rewrite one already-delimited expression with the same declaration
-- environment used by resource rewriting.  Canonical values cross this
-- boundary after rendering and parsing, so they must recover dependent
-- declaration invocations before closure collection inspects references.
rewriteStandaloneSyntax
  :: RuntimeSyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandaloneSyntax context =
  runRewriteExpression context

rewriteResourceSyntax
  :: ResourceEnvelope
  -> RuntimeSyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntax envelope context raw =
  rewriteResourceSyntaxWithSpan Nothing envelope context raw

rewriteResourceSyntaxLocated
  :: ResourceEnvelope
  -> RuntimeSyntaxContext
  -> Located Expression
  -> Either SyntaxRewriteFailure (Located Expression)
rewriteResourceSyntaxLocated envelope context
    (Located sourceSpan raw) =
  Located sourceSpan <$> rewriteResourceSyntaxWithSpan
    (Just sourceSpan) envelope context raw

rewriteResourceSyntaxWithSpan
  :: Maybe SourceSpan
  -> ResourceEnvelope
  -> RuntimeSyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntaxWithSpan sourceSpan envelope context raw =
  case (envelope, raw) of
    (ExplicitMapEnvelope, expressionValue) ->
      runRewriteExpression initial expressionValue
    (ImplicitBlockEnvelope, AtlasMap entries) -> rewriteImplicitResource entries
    (ImplicitBlockEnvelope, expressionValue) ->
      rewriteImplicitResource [expressionValue]
  where
    initial = context { contextSourceSpan = sourceSpan }
    rewriteImplicitResource entries = do
      rewrittenContainer <- runRewriteExpression initial
        (AtlasMap entries)
      let rewritten = case rewrittenContainer of
            AtlasMap selected -> selected
            selected -> [selected]
      contextAssembleImplicitResource initial rewritten

runRewriteExpression
  :: RuntimeSyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure Expression
runRewriteExpression environment value = do
  (result, rejections) <- runStructuralCandidates environment value
  case (rewriteResultSelection result, rejections) of
    (Nothing, _ : _) -> Left
      (RejectedSyntaxCandidates (reportCandidateRejections rejections))
    _ -> Right (rewriteResultExpression result)

directSyntaxFunctionExpansion
  :: RuntimeRewriteRule
  -> [Expression]
  -> SyntaxFunctionExpansion
directSyntaxFunctionExpansion selectedRule captures =
  SyntaxExpression (FunctionApplication
    (rewriteRuleImplementation selectedRule) suppliedInput)
  where
    suppliedInput = case captures of
      [] -> AtlasMap []
      [capture] -> capture
      _ -> AtlasMap captures

runStructuralCandidates
  :: RuntimeSyntaxContext
  -> Expression
  -> Either SyntaxRewriteFailure
      (RuntimeRewriteResult, [RuntimeCandidateRejection])
runStructuralCandidates environment source =
  runRewriteStack operations environment source
  where
    operations = RewriteStackOperations
      { stackEnumerateCandidates = structuralCandidatesFor
      , stackPostRewrite = \selectedEnvironment ->
          terminalFallback (declaredExtent selectedEnvironment)
      , stackPrepareStructuralCapture = prepareStructuralCapture
      , stackExpectedHole = expectedHole
      , stackCandidateReturn = candidateReturn
      , stackTypesCompatible = syntaxTypesCompatibility
      , stackRewriteScope = contextRewriteScope
      , stackFinalizeOrdinary = finalizeOrdinary
      , stackPublishChild = publishChild
      , stackPrepareCandidate = prepareCandidate
      , stackExpandCandidate = expandCandidate
      , stackCandidateRejection = \selectedEnvironment details ->
          candidateRejectionAt
            (contextSourceSpan selectedEnvironment) details
      }
    finalizeOrdinary selectedContext rawExpression = case expressionValue of
      FunctionApplication _ Skip -> Left AmbiguousBareSkipApplication
      _ -> Right RewriteResult
        { rewriteResultExpression = expressionValue
        , rewriteResultType = contextResultType selectedContext expressionValue
        , rewriteResultSelection = Nothing
        , rewriteResultDeferred = []
        }
      where
        expressionValue = normalizeRewrittenSequence rawExpression

    normalizeRewrittenSequence value = case value of
      AtlasMap members -> rebuild AtlasMap (concatMap flatten members)
      MapSequence members -> rebuild MapSequence (concatMap flatten members)
      ArgumentativeMap members ->
        ArgumentativeMap (concatMap flatten members)
      _ -> value
      where
        flatten (AtlasMap members) = members
        flatten (MapSequence members) = members
        flatten member = [member]
        rebuild _ [] = AtlasMap []
        rebuild constructor members =
          case filter nonempty members of
            [] -> AtlasMap []
            [member] -> member
            nonemptyMembers -> constructor nonemptyMembers
        nonempty (AtlasMap []) = False
        nonempty (MapSequence []) = False
        nonempty _ = True

    expectedHole selectedEnvironment candidate context index =
      Map.lookup index (candidateTypingExpectedHoles context)
        <|> classified
      where
        classified = case drop index
            (structuralCandidateCaptures candidate) of
          (kind, _, _) : _ -> case contextClassify selectedEnvironment [kind] of
            [(_, family)] -> family
            _ -> Nothing
          [] -> Nothing
    candidateReturn _ candidate _ = rewriteRuleReturnType compiled
      where
        compiled = structuralCandidateRule candidate
    prepareCandidate _ selected =
      let candidate = selectedStructuralCandidate selected
          compiled = structuralCandidateRule candidate
      in prepareSelectedSyntaxMatch compiled
          (structuralCandidateMatch candidate)
    expandCandidate selectedEnvironment prepared = do
      expressionValue <- contextExpandSyntax selectedEnvironment
        (preparedExpansionSyntax prepared)
      pure (postRewriteExpansion
        (declaredExtent selectedEnvironment)
        expressionValue
        (preparedExpansionRemaining prepared))

publishChild
  :: RuntimeSyntaxContext
  -> Expression
  -> Int
  -> RuntimeRewriteResult
  -> Either SyntaxRewriteFailure (Maybe RuntimeSyntaxContext)
publishChild environment parent cursor result = Right $ case parent of
  AtlasMap {} -> contextPublish environment entry
  MapSequence {} -> contextPublish environment entry
  Begin declarations _
    | cursor < length declarations -> contextPublish environment entry
  FunctionBody declarations _
    | cursor < length declarations -> contextPublish environment entry
  _ -> Nothing
  where
    entry = rewriteResultExpression result

structuralCandidatesFor
  :: RuntimeSyntaxContext
  -> Expression
  -> [RuntimeStructuralCandidate]
structuralCandidatesFor = declaredCandidatesFor

declaredExtent
  :: RuntimeSyntaxContext
  -> Expression
  -> Maybe (Expression, [Expression])
declaredExtent environment value = case declaredCandidatesFor environment value of
  candidates -> case filter
      (rewriteRuleClaimsSyntax . structuralCandidateRule) candidates of
    candidate : _ -> Just
      ( templateSelectionWhole (structuralCandidateSelection candidate)
      , structuralCandidateRemaining candidate
      )
    [] -> Nothing

rewriteRuleClaimsSyntax :: RuntimeRewriteRule -> Bool
rewriteRuleClaimsSyntax compiled = case declarativeMatcherPlan
    (rewriteRule compiled) of
  IdentifierApplicationMatcher {} -> True
  LiteralExpressionMatcher (LiteralExpressionPattern parts) ->
    any expressionLiteral parts
  where
    expressionLiteral (LiteralExpressionPatternLiteral literal) =
      not (null literal)
    expressionLiteral LiteralExpressionPatternCapture {} = False

declaredCandidatesFor
  :: RuntimeSyntaxContext
  -> Expression
  -> [RuntimeStructuralCandidate]
declaredCandidatesFor environment value =
    enumerate value (contextRewriteRules environment) <> scopedCandidates
  where
    enumerate selectedValue = concatMap (\rule ->
      enumerateRuleStructuralCandidates rule selectedValue)
    scopedCandidates = case applicationSpine value of
      (ScopeAccess source selector, arguments@(_ : _)) ->
        let scopedEnvironment = contextScope environment source
            compiled = contextRewriteRules scopedEnvironment
            scopedValue = applicationFrom
              (selectorApplicationHead selector : arguments)
        in enumerate scopedValue compiled
      (ScopedExpression source body, arguments@(_ : _)) ->
        let scopedEnvironment = contextScope environment source
            compiled = contextRewriteRules scopedEnvironment
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue compiled
      (WithScopes sources body, arguments@(_ : _)) ->
        let scopedEnvironment = foldl contextScope environment sources
            compiled = contextRewriteRules scopedEnvironment
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue compiled
      _ -> []
    selectorApplicationHead selector = case literalIdentifierName selector of
      Just name -> IdentifierReference name
      Nothing -> identifierExpressionExpression selector
