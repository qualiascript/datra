-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Application spines retain logical line breaks until a declaration has
-- selected the extent it wants to match.
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
import Data.Map.Strict qualified as Map
import DatraLanguage.AST
import DatraLanguage.Application
  ( applicationFrom
  , applicationSpine
  )
import DatraLanguage.Diagnostics.Application
  ( CandidateRejectionReason (..)
  , SyntaxRewriteFailure (..)
  )
import DatraLanguage.Diagnostics
  ( Located (..)
  , SourceSpan
  )
import Parsing (ResourceEnvelope (..))
import DatraTypes
  ( Decision (..)
  , InterpretedValue
  , asciiStringValue
  , decideValueSubfederation
  )
import StringExpression
  ( StringExpression (..)
  , TemplateSelection (..)
  )
import StringInterpolation
  ( DeclarativeCapture (..)
  , DeclarativeMatcherPlan (..)
  , LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , SyntaxRule (..)
  , SyntaxRuleMode (..)
  )
import StringInterpolation.Matching
  ( SyntaxMatch (..) )
import SyntaxRewriting.Types
  ( CandidateRejection
  , CandidateDecision (..)
  , CandidateRejectionDetails (..)
  , CandidateTypingContext (..)
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

type RuntimeSyntaxContext = SyntaxContext
type RuntimeSyntaxRuleFamily = SyntaxRuleFamily
type RuntimeRewriteRule = RewriteRule
type RuntimeRewriteResult = RewriteResult
type RuntimeCandidateRejection = CandidateRejection
type RuntimeStructuralCandidate = StructuralCandidate

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
prepareSelectedSyntaxMatch rule matched =
  case syntaxRuleMode (rewriteRule rule) of
    ExpressionMode -> prepared
      (syntaxRuleAdapter (rewriteRule rule))
    FunctionMode -> prepared
      (functionApplicationExpression rule captures)
  where
    selection = syntaxMatchSelection matched
    captures = templateSelectionCaptures selection
    prepared expansion = PreparedExpansion
      { preparedExpansionExpression = expansion
      , preparedExpansionRemaining = syntaxMatchRemaining matched
      }

compileRuleWith
  :: (Expression -> Maybe InterpretedValue)
  -> SyntaxRule
  -> RuntimeRewriteRule
compileRuleWith evaluate rule =
  compileRewriteRule (evaluate (syntaxRuleCodomain rule)) rule

compileRuleFamily
  :: RuntimeSyntaxRuleFamily
  -> [RuntimeRewriteRule]
compileRuleFamily family =
  [ (compileRuleWith (syntaxRuleFamilyEvaluate family) rule)
      { rewriteRuleBranch = branch
      }
  | (branch, rule) <- syntaxRuleFamilyRules family
  ]

contextRewriteRules
  :: RuntimeSyntaxContext
  -> [RuntimeRewriteRule]
contextRewriteRules = concatMap compileRuleFamily . contextRuleFamilies

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
  -- OBSOLETE normalization seam: the rewrite stack must return the final tree
  -- instead of relying on this post-rewrite reshaping pass.
  normalizeExpression <$> case (envelope, raw) of
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

functionApplicationExpression
  :: RuntimeRewriteRule
  -> [Expression]
  -> Expression
functionApplicationExpression selectedRule captures =
  FunctionApplication
    (rewriteRuleImplementation selectedRule) suppliedInput
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
      { stackExhausted = RewriteStackExhausted
      , stackEnumerateCandidates = structuralCandidatesFor
      , stackPostRewrite = \selectedEnvironment ->
          terminalFallback (declaredExtent selectedEnvironment)
      , stackPrepareStructuralCapture = prepareStructuralCapture
      , stackExpectedHole = expectedHole
      , stackCandidateReturn = candidateReturn
      , stackDecideCandidate = decideCandidate
      , stackBlockerResolved = blockerResolved
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
        }
      where
        expressionValue = obsoleteNormalizeRewrittenSequence rawExpression

    -- OBSOLETE: candidate expansion currently relies on a second, external
    -- sequence-flattening pass. Rewriting should construct the final sequence
    -- shape directly instead.
    obsoleteNormalizeRewrittenSequence value = case value of
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
    candidateReturn selectedEnvironment candidate _ =
      rewriteRuleReturnType compiled <|>
        contextResultType selectedEnvironment
          (syntaxRuleCodomain (rewriteRule compiled))
      where
        compiled = structuralCandidateRule candidate
    decideCandidate selectedEnvironment selected =
      case firstRefuted checks of
        Just rejectedDetails -> CandidateRefuted rejectedDetails
        Nothing -> case blockers of
          _ : _ -> CandidateHeld blockers fallback
          [] -> case returnType of
            Just selectedReturn
              | allProved checks -> CandidateAccepted selectedReturn
            _ -> CandidateRefuted fallback
      where
        candidate = selectedStructuralCandidate selected
        context = selectedTypingContext selected
        captures = selectedCaptures selected
        checks =
          [ checkCapture index captureSource result
          | (index, ((_, captureSource, _), result)) <- zip [0 ..]
              (zip (structuralCandidateCaptures candidate) captures)
          ]
        checkCapture index captureSource result =
          case (actual, expected) of
            (Just actualValue, Just expectedValue) ->
              case decideValueSubfederation actualValue expectedValue of
                DecisionProved () -> Right True
                DecisionRefuted -> Left (rejectionDetails index captureSource
                  (Just expectedValue) (Just actualValue) TypedHoleMismatch)
                DecisionUndecidable -> Right False
            _ -> Right False
          where
            expected = expectedHole selectedEnvironment candidate context index
            actual = captureActual result
        firstRefuted [] = Nothing
        firstRefuted (Left detailsValue : _) = Just detailsValue
        firstRefuted (_ : remaining) = firstRefuted remaining
        allProved = all proved
        proved (Right True) = True
        proved _ = False
        blockers = concat
          [ missingCaptureBlockers index kind result
          | (index, (kind, _, _), result) <- zip3 [0 ..]
              (structuralCandidateCaptures candidate) captures
          ] <> returnBlockers
        missingCaptureBlockers index kind result =
          expectedBlockers <> actualBlockers
          where
            expectedBlockers = case expectedHole selectedEnvironment
                candidate context index of
              Just _ -> []
              Nothing -> case kind of
                StringExpressionCapture (ValueString target) ->
                  [target]
                _ -> []
            actualBlockers = case captureActual result of
              Just _ -> []
              Nothing -> [rewriteResultExpression result]
        captureActual result = rewriteResultType result <|> lexicalValue
          where
            lexicalValue = case rewriteResultExpression result of
              IdentifierReference (SimpleIdentifierString name) ->
                either (const Nothing) Just (asciiStringValue name)
              _ -> Nothing
        returnType = candidateReturn selectedEnvironment candidate context
        returnBlockers = case returnType of
          Just _ -> []
          Nothing -> [syntaxRuleCodomain (rewriteRule
            (structuralCandidateRule candidate))]
        fallback = rejectionDetails 0
          (templateSelectionWhole (structuralCandidateSelection candidate))
          Nothing Nothing TypedHoleMismatch
        rejectionDetails index captureSource expected actual reason =
          CandidateRejectionDetails
          { candidateRejectionRule = structuralCandidateRule candidate
          , candidateRejectionBranch = rewriteRuleBranch
              (structuralCandidateRule candidate)
          , candidateRejectionCaptureIndex = index
          , candidateRejectionSource = captureSource
          , candidateRejectionExpected = expected
          , candidateRejectionActual = actual
          , candidateRejectionContext = context
          , candidateRejectionReason = reason
          }
    blockerResolved selectedEnvironment blocker =
      case contextClassify selectedEnvironment
          [StringExpressionCapture (ValueString blocker)] of
        [(_, Just _)] -> True
        _ -> False
    prepareCandidate _ selected =
      let candidate = selectedStructuralCandidate selected
          compiled = structuralCandidateRule candidate
      in prepareSelectedSyntaxMatch compiled
          (structuralCandidateMatch candidate)
    expandCandidate selectedEnvironment prepared = do
      pure (postRewriteExpansion
        (declaredExtent selectedEnvironment)
        (preparedExpansionExpression prepared)
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
