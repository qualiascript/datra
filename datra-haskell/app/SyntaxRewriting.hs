-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Application spines retain logical line breaks until a declaration has
-- selected the extent it wants to match.
module SyntaxRewriting
  ( RewriteLocus (..)
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
import DatraTypes
  ( Decision (..)
  , InterpretedValue
  , asciiStringValue
  , decideValueSubfederation
  )
import DatraTypes.Scope
  ( DeclarationLayerImportPolicy (..), Scope )
import Evaluation.Scope.Syntax
  ( ScopeSyntaxRule (..)
  , enterSyntaxScope
  , openSyntaxScope
  , predeclareSyntaxLets
  , publishSyntaxDeclaration
  , scopeSyntaxRules
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

type SyntaxEvaluator = Scope -> Expression -> Maybe InterpretedValue

scopeRewriteRules
  :: SyntaxEvaluator
  -> Scope
  -> [RuntimeRewriteRule]
scopeRewriteRules evaluate scope =
  [ (compileRewriteRule
        familyScope
        (scopeSyntaxRuleImportPolicy visible)
        (scopeSyntaxRuleLayer visible)
        (evaluate familyScope (syntaxRuleCodomain rule))
        rule)
      { rewriteRuleBranch = scopeSyntaxRuleBranch visible }
  | visible <- scopeSyntaxRules scope
  , let rule = scopeSyntaxRuleValue visible
        familyScope = scopeSyntaxRuleFamilyScope visible
  ]

-- | Rewrite one already-delimited expression with the same declaration
-- environment used by resource rewriting.  Canonical values cross this
-- boundary after rendering and parsing, so they must recover dependent
-- declaration invocations before closure collection inspects references.
rewriteStandaloneSyntax
  :: SyntaxEvaluator
  -> Scope
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandaloneSyntax evaluate scope =
  runRewriteExpression evaluate Nothing scope

rewriteResourceSyntax
  :: SyntaxEvaluator
  -> Scope
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntax evaluate scope raw =
  rewriteResourceSyntaxWithSpan evaluate Nothing scope raw

rewriteResourceSyntaxLocated
  :: SyntaxEvaluator
  -> Scope
  -> Located Expression
  -> Either SyntaxRewriteFailure (Located Expression)
rewriteResourceSyntaxLocated evaluate scope
    (Located sourceSpan raw) =
  Located sourceSpan <$> rewriteResourceSyntaxWithSpan
    evaluate (Just sourceSpan) scope raw

rewriteResourceSyntaxWithSpan
  :: SyntaxEvaluator
  -> Maybe SourceSpan
  -> Scope
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteResourceSyntaxWithSpan evaluate sourceSpan scope raw =
  -- OBSOLETE normalization seam: the rewrite stack must return the final tree
  -- instead of relying on this post-rewrite reshaping pass.
  normalizeExpression <$> runRewriteExpression evaluate sourceSpan scope raw

runRewriteExpression
  :: SyntaxEvaluator
  -> Maybe SourceSpan
  -> Scope
  -> Expression
  -> Either SyntaxRewriteFailure Expression
runRewriteExpression evaluate sourceSpan environment value = do
  (result, rejections) <- runStructuralCandidates
    evaluate sourceSpan environment value
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
  :: SyntaxEvaluator
  -> Maybe SourceSpan
  -> Scope
  -> Expression
  -> Either SyntaxRewriteFailure
      (RuntimeRewriteResult, [RuntimeCandidateRejection])
runStructuralCandidates evaluate sourceSpan environment source =
  runRewriteStack operations environment source
  where
    operations = RewriteStackOperations
      { stackExhausted = RewriteStackExhausted
      , stackEnumerateCandidates = structuralCandidatesFor evaluate
      , stackPostRewrite = \selectedEnvironment ->
          terminalFallback (declaredExtent evaluate selectedEnvironment)
      , stackPrepareStructuralCapture = prepareStructuralCapture
      , stackExpectedHole = expectedHole
      , stackCandidateReturn = candidateReturn
      , stackDecideCandidate = decideCandidate
      , stackBlockerResolved = blockerResolved
      , stackRewriteScope = rewriteScope evaluate
      , stackFinalizeOrdinary = finalizeOrdinary
      , stackPublishChild = publishChild
      , stackPrepareCandidate = prepareCandidate
      , stackExpandCandidate = expandCandidate
      , stackCandidateRejection = \_ details ->
          candidateRejectionAt
            sourceSpan details
      , stackStrictImportAmbiguity = \_ -> AmbiguousStrictSyntaxImport
      }
    finalizeOrdinary selectedContext rawExpression = case expressionValue of
      FunctionApplication _ Skip -> Left AmbiguousBareSkipApplication
      _ -> Right RewriteResult
        { rewriteResultExpression = expressionValue
        , rewriteResultType = evaluate selectedContext expressionValue
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

    expectedHole _ candidate context index =
      Map.lookup index (candidateTypingExpectedHoles context)
        <|> classified
      where
        classified = case drop index
            (structuralCandidateCaptures candidate) of
          (kind, _, _) : _ -> classifyCapture candidate kind
          [] -> Nothing
        classifyCapture selectedCandidate kind = case kind of
          StringExpressionCapture (ValueString target) ->
            evaluate
              (rewriteRuleFamilyScope
                (structuralCandidateRule selectedCandidate))
              target
          _ -> Nothing
    candidateReturn _ candidate _ =
      rewriteRuleReturnType compiled <|>
        evaluate (rewriteRuleFamilyScope compiled)
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
      case evaluate selectedEnvironment blocker of
        Just _ -> True
        Nothing -> False
    prepareCandidate _ selected =
      let candidate = selectedStructuralCandidate selected
          compiled = structuralCandidateRule candidate
      in prepareSelectedSyntaxMatch compiled
          (structuralCandidateMatch candidate)
    expandCandidate selectedEnvironment prepared = do
      pure (postRewriteExpansion
        (declaredExtent evaluate selectedEnvironment)
        (preparedExpansionExpression prepared)
        (preparedExpansionRemaining prepared))

rewriteScope :: SyntaxEvaluator -> Scope -> RewriteLocus -> Scope
rewriteScope evaluate environment locus = case locus of
  RewriteExpression expressionValue ->
    expressionScope environment expressionValue
  RewriteChild parent cursor child ->
    expressionScope (scopeAt cursor (childScopes parent)) child
  where
    childScopes expressionValue = case expressionValue of
      MaybeThen _ _ ->
        [ environment
        , enterSyntaxScope Nothing environment
        ]
      ScopedExpression source _ ->
        [ environment
        , enterSyntaxScope Nothing
            (openSyntaxScope evaluate PreferentialImport environment source)
        ]
      WithScopes sources _ ->
        replicate (length sources) environment <>
          [ enterSyntaxScope Nothing
              (foldl
                (openSyntaxScope evaluate StrictImport)
                environment
                sources)
          ]
      _ -> map (const environment)
        (expressionChildren expressionValue)

    scopeAt selected scopes = case drop selected scopes of
      selectedScope : _ -> selectedScope
      [] -> environment

    expressionScope selected expressionValue = case expressionValue of
      AtlasMap entries -> predeclareSyntaxLets entries selected
      Begin declarations result -> predeclareSyntaxLets
        (map DeclarationExpression declarations <> [result])
        (enterSyntaxScope Nothing selected)
      FunctionBody declarations result -> predeclareSyntaxLets
        (map DeclarationExpression declarations <> [result])
        (enterSyntaxScope Nothing selected)
      _ -> selected

publishChild
  :: Scope
  -> Expression
  -> Int
  -> RuntimeRewriteResult
  -> Either SyntaxRewriteFailure (Maybe Scope)
publishChild environment parent cursor result = Right $ case parent of
  AtlasMap {} -> publishSyntaxDeclaration entry environment
  MapSequence {} -> publishSyntaxDeclaration entry environment
  Begin declarations _
    | cursor < length declarations ->
        publishSyntaxDeclaration entry environment
  FunctionBody declarations _
    | cursor < length declarations ->
        publishSyntaxDeclaration entry environment
  _ -> Nothing
  where
    entry = rewriteResultExpression result

structuralCandidatesFor
  :: SyntaxEvaluator
  -> Scope
  -> Expression
  -> [RuntimeStructuralCandidate]
structuralCandidatesFor = declaredCandidatesFor

declaredExtent
  :: SyntaxEvaluator
  -> Scope
  -> Expression
  -> Maybe (Expression, [Expression])
declaredExtent evaluate environment value =
  case declaredCandidatesFor evaluate environment value of
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
  :: SyntaxEvaluator
  -> Scope
  -> Expression
  -> [RuntimeStructuralCandidate]
declaredCandidatesFor evaluate environment value =
    enumerate value (scopeRewriteRules evaluate environment) <> scopedCandidates
  where
    enumerate selectedValue = concatMap (\rule ->
      enumerateRuleStructuralCandidates rule selectedValue)
    scopedCandidates = case applicationSpine value of
      (ScopedExpression source body, arguments@(_ : _)) ->
        let scopedEnvironment = openSyntaxScope
              evaluate PreferentialImport environment source
            compiled = scopeRewriteRules evaluate scopedEnvironment
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue compiled
      (WithScopes sources body, arguments@(_ : _)) ->
        let scopedEnvironment = foldl
              (openSyntaxScope evaluate StrictImport) environment sources
            compiled = scopeRewriteRules evaluate scopedEnvironment
            scopedValue = applicationFrom (body : arguments)
        in enumerate scopedValue compiled
      _ -> []
