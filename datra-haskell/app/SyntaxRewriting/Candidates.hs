module SyntaxRewriting.Candidates
  ( compileRewriteRule
  , enumerateRuleStructuralCandidates
  , initialCandidateFrame
  , advanceCandidateFrameWith
  , structuralCandidateMatch
  ) where

import DatraLanguage.AST (Expression)
import StringExpression
  ( TemplateSelection (..) )
import StringInterpolation
  ( DeclarativeCapture
  , DeclarativeMatcherPlan (..)
  , LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , SyntaxRule (..)
  , syntaxRuleCaptures
  )
import Data.Map.Strict qualified as Map
import SyntaxRewriting.Types
  ( CaptureExtent (..)
  , CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejectionDetails (..)
  , CandidateRejectionReason (..)
  , CandidateTypingContext (..)
  , Compatibility (..)
  , CompatibilityConstraint (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , StructuralCandidate (..)
  )
import StringInterpolation.Matching
  ( SyntaxMatch (..)
  , DeclarativeMatch (..)
  , enumerateSyntaxRuleSelections
  )
import Parsing (expressionParser)

initialCandidateFrame
  :: StructuralCandidate syntaxType
  -> CandidateFrame syntaxType
initialCandidateFrame _ = CandidateFrame
  { candidateFrameNextCapture = 0
  , candidateFrameTypingContext = CandidateTypingContext
      { candidateTypingInputs = Map.empty
      , candidateTypingExpectedHoles = Map.empty
      , candidateTypingBlocked = []
      }
  , candidateFrameResults = Map.empty
  , candidateFramePreparedCaptures = Map.empty
  }

-- | Continue one candidate from its stored capture cursor.  The callbacks are
-- the existing Datra typing operations: expected-hole instantiation, result
-- type instantiation, finalized-node lookup, and subfederation checking.
-- Completed captures are retained in the returned frame and never revisited.
advanceCandidateFrameWith
  :: ( DeclarativeCapture
       -> Expression
       -> Maybe Expression
     )
  -> (CandidateTypingContext syntaxType -> Int -> Maybe syntaxType)
  -> (CandidateTypingContext syntaxType -> syntaxType)
  -> (syntaxType -> syntaxType -> Compatibility)
  -> StructuralCandidate syntaxType
  -> CandidateFrame syntaxType
  -> CandidateFrameProgress syntaxType
advanceCandidateFrameWith prepareCapture expectedHole candidateReturn
    compatible candidate =
  advance
  where
    advance frame
      | captureIndex >= length captures =
          CandidateFrameComplete
            context
            [ preparedResult
            | index <- [0 .. length captures - 1]
            , Just childResult <- [Map.lookup index results]
            , let preparedResult = childResult
                    { rewriteResultExpression = Map.findWithDefault
                        (rewriteResultExpression childResult) index
                        (candidateFramePreparedCaptures frame)
                    }
            ]
            (candidateReturn context)
      | otherwise =
          case Map.lookup captureIndex results of
            Nothing -> case extent of
              WholeCaptureExtent ->
                CandidateFrameNeedsTerminal frame captureIndex kind source
              ProperCaptureExtent ->
                CandidateFrameNeedsChild frame captureIndex kind source
            Just result -> checkResult frame result
      where
        captures = structuralCandidateCaptures candidate
        captureIndex = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        results = candidateFrameResults frame
        (kind, source, extent) = captures !! captureIndex
    checkResult frame result = check
      where
        check = case expected of
          Just wanted -> case compatible (rewriteResultType result) wanted of
            CompatibilityProved -> acceptSelectedCapture frame [] result
            CompatibilityUndecidable -> acceptSelectedCapture frame
              [CompatibilityConstraint index
                (rewriteResultType result) wanted]
              result
            CompatibilityRefuted -> CandidateFrameRejected
              (rejectionDetails TypedHoleMismatch
                (Just wanted) (Just (rewriteResultType result)) frame)
          Nothing -> prepareStructuralResult frame result

        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index
        captures = structuralCandidateCaptures
          candidate
        (kind, _, _) = captures !! index
        acceptSelectedCapture selectedFrame deferred selectedResult =
          acceptPreparedCapture selectedFrame deferred selectedResult
            (rewriteResultExpression selectedResult)

        prepareStructuralResult selectedFrame selectedResult =
          case prepareCapture kind
              (rewriteResultExpression selectedResult) of
            Just preparedExpression -> acceptPreparedCapture
              selectedFrame [] selectedResult preparedExpression
            Nothing -> CandidateFrameRejected
              (rejectionDetails RequiredChildExhausted expected Nothing
                selectedFrame)

    acceptPreparedCapture frame deferred result preparedExpression = advance frame
          { candidateFrameNextCapture = index + 1
          , candidateFrameTypingContext = context
              { candidateTypingInputs = Map.insert index
                  (rewriteResultType result)
                  (candidateTypingInputs context)
              , candidateTypingExpectedHoles = maybe
                  (candidateTypingExpectedHoles context)
                  (\wanted -> Map.insert index wanted
                    (candidateTypingExpectedHoles context))
                  expected
              , candidateTypingBlocked =
                  candidateTypingBlocked context <> deferred
              }
          , candidateFramePreparedCaptures = Map.insert
              index preparedExpression
              (candidateFramePreparedCaptures frame)
          , candidateFrameResults = Map.insert index result
              (candidateFrameResults frame)
          }
      where
        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index

    rejectionDetails reason expected actual frame =
      CandidateRejectionDetails
        { candidateRejectionRule = structuralCandidateRule candidate
        , candidateRejectionBranch = rewriteRuleBranch
            (structuralCandidateRule candidate)
        , candidateRejectionCaptureIndex = index
        , candidateRejectionSource = source
        , candidateRejectionExpected = expected
        , candidateRejectionActual = actual
        , candidateRejectionContext = candidateFrameTypingContext frame
        , candidateRejectionReason = reason
        }
      where
        captures = structuralCandidateCaptures candidate
        index = candidateFrameNextCapture frame
        source = case drop index captures of
          (_, captured, _) : _ -> captured
          [] -> templateSelectionWhole
            (structuralCandidateSelection candidate)

compileRewriteRule :: syntaxType -> SyntaxRule -> RewriteRule syntaxType
compileRewriteRule returnType rule = RewriteRule
  { rewriteRule = rule
  , rewriteRuleBranch = 0
  , rewriteRuleSyntaxInsertion = Nothing
  , rewriteRuleReturnType = returnType
  }

enumerateRuleStructuralCandidates
  :: RewriteRule syntaxType
  -> Expression
  -> [StructuralCandidate syntaxType]
enumerateRuleStructuralCandidates compiled expressionValue =
  [ StructuralCandidate
      { structuralCandidateRule = compiled
      , structuralCandidateSelection =
          declarativeMatchSelection matched
      , structuralCandidateCaptures =
          zipWith
            (\(kind, captured) extent -> (kind, captured, extent))
            (declarativeMatchCaptures matched)
            (ruleCaptureExtents rule)
      , structuralCandidateRemaining =
          declarativeMatchRemaining matched
      }
  | matched <- enumerateSyntaxRuleSelections
      expressionParser rule expressionValue
  ]
  where
    rule = rewriteRule compiled

ruleCaptureExtents :: SyntaxRule -> [CaptureExtent]
ruleCaptureExtents rule = case declarativeMatcherPlan rule of
  IdentifierApplicationMatcher {} ->
    replicate (length (syntaxRuleCaptures rule)) ProperCaptureExtent
  LiteralExpressionMatcher (LiteralExpressionPattern parts) -> case parts of
    [LiteralExpressionPatternCapture _] -> [WholeCaptureExtent]
    _ ->
      [ ProperCaptureExtent
      | LiteralExpressionPatternCapture _ <- parts
      ]

structuralCandidateMatch
  :: StructuralCandidate syntaxType
  -> SyntaxMatch
structuralCandidateMatch candidate = SyntaxMatch
  { syntaxMatchRule = rewriteRule (structuralCandidateRule candidate)
  , syntaxMatchSelection = structuralCandidateSelection candidate
  , syntaxMatchRemaining = structuralCandidateRemaining candidate
  }
