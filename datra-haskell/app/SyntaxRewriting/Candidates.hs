module SyntaxRewriting.Candidates
  ( compileRewriteRule
  , enumerateRuleStructuralCandidates
  , initialCandidateFrame
  , advanceCandidateFrameWith
  , structuralCandidateMatch
  ) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.StringExpression
  ( StringExpression (..)
  , StringTemplatePart (..)
  , TemplateSelection (..)
  )
import StringInterpolation
  ( SyntaxRule (..) )
import Data.Map.Strict qualified as Map
import DatraTypes (InterpretedValue)
import SyntaxRewriting.Types
  ( CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejectionDetails (..)
  , CandidateRejectionReason (..)
  , CandidateTypingContext (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , StructuralCandidate (..)
  )
import StringInterpolation.Matching
  ( SyntaxMatch (..)
  , StructuralSyntaxMatch (..)
  , enumerateSyntaxRuleSelections
  )
import Parsing (stringInterpolationParser)

initialCandidateFrame :: StructuralCandidate -> CandidateFrame
initialCandidateFrame _ = CandidateFrame
  { candidateFrameNextCapture = 0
  , candidateFrameTypingContext = CandidateTypingContext
      { candidateTypingInputs = Map.empty
      , candidateTypingExpectedHoles = Map.empty
      , candidateTypingReturnType = Nothing
      }
  , candidateFrameResults = Map.empty
  , candidateFramePreparedCaptures = Map.empty
  }

-- | Continue one candidate from its stored capture cursor.  The callbacks are
-- the existing Datra typing operations: expected-hole instantiation, result
-- type instantiation, finalized-node lookup, and subfederation checking.
-- Completed captures are retained in the returned frame and never revisited.
advanceCandidateFrameWith
  :: ( [(StringExpression Expression, Expression)]
       -> StringExpression Expression
       -> Expression
       -> Maybe Expression
     )
  -> (CandidateTypingContext -> Int -> Maybe InterpretedValue)
  -> (CandidateTypingContext -> Maybe InterpretedValue)
  -> (InterpretedValue -> InterpretedValue -> Bool)
  -> StructuralCandidate
  -> CandidateFrame
  -> CandidateFrameProgress
advanceCandidateFrameWith prepareCapture expectedHole candidateReturn
    compatible candidate =
  advance
  where
    advance frame
      | captureIndex >= length captures =
          case candidateReturn context of
            Just resultType -> CandidateFrameAccepted
              context { candidateTypingReturnType = Just resultType }
              [ preparedResult
              | index <- [0 .. length captures - 1]
              , Just childResult <- [Map.lookup index results]
              , let preparedResult = childResult
                      { rewriteResultExpression = Map.findWithDefault
                          (rewriteResultExpression childResult) index
                          (candidateFramePreparedCaptures frame)
                      }
              ]
              resultType
            Nothing -> CandidateFrameRejected
              (rejectionDetails CandidateReturnMismatch Nothing Nothing frame)
      | otherwise =
          case Map.lookup captureIndex results of
            Nothing -> CandidateFrameNeedsChild frame captureIndex kind source
            Just result -> checkResult frame result
      where
        captures = structuralCandidateCaptures candidate
        captureIndex = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        results = candidateFrameResults frame
        (kind, source) = captures !! captureIndex
    checkResult frame result = case prepared of
      Nothing -> CandidateFrameRejected
        (rejectionDetails RequiredChildExhausted expected Nothing frame)
      Just preparedExpression ->
        case (requiresTypedResult kind result, expected, rewriteResultType result) of
          (False, _, _) -> advanceFrame preparedExpression
          (True, Just wanted, Just actual)
            | not (compatible actual wanted) -> CandidateFrameRejected
                (rejectionDetails TypedHoleMismatch
                  (Just wanted) (Just actual) frame)
          (True, Just wanted, Nothing) -> CandidateFrameRejected
            (rejectionDetails RequiredChildExhausted
              (Just wanted) Nothing frame)
          _ -> advanceFrame preparedExpression
      where
        prepared = prepareCapture completed kind
          (rewriteResultExpression result)
        advanceFrame preparedExpression = advance frame
          { candidateFrameNextCapture = index + 1
          , candidateFrameTypingContext = context
              { candidateTypingInputs = maybe
                  (candidateTypingInputs context)
                  (\actual -> Map.insert index actual
                    (candidateTypingInputs context))
                  (rewriteResultType result)
              , candidateTypingExpectedHoles = maybe
                  (candidateTypingExpectedHoles context)
                  (\wanted -> Map.insert index wanted
                    (candidateTypingExpectedHoles context))
                  expected
              }
          , candidateFramePreparedCaptures = Map.insert
              index preparedExpression
              (candidateFramePreparedCaptures frame)
          }
        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index
        captures = structuralCandidateCaptures
          candidate
        (kind, _) = captures !! index
        completed =
          [ (previousKind, preparedExpression)
          | previousIndex <- [0 .. index - 1]
          , let (previousKind, _) = captures !! previousIndex
          , Just preparedExpression <- [Map.lookup previousIndex
              (candidateFramePreparedCaptures frame)]
          ]

        requiresTypedResult ValueString {} _ = True
        requiresTypedResult StringLiteralString {} _ = True
        requiresTypedResult _ selected = case rewriteResultSelection selected of
          Just _ -> True
          Nothing -> False

    rejectionDetails reason expected actual frame =
      CandidateRejectionDetails
        { candidateRejectionRule = structuralCandidateRule candidate
        , candidateRejectionBranch = structuralCandidateBranch candidate
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
          (_, captured) : _ -> captured
          [] -> templateSelectionWhole
            (structuralCandidateSelection candidate)

compileRewriteRule :: SyntaxRule -> RewriteRule
compileRewriteRule rule = RewriteRule
  { rewriteRule = rule
  , rewriteRuleBranch = 0
  , rewriteRuleEvaluation = Nothing
  , rewriteRuleHoleFamilies =
      [ Nothing | StringTemplateInterpolation _ <- pieces ]
  , rewriteRuleSyntaxInsertion = Nothing
  , rewriteRuleReturnType = Nothing
  }
  where
    pieces = stringInterpolationTemplate rule

enumerateRuleStructuralCandidates
  :: RewriteRule
  -> [Expression]
  -> [StructuralCandidate]
enumerateRuleStructuralCandidates compiled projections =
  [ StructuralCandidate
      { structuralCandidateRule = compiled
      , structuralCandidateBranch = rewriteRuleBranch compiled
      , structuralCandidateProjection = projection
      , structuralCandidateSelection =
          structuralSyntaxMatchSelection matched
      , structuralCandidateCaptures =
          structuralSyntaxMatchCaptures matched
      , structuralCandidateRemaining =
          structuralSyntaxMatchRemaining matched
      }
  | (projection, expressionValue) <- zip [0 ..]
      projections
  , matched <- enumerateSyntaxRuleSelections
      stringInterpolationParser rule expressionValue
  ]
  where
    rule = rewriteRule compiled

structuralCandidateMatch :: StructuralCandidate -> SyntaxMatch
structuralCandidateMatch candidate = SyntaxMatch
  { syntaxMatchRule = rewriteRule (structuralCandidateRule candidate)
  , syntaxMatchSelection = structuralCandidateSelection candidate
  , syntaxMatchRemaining = structuralCandidateRemaining candidate
  }
