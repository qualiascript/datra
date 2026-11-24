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
  :: ( [(DeclarativeCapture, Expression)]
       -> DeclarativeCapture
       -> Expression
       -> Maybe Expression
     )
  -> (CandidateTypingContext syntaxType -> Int -> Maybe syntaxType)
  -> (CandidateTypingContext syntaxType -> Maybe syntaxType)
  -> (syntaxType -> syntaxType -> Bool)
  -> StructuralCandidate syntaxType
  -> CandidateFrame syntaxType
  -> CandidateFrameProgress syntaxType
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
            Nothing -> case extent of
              WholeCaptureExtent -> checkTerminalCapture frame
              ProperCaptureExtent ->
                CandidateFrameNeedsChild frame captureIndex kind source
            Just result -> checkResult frame result
      where
        captures = structuralCandidateCaptures candidate
        captureIndex = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        results = candidateFrameResults frame
        (kind, source, extent) = captures !! captureIndex
    -- A whole-extent capture cannot become a child without revisiting the
    -- same rewrite locus. Its contract must prepare it directly. Proper
    -- subextents always use the ordinary child scheduler, including atoms.
    checkTerminalCapture frame =
      case prepareCapture completed kind source of
        Nothing -> CandidateFrameRejected
          (rejectionDetails RequiredChildExhausted expected Nothing frame)
        Just preparedExpression ->
          acceptPreparedCapture frame
            RewriteResult
              { rewriteResultExpression = source
              , rewriteResultType = expected
              , rewriteResultSelection = Nothing
              }
            preparedExpression
      where
        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index
        captures = structuralCandidateCaptures candidate
        (kind, source, _) = captures !! index
        completed = completedCaptures frame index captures
    checkResult frame result = case typedResult of
      Left rejection -> rejection
      Right structurallyTyped -> case prepared of
        Just preparedExpression ->
          acceptPreparedCapture frame result preparedExpression
        Nothing
          | structurallyTyped -> acceptPreparedCapture frame result
              (rewriteResultExpression result)
          | otherwise -> CandidateFrameRejected
              (rejectionDetails RequiredChildExhausted expected Nothing frame)
      where
        prepared = prepareCapture completed kind
          (rewriteResultExpression result)
        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index
        captures = structuralCandidateCaptures
          candidate
        (kind, _, _) = captures !! index
        completed = completedCaptures frame index captures
        typedResult = case
            (requiresTypedResult kind result, expected, rewriteResultType result) of
          (False, _, _) -> Right False
          (True, Just wanted, Just actual)
            | compatible actual wanted -> Right True
            | otherwise -> Left (CandidateFrameRejected
                (rejectionDetails TypedHoleMismatch
                  (Just wanted) (Just actual) frame))
          (True, Just wanted, Nothing) -> Left (CandidateFrameRejected
            (rejectionDetails RequiredChildExhausted
              (Just wanted) Nothing frame))
          _ -> Right False

    acceptPreparedCapture frame result preparedExpression = advance frame
          { candidateFrameNextCapture = index + 1
          , candidateFrameTypingContext = context
              { candidateTypingInputs = maybe
                  (candidateTypingInputs context)
                  (\selected -> Map.insert index selected
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
          , candidateFrameResults = Map.insert index result
              (candidateFrameResults frame)
          }
      where
        index = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        expected = expectedHole context index

    completedCaptures frame index captures =
      [ (previousKind, preparedExpression)
      | previousIndex <- [0 .. index - 1]
      , let (previousKind, _, _) = captures !! previousIndex
      , Just preparedExpression <- [Map.lookup previousIndex
          (candidateFramePreparedCaptures frame)]
      ]

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
          (_, captured, _) : _ -> captured
          [] -> templateSelectionWhole
            (structuralCandidateSelection candidate)

compileRewriteRule :: SyntaxRule -> RewriteRule syntaxType
compileRewriteRule rule = RewriteRule
  { rewriteRule = rule
  , rewriteRuleBranch = 0
  , rewriteRuleEvaluation = Nothing
  , rewriteRuleHoleFamilies =
      map (const Nothing) (syntaxRuleCaptures rule)
  , rewriteRuleSyntaxInsertion = Nothing
  , rewriteRuleReturnType = Nothing
  }

enumerateRuleStructuralCandidates
  :: RewriteRule syntaxType
  -> Expression
  -> [StructuralCandidate syntaxType]
enumerateRuleStructuralCandidates compiled expressionValue =
  [ StructuralCandidate
      { structuralCandidateRule = compiled
      , structuralCandidateBranch = rewriteRuleBranch compiled
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
