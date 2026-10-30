module SyntaxRewriting.Candidates
  ( compileRewriteRule
  , compileDependentRewriteRule
  , enumerateRuleStructuralCandidates
  , initialCandidateFrame
  , advanceCandidateFrameWith
  , candidateFrameRequiresTypedChild
  , structuralCandidateMatch
  ) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.DependentDeclaration (DependentDeclaration)
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , syntaxTemplateLiteralPrefix
  )
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import DatraTypes (InterpretedValue)
import SyntaxRewriting.Types
  ( CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejectionDetails (..)
  , CandidateRejectionReason (..)
  , CandidateTypingContext (..)
  , RewriteDependency (..)
  , RewriteNodeId
  , RewriteResult (..)
  , RewriteRule (..)
  , StructuralCandidate (..)
  )
import SyntaxTemplateMatching
  ( SyntaxMatch (..)
  , StructuralSyntaxMatch (..)
  , enumerateSyntaxRuleSelections
  )
import SyntaxTemplateProjection
  ( applicationFrom
  , applicationPhrase
  , literalExpression
  , matchesLiteral
  )

initialCandidateFrame :: StructuralCandidate -> CandidateFrame
initialCandidateFrame candidate = CandidateFrame
  { candidateFrameCandidate = candidate
  , candidateFrameNextCapture = 0
  , candidateFrameTypingContext = CandidateTypingContext
      { candidateTypingInputs = Map.empty
      , candidateTypingExpectedHoles = Map.empty
      , candidateTypingReturnType = Nothing
      }
  , candidateFrameChildren = Map.empty
  , candidateFramePreparedCaptures = Map.empty
  }

candidateFrameRequiresTypedChild :: CandidateFrame -> Bool
candidateFrameRequiresTypedChild frame = case drop
    (candidateFrameNextCapture frame)
    (structuralCandidateCaptures (candidateFrameCandidate frame)) of
  (ValueSyntaxHole {}, _) : _ -> True
  _ -> False

-- | Continue one candidate from its stored capture cursor.  The callbacks are
-- the existing Datra typing operations: expected-hole instantiation, result
-- type instantiation, finalized-node lookup, and subfederation checking.
-- Completed captures are retained in the returned frame and never revisited.
advanceCandidateFrameWith
  :: ( [(SyntaxHoleKind Expression, Expression)]
       -> SyntaxHoleKind Expression
       -> Expression
       -> Maybe Expression
     )
  -> (CandidateTypingContext -> Int -> Maybe InterpretedValue)
  -> (CandidateTypingContext -> Maybe InterpretedValue)
  -> (RewriteNodeId -> Maybe RewriteResult)
  -> (InterpretedValue -> InterpretedValue -> Bool)
  -> CandidateFrame
  -> CandidateFrameProgress
advanceCandidateFrameWith prepareCapture expectedHole candidateReturn
    lookupResult compatible =
  advance
  where
    advance frame
      | captureIndex >= length captures =
          case candidateReturn context of
            Just resultType -> CandidateFrameAccepted
              context { candidateTypingReturnType = Just resultType }
              [ preparedResult
              | index <- [0 .. length captures - 1]
              , Just child <- [Map.lookup index children]
              , Just childResult <- [lookupResult child]
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
          case Map.lookup captureIndex children of
            Nothing -> CandidateFrameNeedsChild captureIndex kind source
            Just child -> case lookupResult child of
              Nothing -> CandidateFrameBlocked
                (Set.singleton (RewriteNodeResult child))
              Just result -> checkResult frame result
      where
        candidate = candidateFrameCandidate frame
        captures = structuralCandidateCaptures candidate
        captureIndex = candidateFrameNextCapture frame
        context = candidateFrameTypingContext frame
        children = candidateFrameChildren frame
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
          (candidateFrameCandidate frame)
        (kind, _) = captures !! index
        completed =
          [ (previousKind, preparedExpression)
          | previousIndex <- [0 .. index - 1]
          , let (previousKind, _) = captures !! previousIndex
          , Just preparedExpression <- [Map.lookup previousIndex
              (candidateFramePreparedCaptures frame)]
          ]

        requiresTypedResult ValueSyntaxHole {} _ = True
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
        candidate = candidateFrameCandidate frame
        captures = structuralCandidateCaptures candidate
        index = candidateFrameNextCapture frame
        source = case drop index captures of
          (_, captured) : _ -> captured
          [] -> templateSelectionWhole
            (structuralCandidateSelection candidate)

compileRewriteRule :: SyntaxRule -> RewriteRule
compileRewriteRule rule = RewriteRule
  { rewriteRule = rule
  , rewriteRuleDeclaration = Nothing
  , rewriteRuleBranch = 0
  , rewriteRuleLiteralPrefix = syntaxTemplateLiteralPrefix rule
  , rewriteRuleLiterals = Set.fromList
      [ literal | SyntaxLiteral literal <- pieces ]
  , rewriteRuleEvaluation = Nothing
  , rewriteRuleHoleFamilies =
      [ Nothing | SyntaxHole _ <- pieces ]
  , rewriteRuleSyntaxInsertion = Nothing
  , rewriteRuleRuntimeInsertion = Nothing
  , rewriteRuleReturnType = Nothing
  }
  where
    pieces = syntaxTemplatePieces (syntaxTemplate rule)

compileDependentRewriteRule
  :: DependentDeclaration Expression
  -> Int
  -> SyntaxRule
  -> RewriteRule
compileDependentRewriteRule declaration branch rule =
  (compileRewriteRule rule)
    { rewriteRuleDeclaration = Just declaration
    , rewriteRuleBranch = branch
    }

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
      (concatMap (candidateProjections compiled) projections)
  , matched <- enumerateSyntaxRuleSelections rule expressionValue
  ]
  where
    rule = rewriteRule compiled

candidateProjections :: RewriteRule -> Expression -> [Expression]
candidateProjections compiled expressionValue =
  blockTemplateProjections compiled expressionValue
    <> [expressionValue]

blockTemplateProjections :: RewriteRule -> Expression -> [Expression]
blockTemplateProjections compiled expressionValue = do
  (prefix, delimiter) <- maybeToList
    (blockTemplateShape (syntaxTemplatePieces
      (syntaxTemplate (rewriteRule compiled))))
  let phrase = applicationPhrase expressionValue
  if and (zipWith matchesLiteral prefix phrase)
      && length phrase >= length prefix
    then do
      let afterPrefix = drop (length prefix) phrase
          (writtenBlockMembers, delimiterAndResult) =
            break (matchesLiteral delimiter) afterPrefix
      _ : resultMembers <- pure delimiterAndResult
      if null resultMembers
        then []
        else pure (applicationFrom
          ( map literalExpression prefix
            <> [ AtlasMap writtenBlockMembers
               , literalExpression delimiter
               , applicationFrom resultMembers
               ]
          ))
    else []

blockTemplateShape
  :: [SyntaxPiece Expression]
  -> Maybe ([String], String)
blockTemplateShape pieces = case break isBlockHole pieces of
  (prefix, SyntaxHole BlockSyntaxHole {}
      : SyntaxLiteral delimiter
      : [SyntaxHole ExpressionSyntaxHole {}]) ->
    (, delimiter) <$> traverse literal prefix
  _ -> Nothing
  where
    isBlockHole (SyntaxHole BlockSyntaxHole {}) = True
    isBlockHole _ = False
    literal (SyntaxLiteral value) = Just value
    literal _ = Nothing

maybeToList :: Maybe value -> [value]
maybeToList Nothing = []
maybeToList (Just value) = [value]

structuralCandidateMatch :: StructuralCandidate -> SyntaxMatch
structuralCandidateMatch candidate = SyntaxMatch
  { syntaxMatchRule = rewriteRule (structuralCandidateRule candidate)
  , syntaxMatchSelection = structuralCandidateSelection candidate
  , syntaxMatchRemaining = structuralCandidateRemaining candidate
  }
