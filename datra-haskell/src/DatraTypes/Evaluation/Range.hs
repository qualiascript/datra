{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Checked range construction and canonicalization.
module Evaluation.Range
  ( boundedRangeValue
  , openPlusRangeValue
  , openMinusRangeValue
  , interpretedRangeValue
  , canonicalizeRanges
  , concatenateRangeCapability
  ) where

import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import DatraLanguage.Diagnostics.Interpreter
  ( InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Construction (mapFromInsertion)
import Evaluation.Numerical
  ( requireExplicit
  , requireRangeUpperBoundary
  )
import Evaluation.Value
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand
  ( someSuperEllipsis
  , withSomeSuperEllipsis
  )
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( SuperEllipsisRank
  , SuperEllipsisTarget
  , superEllipsisTargetRank
  )
import SuperEllipsisRange qualified as Range

boundedRangeValue
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
boundedRangeValue lowerValue upperValue = do
  lower <- requireExplicit LeftOperand lowerValue
  upper <- requireRangeUpperBoundary RightOperand upperValue
  makeBoundedRange lower upper

openPlusRangeValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
openPlusRangeValue value = do
  endpoint <- requireExplicit LeftOperand value
  makeRange endpoint Range.PlusSign

openMinusRangeValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
openMinusRangeValue value = do
  endpoint <- requireExplicit LeftOperand value
  makeRange endpoint Range.MinusSign

makeBoundedRange
  :: EvaluatedExplicit
  -> (Natural, Ordinal)
  -> Either InterpretingError InterpretedValue
makeBoundedRange lower (upperLevel, upperOrdinal) =
  let (lowerLevel, lowerOrdinal) = explicitOrdinal lower
  in makeRangeAt
      (max lowerLevel upperLevel)
      lowerOrdinal
      (Range.GivenTarget upperOrdinal)

makeRange
  :: EvaluatedExplicit
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError InterpretedValue
makeRange endpoint target =
  let (level, ordinalValue) = explicitOrdinal endpoint
  in makeRangeAt level ordinalValue target

makeRangeAt
  :: Natural
  -> Ordinal
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError InterpretedValue
makeRangeAt level start target =
  interpretedRangeValue <$> makeEvaluatedRangeAt level start target

makeEvaluatedRangeAt
  :: Natural
  -> Ordinal
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError EvaluatedRange
makeEvaluatedRangeAt level start target =
  withRank level $ \valueRank ->
    case Range.superEllipsisRangeEither valueRank start target $ \valueRange ->
        EvaluatedRange level valueRange of
      Left rejection -> Left (RangeConstructionRejected rejection)
      Right value -> Right value

interpretedRangeValue :: EvaluatedRange -> InterpretedValue
interpretedRangeValue evaluatedRange =
  InterpretedValue
    (RangeForm evaluatedRange)
    (ValidInsertion insertion)
    (mapFromInsertion insertion [canonical])
    canonical
  where
    insertion = rangeInsertion evaluatedRange
    canonical = CanonicalRange (rangeDescription evaluatedRange)

canonicalizeRanges
  :: [EvaluatedRange]
  -> Either InterpretingError [EvaluatedRange]
canonicalizeRanges [] = Right []
canonicalizeRanges (firstRange : rest) = go [firstRange] rest
  where
    go canonical [] = Right canonical
    go [] remaining = canonicalizeRanges remaining
    go canonical nextRanges@(nextRange : remaining) =
      case reverse canonical of
        [] -> go [] nextRanges
        previousRange : reversedPrefix ->
          case analyzeRangePair previousRange nextRange of
            Range.RangeConcatCanonical description -> do
              merged <-
                makeEvaluatedRangeAt
                  (canonicalRangeLevel
                    previousRange nextRange description)
                  (Range.describedRangeStart description)
                  (Range.describedRangeTarget description)
              go (reverse reversedPrefix <> [merged]) remaining
            _ -> go (canonical <> [nextRange]) remaining

canonicalRangeLevel
  :: EvaluatedRange
  -> EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
  -> Natural
canonicalRangeLevel previousRange nextRange description
  | Range.describedRangeRankLimit description
      == Range.describedRangeRankLimit (rangeDescription previousRange) =
      evaluatedRangeLevel previousRange
  | otherwise = evaluatedRangeLevel nextRange

concatenateRangeCapability :: [EvaluatedRange] -> InsertionCapability
concatenateRangeCapability [] = NoInsertion
concatenateRangeCapability ranges =
  case Range.validateSuperEllipsisRangeDescriptions
      (map rangeDescription ranges) of
    Left rejection -> RejectedInsertion rejection
    Right () ->
      ValidInsertion
        (foldl1
          appendSomeSuperEllipsisInsertion
          (map rangeInsertion ranges))

analyzeRangePair
  :: EvaluatedRange
  -> EvaluatedRange
  -> Range.SuperEllipsisRangeConcatAnalysis
analyzeRangePair firstRange secondRange =
  Range.analyzeSuperEllipsisRangeDescriptions
    (rangeDescription firstRange)
    (rangeDescription secondRange)

withRank
  :: Natural
  -> (forall (target :: Type).
       SuperEllipsisTarget target
       => SuperEllipsisRank target
       -> result)
  -> result
withRank level useRank =
  withSomeSuperEllipsis (someSuperEllipsis level) $
    \(_ :: StableConfederalData target) ->
      useRank (superEllipsisTargetRank @target)
