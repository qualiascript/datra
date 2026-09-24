{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Checked range construction and canonicalization.
module Evaluation.Range
  ( boundedRangeValue
  , openPlusRangeValue
  , openMinusRangeValue
  , naturalRangeValue
  , naturalRangeUpwardsValue
  , valuedNaturalRangeValue
  , valuedNaturalRangeUpwardsValue
  , naturalTypeValue
  , integerRangeValue
  , integerRangeUpwardsValue
  , integerRangeDownwardsValue
  , valuedIntegerRangeValue
  , valuedIntegerRangeUpwardsValue
  , valuedIntegerRangeDownwardsValue
  , integerTypeValue
  , interpretedRangeValue
  , makeEvaluatedRangeAt
  , canonicalizeRanges
  , concatenateRangeCapability
  ) where

import Data.Kind (Type)
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression
      ( PrimitiveAtlasMapFederation
      )
  )
import DatraOrdinal (Ordinal, finiteOrdinal)
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Construction (mapFromInsertion)
import Evaluation.Numerical
  ( requireExplicit
  , requireRangeUpperBoundary
  )
import Evaluation.Value
import Numeric.Natural (Natural)
import EllipsisNatural qualified
import EllipsisInteger qualified
import NaturalRange qualified
import NaturalType qualified
import ValuedNaturalRange qualified
import IntegerRange qualified
import IntegerType qualified
import ValuedIntegerRange qualified
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
import SuperEllipsisInsertion (eraseSuperEllipsisInsertion)

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

naturalRangeValue :: Natural -> Natural -> Either InterpretingError InterpretedValue
naturalRangeValue start target =
  case EllipsisNatural.ellipsisNatural start $ \origin ->
      EllipsisNatural.ellipsisNatural target $ \destination ->
        NaturalRange.naturalRange origin destination interpretedNaturalRangeValue
    of
      Just (Just (Just value)) -> Right value
      _ -> interpretedNaturalRangeFallback
        start
        (NaturalRange.FiniteNaturalTarget target)

naturalRangeUpwardsValue
  :: Natural
  -> Either InterpretingError InterpretedValue
naturalRangeUpwardsValue start =
  case EllipsisNatural.ellipsisNatural start $ \origin ->
      NaturalRange.naturalRange
        origin NaturalRange.upwards interpretedNaturalRangeValue
    of
      Just (Just value) -> Right value
      _ -> interpretedNaturalRangeFallback start NaturalRange.UpwardsTarget

valuedNaturalRangeValue
  :: Natural
  -> Natural
  -> Either InterpretingError InterpretedValue
valuedNaturalRangeValue start target =
  EllipsisNatural.ellipsisNaturalTotal start $ \origin ->
    EllipsisNatural.ellipsisNaturalTotal target $ \destination ->
      case ValuedNaturalRange.valuedNaturalRangeEither
          origin destination
          (interpretedValuedNaturalRangeValue
            (ValuedNaturalRangeSemantics
              start (NaturalRange.FiniteNaturalTarget target))) of
        Left rejection -> Left (RangeConstructionRejected rejection)
        Right value -> Right value

valuedNaturalRangeUpwardsValue
  :: Natural
  -> Either InterpretingError InterpretedValue
valuedNaturalRangeUpwardsValue start =
  EllipsisNatural.ellipsisNaturalTotal start $ \origin ->
    case ValuedNaturalRange.valuedNaturalRangeEither
        origin NaturalRange.upwards
        (interpretedValuedNaturalRangeValue
          (ValuedNaturalRangeSemantics start NaturalRange.UpwardsTarget)) of
      Left rejection -> Left (RangeConstructionRejected rejection)
      Right value -> Right value

naturalTypeValue :: Either InterpretingError InterpretedValue
naturalTypeValue =
  case NaturalType.naturalTypeEither
      (interpretedValuedNaturalRangeValue NaturalTypeSemantics) of
    Left rejection -> Left (RangeConstructionRejected rejection)
    Right value -> Right value

integerRangeValue
  :: Integer -> Integer -> Either InterpretingError InterpretedValue
integerRangeValue start target =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    EllipsisInteger.ellipsisInteger target $ \destination ->
      case IntegerRange.integerRange
          origin destination interpretedIntegerRangeValue of
        Just value -> Right value
        Nothing -> Left (ExpectedFiniteIntegerOperand
          LeftOperand IntegerValueKind)

integerRangeUpwardsValue
  :: Integer -> Either InterpretingError InterpretedValue
integerRangeUpwardsValue start =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    case IntegerRange.integerRange
        origin IntegerRange.upwards interpretedIntegerRangeValue of
      Just value -> Right value
      Nothing -> Left (ExpectedFiniteIntegerOperand
        LeftOperand IntegerValueKind)

integerRangeDownwardsValue
  :: Integer -> Either InterpretingError InterpretedValue
integerRangeDownwardsValue start =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    case IntegerRange.integerRange
        origin IntegerRange.downwards interpretedIntegerRangeValue of
      Just value -> Right value
      Nothing -> Left (ExpectedFiniteIntegerOperand
        LeftOperand IntegerValueKind)

valuedIntegerRangeValue
  :: Integer -> Integer -> Either InterpretingError InterpretedValue
valuedIntegerRangeValue start target =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    EllipsisInteger.ellipsisInteger target $ \destination ->
      case ValuedIntegerRange.valuedIntegerRange
          origin destination
          (interpretedValuedIntegerRangeValue
            (ValuedIntegerRangeSemantics
              start (IntegerRange.FiniteIntegerTarget target))) of
        Just value -> Right value
        Nothing -> Left (ExpectedFiniteIntegerOperand
          LeftOperand IntegerValueKind)

valuedIntegerRangeUpwardsValue
  :: Integer -> Either InterpretingError InterpretedValue
valuedIntegerRangeUpwardsValue start =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    case ValuedIntegerRange.valuedIntegerRange
        origin IntegerRange.upwards
        (interpretedValuedIntegerRangeValue
          (ValuedIntegerRangeSemantics
            start IntegerRange.UpwardsIntegerTarget)) of
      Just value -> Right value
      Nothing -> Left (ExpectedFiniteIntegerOperand
        LeftOperand IntegerValueKind)

valuedIntegerRangeDownwardsValue
  :: Integer -> Either InterpretingError InterpretedValue
valuedIntegerRangeDownwardsValue start =
  EllipsisInteger.ellipsisInteger start $ \origin ->
    case ValuedIntegerRange.valuedIntegerRange
        origin IntegerRange.downwards
        (interpretedValuedIntegerRangeValue
          (ValuedIntegerRangeSemantics
            start IntegerRange.DownwardsIntegerTarget)) of
      Just value -> Right value
      Nothing -> Left (ExpectedFiniteIntegerOperand
        LeftOperand IntegerValueKind)

integerTypeValue :: Either InterpretingError InterpretedValue
integerTypeValue =
  Right
    (IntegerType.integerType
      (interpretedValuedIntegerRangeValue IntegerTypeSemantics))

interpretedNaturalRangeValue
  :: NaturalRange.NaturalRange rangeScope federationScope
  -> InterpretedValue
interpretedNaturalRangeValue valueRange =
  makeInterpretedValue
    structuralDatraType
    (NaturalRangeForm evaluatedNaturalRange)
    (ValidInsertion insertion)
    valueMap
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation evaluatedNaturalRange))
    NonTotalInterpretedMap
    semantics
  where
    evaluatedNaturalRange = EvaluatedNaturalRange valueRange
    evaluated =
      EvaluatedRange 1 (NaturalRange.naturalRangeEllipsisRange valueRange)
    insertion = rangeInsertion evaluated
    valueMap = mapFromInsertion insertion [semantics]
    semantics =
      NaturalRangeSemantics
        (NaturalRange.naturalRangeStart valueRange)
        (NaturalRange.naturalRangeTarget valueRange)

interpretedValuedNaturalRangeValue
  :: ValueSemantics
  -> ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
  -> InterpretedValue
interpretedValuedNaturalRangeValue semantics valueRange =
  makeInterpretedValue
    structuralDatraType
    (ValuedNaturalRangeForm evaluatedValuedNaturalRange)
    (ValidInsertion insertion)
    valueMap
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation evaluatedValuedNaturalRange))
    NonTotalInterpretedMap
    semantics
  where
    evaluatedValuedNaturalRange = EvaluatedValuedNaturalRange valueRange
    evaluated =
      EvaluatedRange
        1
        (ValuedNaturalRange.valuedNaturalRangeEllipsisRange valueRange)
    insertion = rangeInsertion evaluated
    valueMap = mapFromInsertion insertion [semantics]

interpretedIntegerRangeValue
  :: IntegerRange.IntegerRange rangeScope federationScope
  -> InterpretedValue
interpretedIntegerRangeValue valueRange =
  makeInterpretedValue
    structuralDatraType
    (IntegerRangeForm evaluatedIntegerRange)
    (ValidInsertion insertion)
    valueMap
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation evaluatedIntegerRange))
    NonTotalInterpretedMap
    semantics
  where
    evaluatedIntegerRange = EvaluatedIntegerRange valueRange
    insertion = eraseSuperEllipsisInsertion
      (IntegerRange.integerRangeInsertion valueRange)
    valueMap = mapFromInsertion insertion [semantics]
    semantics =
      IntegerRangeSemantics
        (IntegerRange.integerRangeStart valueRange)
        (IntegerRange.integerRangeTarget valueRange)

interpretedValuedIntegerRangeValue
  :: ValueSemantics
  -> ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
  -> InterpretedValue
interpretedValuedIntegerRangeValue semantics valueRange =
  makeInterpretedValue
    structuralDatraType
    (ValuedIntegerRangeForm evaluatedValuedIntegerRange)
    (ValidInsertion insertion)
    valueMap
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        evaluatedValuedIntegerRange))
    NonTotalInterpretedMap
    semantics
  where
    evaluatedValuedIntegerRange = EvaluatedValuedIntegerRange valueRange
    insertion = eraseSuperEllipsisInsertion
      (ValuedIntegerRange.valuedIntegerRangeInsertion valueRange)
    valueMap = mapFromInsertion insertion [semantics]

interpretedNaturalRangeFallback
  :: Natural
  -> NaturalRange.NaturalRangeTarget
  -> Either InterpretingError InterpretedValue
interpretedNaturalRangeFallback start target = do
  evaluated <-
    makeEvaluatedRangeAt
      1
      (finiteOrdinal start)
      (case target of
        NaturalRange.UpwardsTarget -> Range.PlusSign
        NaturalRange.FiniteNaturalTarget final
          | start <= final -> Range.GivenTarget (finiteOrdinal (final + 1))
          | final == 0 -> Range.MinusSign
          | otherwise -> Range.GivenTarget (finiteOrdinal (final - 1)))
  let insertion = rangeInsertion evaluated
      semantics = NaturalRangeSemantics start target
      valueMap = mapFromInsertion insertion [semantics]
  pure
    (makeSingletonInterpretedValue
      structuralDatraType
      (RangeForm evaluated)
      (ValidInsertion insertion)
      valueMap
      TotalInterpretedMap
      semantics)

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
  makeSingletonInterpretedValue
    structuralDatraType
    (RangeForm evaluatedRange)
    (ValidInsertion insertion)
    valueMap
    TotalInterpretedMap
    semantics
  where
    insertion = rangeInsertion evaluatedRange
    semantics = RangeSemantics (rangeDescription evaluatedRange)
    valueMap = mapFromInsertion insertion [semantics]

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
