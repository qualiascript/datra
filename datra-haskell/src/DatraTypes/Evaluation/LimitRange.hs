-- | Semantic construction of integer ranges whose bounds may be infinite.
module Evaluation.LimitRange
  ( IntegerRangeKind (..)
  , integerLimitRangeValue
  ) where

import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Numerical
  ( IntegerLimit (..)
  , makeIntegerLimit
  , requireIntegerLimit
  )
import Evaluation.Map (concatenateValues)
import Evaluation.Range
import Evaluation.Value

data IntegerRangeKind
  = IntegerRangeKind
  | ValuedIntegerRangeKind
  deriving (Eq, Show)

data IntegerRangeEndpoint
  = FiniteEndpoint IntegerLimit
  | UpwardsEndpoint
  | DownwardsEndpoint

integerLimitRangeValue
  :: IntegerRangeKind
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
integerLimitRangeValue kind startValue endpointValue = do
  start <- requireIntegerLimit LeftOperand startValue
  endpoint <- requireIntegerRangeEndpoint endpointValue
  case start of
    FiniteInteger finiteStart -> finiteStartRange kind finiteStart endpoint
    PositiveInfinity -> infiniteStartRange kind PositiveInfinity endpoint
    NegativeInfinity -> infiniteStartRange kind NegativeInfinity endpoint
  where
    infiniteStartRange ValuedIntegerRangeKind _ _ =
      Left (IndeterminateInfinityOperation "from")
    infiniteStartRange IntegerRangeKind infinity target =
      unvaluedInfiniteStartRange infinity target

unvaluedInfiniteStartRange
  :: IntegerLimit
  -> IntegerRangeEndpoint
  -> Either InterpretingError InterpretedValue
unvaluedInfiniteStartRange infinity endpoint =
  case (infinity, endpoint) of
    (PositiveInfinity, UpwardsEndpoint) -> singleton PositiveInfinity
    (PositiveInfinity, DownwardsEndpoint) -> allLimits
    (NegativeInfinity, DownwardsEndpoint) -> singleton NegativeInfinity
    (NegativeInfinity, UpwardsEndpoint) -> allLimits
    (_, FiniteEndpoint same) | same == infinity -> singleton infinity
    (PositiveInfinity, FiniteEndpoint (FiniteInteger target)) ->
      integerRangeUpwardsValue target >>= include PositiveInfinity
    (NegativeInfinity, FiniteEndpoint (FiniteInteger target)) ->
      integerRangeDownwardsValue target >>= include NegativeInfinity
    (PositiveInfinity, FiniteEndpoint NegativeInfinity) -> allLimits
    (NegativeInfinity, FiniteEndpoint PositiveInfinity) -> allLimits
    _ -> Left (IndeterminateInfinityOperation "range")
  where
    singleton = Right . makeIntegerLimit
    include limit finite = makeEitherValue finite (makeIntegerLimit limit)
    allLimits = do
      negative <- integerRangeDownwardsValue 0
      positive <- integerRangeUpwardsValue 1
      finite <- concatenateValues negative positive
      withNegative <- makeEitherValue (makeIntegerLimit NegativeInfinity) finite
      makeEitherValue withNegative (makeIntegerLimit PositiveInfinity)

requireIntegerRangeEndpoint
  :: InterpretedValue
  -> Either InterpretingError IntegerRangeEndpoint
requireIntegerRangeEndpoint value =
  case rangeDirection (interpretedSemantics value) of
    Just True -> Right UpwardsEndpoint
    Just False -> Right DownwardsEndpoint
    Nothing -> FiniteEndpoint <$> requireIntegerLimit RightOperand value

rangeDirection :: ValueSemantics -> Maybe Bool
rangeDirection semantics =
  case semantics of
    AsciiStringSemantics "up" -> Just True
    AsciiStringSemantics "down" -> Just False
    AssignmentSemantics _ _ given -> rangeDirection given
    SpecificationSemantics source _ -> rangeDirection source
    _ -> Nothing

finiteStartRange
  :: IntegerRangeKind
  -> Integer
  -> IntegerRangeEndpoint
  -> Either InterpretingError InterpretedValue
finiteStartRange kind start endpoint =
  case endpoint of
    UpwardsEndpoint -> upwards start
    DownwardsEndpoint -> downwards start
    FiniteEndpoint (FiniteInteger target) -> bounded start target
    FiniteEndpoint PositiveInfinity -> do
      finite <- upwards start
      includeEndpoint finite PositiveInfinity
    FiniteEndpoint NegativeInfinity -> do
      finite <- downwards start
      includeEndpoint finite NegativeInfinity
  where
    includeEndpoint finite limit =
      case kind of
        ValuedIntegerRangeKind ->
          concatenateValues finite (makeIntegerLimit limit)
        IntegerRangeKind ->
          makeEitherValue finite (makeIntegerLimit limit)
    upwards value
      | value >= 0 = naturalUpwards (fromInteger value)
      | otherwise = integerUpwards value
    downwards = integerDownwards
    bounded origin target
      | origin >= 0 && target >= 0 =
          naturalBounded (fromInteger origin) (fromInteger target)
      | otherwise = integerBounded origin target
    naturalUpwards = case kind of
      IntegerRangeKind -> naturalRangeUpwardsValue
      ValuedIntegerRangeKind -> valuedNaturalRangeUpwardsValue
    integerUpwards = case kind of
      IntegerRangeKind -> integerRangeUpwardsValue
      ValuedIntegerRangeKind -> valuedIntegerRangeUpwardsValue
    integerDownwards = case kind of
      IntegerRangeKind -> integerRangeDownwardsValue
      ValuedIntegerRangeKind -> valuedIntegerRangeDownwardsValue
    naturalBounded = case kind of
      IntegerRangeKind -> naturalRangeValue
      ValuedIntegerRangeKind -> valuedNaturalRangeValue
    integerBounded = case kind of
      IntegerRangeKind -> integerRangeValue
      ValuedIntegerRangeKind -> valuedIntegerRangeValue
