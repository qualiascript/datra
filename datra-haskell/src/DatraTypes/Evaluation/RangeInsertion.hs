-- | Executable and invertible native range constructors.
module Evaluation.RangeInsertion
  ( valuedIntegerRangeInsertion
  , boundedIntegerRangeInsertion
  ) where

import Evaluation.Access (accessValues)
import Evaluation.Arguments (makeArgumentativeMapPreservingSingleton)
import Evaluation.Construction (makeAsciiString, makeInteger, makeNatural)
import Evaluation.Error (InterpretingError)
import Evaluation.LimitRange
  ( IntegerRangeKind (IntegerRangeKind, ValuedIntegerRangeKind)
  , integerLimitRangeValue
  )
import Evaluation.Numerical (makeIntegerLimit, requireIntegerLimit)
import Evaluation.Value
import IntegerRange qualified
import NaturalRange qualified

data RangeEndpoint
  = FiniteEndpoint IntegerLimit
  | UpwardsEndpoint
  | DownwardsEndpoint

valuedIntegerRangeInsertion :: RuntimeFunctionInsertion
valuedIntegerRangeInsertion = RuntimeFunctionInsertion
  (rangeApplication ValuedIntegerRangeKind)
  valuedRangePreimage

boundedIntegerRangeInsertion :: RuntimeFunctionInsertion
boundedIntegerRangeInsertion = RuntimeFunctionInsertion
  boundedApplication
  boundedRangePreimage

rangeApplication
  :: IntegerRangeKind
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
rangeApplication kind argument = do
  start <- accessValues argument (makeNatural 0)
  endpoint <- accessValues argument (makeNatural 1)
  integerLimitRangeValue kind start endpoint

boundedApplication
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
boundedApplication argument = do
  start <- accessValues argument (makeNatural 0)
  endpointValue <- accessValues argument (makeNatural 1)
  endpoint <- requireIntegerLimit endpointValue
  integerLimitRangeValue IntegerRangeKind start (makeIntegerLimit endpoint)

valuedRangePreimage :: InterpretedValue -> Maybe InterpretedValue
valuedRangePreimage value = do
  (origin, endpoint) <- valuedRangeArguments
    (interpretedSemanticResult value)
  endpointValue <- case endpoint of
    FiniteEndpoint limit -> Just (makeIntegerLimit limit)
    UpwardsEndpoint -> Just (makeAsciiString "up")
    DownwardsEndpoint -> Just (makeAsciiString "down")
  either (const Nothing) Just
    (makeArgumentativeMapPreservingSingleton
      [makeInteger origin, endpointValue])

valuedRangeArguments
  :: CanonicalResult
  -> Maybe (Integer, RangeEndpoint)
valuedRangeArguments canonical = case canonical of
  CanonicalValuedNaturalRange origin target ->
    case target of
      NaturalRange.FiniteNaturalTarget endpoint -> Just
        ( toInteger origin
        , FiniteEndpoint (FiniteInteger (toInteger endpoint))
        )
      NaturalRange.UpwardsTarget -> Just (toInteger origin, UpwardsEndpoint)
  CanonicalValuedIntegerRange origin target ->
    case target of
      IntegerRange.FiniteIntegerTarget endpoint -> Just
        (origin, FiniteEndpoint (FiniteInteger endpoint))
      IntegerRange.UpwardsIntegerTarget -> Just (origin, UpwardsEndpoint)
      IntegerRange.DownwardsIntegerTarget -> Just (origin, DownwardsEndpoint)
      IntegerRange.AllIntegersTarget -> Nothing
  CanonicalCoalization
      (CanonicalConcatenation
        [finite, CanonicalIntegerLimit PositiveInfinity]) -> do
    (origin, UpwardsEndpoint) <- valuedRangeArguments finite
    Just (origin, FiniteEndpoint PositiveInfinity)
  CanonicalCoalization
      (CanonicalConcatenation
        [finite, CanonicalIntegerLimit NegativeInfinity]) -> do
    (origin, DownwardsEndpoint) <- valuedRangeArguments finite
    Just (origin, FiniteEndpoint NegativeInfinity)
  _ -> Nothing

boundedRangePreimage :: InterpretedValue -> Maybe InterpretedValue
boundedRangePreimage value = case interpretedSemanticResult value of
  CanonicalIntegerLimitRange origin target ->
    either (const Nothing) Just
      (makeArgumentativeMapPreservingSingleton
        [makeIntegerLimit origin, makeIntegerLimit target])
  _ -> Nothing
