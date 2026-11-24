-- | Executable native range constructors.
module Evaluation.RangeInsertion
  ( valuedIntegerRangeInsertion
  , boundedIntegerRangeInsertion
  ) where

import Evaluation.Access (accessValues)
import Evaluation.Construction (makeNatural)
import Evaluation.Error (InterpretingError)
import Evaluation.LimitRange
  ( IntegerRangeKind (IntegerRangeKind, ValuedIntegerRangeKind)
  , integerLimitRangeValue
  )
import Evaluation.Numerical (makeIntegerLimit, requireIntegerLimit)
import Evaluation.Value

valuedIntegerRangeInsertion :: RuntimeFunctionInsertion
valuedIntegerRangeInsertion = RuntimeFunctionInsertion
  (rangeApplication ValuedIntegerRangeKind)

boundedIntegerRangeInsertion :: RuntimeFunctionInsertion
boundedIntegerRangeInsertion = RuntimeFunctionInsertion
  boundedApplication

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
