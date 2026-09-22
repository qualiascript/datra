-- | Runtime views of retained Atlas-map federation construction structure.
module Evaluation.Federation.Structure
  ( sequenceOperands
  , expansionOperands
  , concatenationOperands
  ) where

import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Value

sequenceOperands :: InterpretedValue -> Maybe [InterpretedValue]
sequenceOperands value =
  case interpretedForm value of
    SequentialMapForm -> finiteMapValues value
    _ -> Nothing

expansionOperands
  :: InterpretedValue
  -> Maybe (InterpretedValue, InterpretedValue)
expansionOperands value =
  case interpretedForm value of
    ExpansionMapForm left right -> Just (left, right)
    _ -> Nothing

concatenationOperands :: InterpretedValue -> [InterpretedValue]
concatenationOperands value =
  case interpretedForm value of
    ConcatenatedMapForm left right ->
      concatenationOperands left <> concatenationOperands right
    RangeConcatenationForm _ (Just (left, right)) ->
      concatenationOperands left <> concatenationOperands right
    _ -> [value]

finiteMapValues :: InterpretedValue -> Maybe [InterpretedValue]
finiteMapValues value = do
  cardinality <-
    naturalAtOrdinal
      (interpretedMapFinalOrderType (interpretedMap value))
  traverse
    (interpretedMapValueAt (interpretedMap value) . finiteOrdinal)
    (finitePositions cardinality)
  where
    finitePositions 0 = []
    finitePositions cardinality = [0 .. cardinality - 1]
