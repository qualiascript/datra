-- | The language-level coalization operation.
--
-- Coalization forgets an Atlas's page decomposition and includes the
-- resulting carrier back as a single-page Atlas. Ranked final-page values are
-- retained, so ordinary access still observes the operand's members.
module Evaluation.Coalization
  ( coalizeValue
  ) where

import Evaluation.Value

coalizeValue :: InterpretedValue -> InterpretedValue
coalizeValue value
  | CoalizationForm _ <- interpretedForm value = value
  | otherwise =
      makeInterpretedValue
        (interpretedDatraType value)
        (CoalizationForm value)
        (interpretedInsertionCapability value)
        coalizedMap
        (interpretedAtlasMapFederation value)
        totality
        (CoalizationSemantics (interpretedSemantics value))
  where
    operandMap = interpretedMap value
    coalizedMap = operandMap
      { interpretedMapPageCardinality = 1
      , interpretedMapComponents = [interpretedSemantics value]
      }
    totality
      | interpretedValueHasTotalMap value = TotalInterpretedMap
      | otherwise = NonTotalInterpretedMap
