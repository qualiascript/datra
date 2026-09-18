-- | Public semantic boundary between Datra syntax and evaluated values.
--
-- AST traversal belongs to the application interpreter. Type coercion,
-- checked construction, canonicalization, access validation, and their
-- strongly typed failures belong here.
module DatraTypes
  ( InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , OperandSide (..)
  , naturalValue
  , formulationValue
  , addValues
  , multiplyValues
  , exponentiateValues
  , boundedRangeValue
  , openPlusRangeValue
  , openMinusRangeValue
  , makeAtlasMap
  , concatenateValues
  , accessValues
  , interpretedValueKind
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  ) where

import Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Access (accessValues)
import Evaluation.Construction
  ( makeFormulation
  , makeNatural
  )
import Evaluation.Map
  ( concatenateValues
  , makeAtlasMap
  )
import Evaluation.Numerical
  ( addValues
  , exponentiateValues
  , multiplyValues
  )
import Evaluation.Range
  ( boundedRangeValue
  , openMinusRangeValue
  , openPlusRangeValue
  )
import Evaluation.Value
  ( CanonicalResult (..)
  , InterpretedMap
  , InterpretedValue
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedRangeDescription
  , interpretedValueKind
  )
import Numeric.Natural (Natural)

naturalValue :: Natural -> InterpretedValue
naturalValue = makeNatural

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation
