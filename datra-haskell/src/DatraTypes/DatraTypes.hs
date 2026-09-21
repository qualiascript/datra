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
  , asciiStringValue
  , formulationValue
  , addValues
  , multiplyValues
  , exponentiateValues
  , boundedRangeValue
  , openPlusRangeValue
  , openMinusRangeValue
  , naturalRangeValue
  , naturalRangeUpwardsValue
  , valuedNaturalRangeValue
  , valuedNaturalRangeUpwardsValue
  , naturalTypeValue
  , makeAtlasMap
  , makeAtlasExpansion
  , concatenateValues
  , accessValues
  , specifyValues
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

import DatraLanguage.Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Access (accessValues)
import Evaluation.Construction
  ( makeAsciiString
  , makeFormulation
  , makeNatural
  )
import Evaluation.Map
  ( concatenateValues
  , makeAtlasExpansion
  , makeAtlasMap
  )
import Evaluation.Numerical
  ( addValues
  , exponentiateValues
  , multiplyValues
  )
import Evaluation.Range
  ( boundedRangeValue
  , naturalTypeValue
  , naturalRangeUpwardsValue
  , naturalRangeValue
  , openMinusRangeValue
  , openPlusRangeValue
  , valuedNaturalRangeUpwardsValue
  , valuedNaturalRangeValue
  )
import Evaluation.Specification (specifyValues)
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

import Data.Char (ord)
import Data.List (find)

naturalValue :: Natural -> InterpretedValue
naturalValue = makeNatural

asciiStringValue :: String -> Either InterpretingError InterpretedValue
asciiStringValue value =
  case find ((>= 256) . ord) value of
    Just character -> Left (InvalidAsciiStringCharacter character)
    Nothing -> Right (makeAsciiString value)

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation
