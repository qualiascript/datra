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
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  , naturalValue
  , integerValue
  , asciiStringValue
  , formulationValue
  , addValues
  , subtractValues
  , minusValue
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
  , integerRangeValue
  , integerRangeUpwardsValue
  , integerRangeDownwardsValue
  , valuedIntegerRangeValue
  , valuedIntegerRangeUpwardsValue
  , valuedIntegerRangeDownwardsValue
  , integerTypeValue
  , identifierTypeValue
  , simpleIdentifierTypeValue
  , assignIdentifierValues
  , makeAtlasMap
  , makeAtlasExpansion
  , concatenateValues
  , accessValues
  , specifyValues
  , interpretedValueKind
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapPageCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  ) where

import Evaluation.Error
  ( AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  , InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Access (accessValues)
import Evaluation.Construction
  ( makeAsciiString
  , makeFormulation
  , makeNatural
  , makeInteger
  )
import Evaluation.Map
  ( concatenateValues
  , makeAtlasExpansion
  , makeAtlasMap
  )
import Evaluation.Numerical
  ( addValues
  , subtractValues
  , minusValue
  , exponentiateValues
  , multiplyValues
  )
import Evaluation.Range
  ( boundedRangeValue
  , naturalTypeValue
  , integerRangeValue
  , integerRangeUpwardsValue
  , integerRangeDownwardsValue
  , valuedIntegerRangeValue
  , valuedIntegerRangeUpwardsValue
  , valuedIntegerRangeDownwardsValue
  , integerTypeValue
  , naturalRangeUpwardsValue
  , naturalRangeValue
  , openMinusRangeValue
  , openPlusRangeValue
  , valuedNaturalRangeUpwardsValue
  , valuedNaturalRangeValue
  )
import Evaluation.Identifier
  ( identifierTypeValue
  , simpleIdentifierTypeValue
  )
import Evaluation.Specification
  ( assignIdentifierValues
  , specifyValues
  )
import Evaluation.Value
  ( CanonicalResult (..)
  , InterpretedMap
  , InterpretedValue
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapPageCardinality
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

integerValue :: Integer -> InterpretedValue
integerValue = makeInteger

asciiStringValue :: String -> Either InterpretingError InterpretedValue
asciiStringValue value =
  case find ((>= 256) . ord) value of
    Just character -> Left (InvalidAsciiStringCharacter character)
    Nothing -> Right (makeAsciiString value)

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation
