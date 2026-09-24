-- | Public semantic boundary between Datra syntax and evaluated values.
--
-- AST traversal belongs to the application interpreter. Type coercion,
-- checked construction, canonicalization, access validation, and their
-- strongly typed failures belong here.
module DatraTypes
  ( CanonicalType
  , DatraType
  , StringRepresentation (..)
  , datraCanonicalType
  , datraStringRepresentation
  , EvaluatedFunction (..)
  , makeFunctionValue
  , syntaxCategoryTypeValue
  , astTypeValue
  , functionAlternatives
  , stringTemplateTypeValue
  , builtinMetaTypeName
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , InterpretedValue
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
  , booleanValue
  , booleanTypeValue
  , eitherValue
  , optionalValue
  , nothingValue
  , asciiStringValue
  , stringTypeValue
  , identifierValueTypeValue
  , CanonicalStringCodec (..)
  , toStringValue
  , weakToStringValue
  , stringTemplateValue
  , extractValue
  , evalValues
  , requireFiniteInteger
  , formulationValue
  , addValues
  , subtractValues
  , minusValue
  , multiplyValues
  , exponentiateValues
  , subfederationValues
  , equalValues
  , booleanAndValues
  , booleanOrValues
  , booleanNotValue
  , booleanCondition
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
  , dependentIdentifierTypeValue
  , simpleIdentifierTypeValue
  , assignIdentifierValues
  , makeAtlasMap
  , makeArgumentMap
  , argumentRows
  , functionArgumentValue
  , argumentPresentations
  , makeAtlasExpansion
  , concatenateValues
  , overloadValues
  , overloadValuesComplete
  , namedAccessValue
  , accessValues
  , validateFunctionInput
  , specifyValues
  , interpretedValueKind
  , interpretedDatraType
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , interpretedCanonicalResult
  , interpretedEvaluationSource
  , withEvaluationSource
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
import Evaluation.Access (accessValues, namedAccessValue)
import Evaluation.Construction
  ( makeAsciiString
  , makeIdentifierValueType
  , makeStringType
  , makeFormulation
  , makeNatural
  , makeInteger
  )
import Evaluation.Boolean
  ( booleanAndValues
  , booleanCondition
  , booleanNotValue
  , booleanOrValues
  , equalValues
  , subfederationValues
  , makeBoolean
  , makeBooleanType
  )
import Evaluation.Either (makeEitherValue)
import Evaluation.Arguments (makeArgumentMap, argumentPresentations, argumentRows, functionArgumentValue)
import Evaluation.Optional (makeNothing, makeOptionalValue)
import Evaluation.ToString
  ( CanonicalStringCodec (..)
  , stringTemplateValue
  , toStringValue
  , weakToStringValue
  )
import Extract (extractValue)
import Evaluation.Eval (evalValues)
import BooleanType qualified
import Evaluation.Map
  ( concatenateValues
  , makeAtlasExpansion
  , makeAtlasMap
  )
import Evaluation.Overload
  ( overloadValues
  , overloadValuesComplete
  )
import Evaluation.Numerical
  ( addValues
  , requireFiniteInteger
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
  ( dependentIdentifierTypeValue
  , simpleIdentifierTypeValue
  )
import Evaluation.Specification
  ( assignIdentifierValues
  , validateFunctionInput
  , specifyValues
  )
import Evaluation.Value
  ( CanonicalType
  , DatraType
  , StringRepresentation (..)
  , datraCanonicalType
  , datraStringRepresentation
  , EvaluatedFunction (..)
  , makeFunctionValue
  , syntaxCategoryTypeValue
  , astTypeValue
  , functionAlternatives
  , stringTemplateTypeValue
  , builtinMetaTypeName
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , CanonicalResult (..)
  , InterpretedMap
  , InterpretedValue
  , interpretedCanonicalResult
  , interpretedDatraType
  , interpretedEvaluationSource
  , withEvaluationSource
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapPageCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedRangeDescription
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , interpretedValueKind
  )
import Numeric.Natural (Natural)

import Data.Char (ord)
import Data.List (find)

naturalValue :: Natural -> InterpretedValue
naturalValue = makeNatural

integerValue :: Integer -> InterpretedValue
integerValue = makeInteger

booleanValue :: Bool -> InterpretedValue
booleanValue value =
  makeBoolean
    (if value then BooleanType.DatraTrue else BooleanType.DatraFalse)

booleanTypeValue :: Either InterpretingError InterpretedValue
booleanTypeValue = makeBooleanType

eitherValue
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
eitherValue = makeEitherValue

optionalValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
optionalValue = makeOptionalValue

nothingValue :: InterpretedValue
nothingValue = makeNothing

asciiStringValue :: String -> Either InterpretingError InterpretedValue
asciiStringValue value =
  case find ((>= 256) . ord) value of
    Just character -> Left (InvalidAsciiStringCharacter character)
    Nothing -> Right (makeAsciiString value)

stringTypeValue :: InterpretedValue
stringTypeValue = makeStringType

identifierValueTypeValue :: InterpretedValue
identifierValueTypeValue = makeIdentifierValueType

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation
