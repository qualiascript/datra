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
  , anyTypeValue
  , builtinMetaTypeName
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , naturalValuedRangeTypeValue
  , integerValuedRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , FunctionFailure (..)
  , ExternalFailure (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
  , OverloadFailure (..)
  , overloadFailureIsAmbiguous
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
  , skipValue
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
  , requireCanonicalTypeAnnotation
  , assignIdentifierValues
  , makeAtlasMap
  , makeArgumentMap
  , argumentRows
  , overloadArgumentRows
  , functionArgumentValue
  , argumentPresentations
  , makeAtlasExpansion
  , concatenateValues
  , ArgumentSchema
  , argumentSlotSchema
  , orderedArgumentSchema
  , unorderedArgumentSchema
  , concatenatedArgumentSchema
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaPositionalDomain
  , argumentSchemaValuesComplete
  , compileParameters
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , parameterValues
  , prepareArguments
  , matchArguments
  , selectFunctionCandidate
  , overloadArgumentSchemaComplete
  , overloadValues
  , safeOverloadValues
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
  , ExternalFailure (..)
  , FunctionFailure (..)
  , InterpretedValueKind (..)
  , InterpretingError (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
  , OverloadFailure (..)
  , overloadFailureIsAmbiguous
  , OperandSide (..)
  )
import Evaluation.Access (accessValues, namedAccessValue)
import Evaluation.Construction
  ( makeAsciiString
  , makeIdentifierValueType
  , makeStringType
  , makeFormulation
  , makeSkip
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
import Evaluation.FunctionArguments
  ( compileParameters
  , matchArguments
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , parameterValues
  , prepareArguments
  , selectFunctionCandidate
  )
import Evaluation.Arguments
  ( argumentPresentations
  , argumentRows
  , functionArgumentValue
  , makeArgumentMap
  , overloadArgumentRows
  )
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
  ( ArgumentSchema
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaPositionalDomain
  , argumentSchemaValuesComplete
  , argumentSlotSchema
  , concatenatedArgumentSchema
  , orderedArgumentSchema
  , overloadArgumentSchemaComplete
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  , unorderedArgumentSchema
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
  , requireCanonicalTypeAnnotation
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
  , anyTypeValue
  , builtinMetaTypeName
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , naturalValuedRangeTypeValue
  , integerValuedRangeTypeValue
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

skipValue :: InterpretedValue
skipValue = makeSkip
