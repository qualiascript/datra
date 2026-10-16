-- | Public semantic boundary between Datra syntax and evaluated values.
--
-- AST traversal belongs to the application interpreter. Type coercion,
-- checked construction, canonicalization, access validation, and their
-- strongly typed failures belong here.
module DatraTypes
  ( ASTMetaCategory (..)
  , DatraType
  , PreparedFunctionArgument (..)
  , EvaluatedFunctionInvocation (..)
  , EvaluatedFunctionBody (..)
  , functionBodySource
  , EvaluatedFunction (..)
  , ReductionContext (..)
  , functionSyntaxEquivalent
  , makeFunctionValue
  , makeFunctionBodyValue
  , interpretedFunctionBody
  , makeDependentSumValue
  , dependentSumView
  , withDependentSumView
  , orderedAtlasMapView
  , withOrderedAtlasMapView
  , withOrderedAtlasMapValues
  , withMapView
  , OrdinalIndexedFamily (..)
  , ordinalIndexedValueFamily
  , ordinalIndexedProductFamily
  , withDependentSumAccess
  , withDependentSumFamily
  , withDependentSumReservationTarget
  , makeLazyMapValue
  , makeCheckedLazyMapValue
  , coalizeValue
  , coalizeMapMemberAt
  , syntaxCategoryTypeValue
  , captureSyntaxExpression
  , specializeSyntaxHoleKind
  , functionAlternatives
  , templateTypeValue
  , syntaxTemplateTypeValue
  , anyTypeValue
  , ordinalTypeValue
  , builtinMetaTypeName
  , builtinMetaTypeCanonicalString
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , naturalValuedRangeTypeValue
  , integerValuedRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , InterpretedValue
  , EvaluatedStringTemplate (..)
  , EvaluatedStringTemplateSegment (..)
  , DynamicScopeLabel (..)
  , ScopeActivation (..)
  , ScopeProtectionPolicy (..)
  , ScopeProtection (..)
  , Decision (..)
  , neverValue
  , interpretedScopeProtection
  , protectInterpretedValue
  , withoutScopeProtection
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , NamedMember (..)
  , NamedMapProjection (..)
  , NamedMapView (..)
  , namedMapView
  , namedMapOrderType
  , namedMapMemberAt
  , namedMapMemberByName
  , namedMapContainsName
  , namedMapViewForValue
  , appendNamedMapViews
  , namedMapValue
  , withNamedMapView
  , InterpretingError (..)
  , FunctionFailure (..)
  , ModuleEvaluationFailure (..)
  , NamedAccessFailure (..)
  , MapLengthFailure (..)
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
  , optionalPresentType
  , justUnderlying
  , optionalUnderlying
  , nothingValue
  , asciiStringValue
  , charTypeValue
  , listTypeValue
  , identifierValueTypeValue
  , CanonicalStringCodec (..)
  , toStringValue
  , templateValue
  , stripOuterIdentifierValue
  , stripOuterIdentifierType
  , evalValues
  , requireFiniteInteger
  , IntegerLimit (..)
  , integerLimitProjection
  , requireIntegerLimit
  , makeIntegerLimit
  , formulationValue
  , skipValue
  , addValues
  , subtractValues
  , plusValue
  , minusValue
  , multiplyValues
  , exponentiateValues
  , compareIntegerLimitValues
  , ordinalSumValues
  , ordinalProductValues
  , ordinalMinusValues
  , ordinalExponentValues
  , ordinalLTValues
  , ordinalLTEValues
  , ordinalGTValues
  , ordinalGTEValues
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
  , IntegerRangeKind (..)
  , integerLimitRangeValue
  , integerTypeValue
  , dependentIdentifierTypeValue
  , dependentIdentifierTemplateTypeValue
  , identifierTemplateTypeValue
  , simpleIdentifierName
  , identifierUnderlyingValue
  , simpleIdentifierTypeValue
  , inferredIdentifierAssignmentValue
  , canonicalValueMarker
  , withTrailingIdentifierMarker
  , hasTrailingIdentifierMarker
  , assignIdentifierValues
  , makeAtlasMap
  , makeAtlasMapPreservingSingleton
  , isEmptyMap
  , makeArgumentMap
  , makeArgumentMapPreservingSingleton
  , argumentMapMembers
  , argumentRows
  , overloadArgumentRows
  , functionArgumentValue
  , argumentPresentations
  , makeAtlasExpansion
  , concatenateValues
  , concatenateValuesWithEquivalenceView
  , mapLengthValue
  , ArgumentSchema
  , argumentSchemaFromValue
  , argumentSlotSchema
  , orderedArgumentSchema
  , unorderedArgumentSchema
  , concatenatedArgumentSchema
  , projectedArgumentSchema
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaBodyDomain
  , argumentSchemaBodyValues
  , argumentSchemaPositionalDomain
  , argumentSchemaVariadicElementType
  , argumentSchemaValuesComplete
  , optionalArgumentSlot
  , argumentValuesComplete
  , suppliedArgumentValue
  , foliageArgumentValuesComplete
  , compileParameters
  , compileParametersWithGenerics
  , compileDependentParameter
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , prepareArguments
  , matchArguments
  , selectFunctionCandidate
  , GenericArgumentBinder (..)
  , overloadArgumentSchemaComplete
  , overloadArgumentSchemaCompleteWithGenerics
  , overloadArgumentSchemaCompleteWithTrustedGenerics
  , argumentSchemaHasInferredGenerics
  , argumentSchemaInferredGenericNames
  , argumentSchemaValidationArgument
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  , namedAccessValue
  , accessValues
  , validateFunctionInput
  , specifyValues
  , contextuallySpecifyValues
  , IdentifierNameDisjointness (..)
  , identifierNameDisjointness
  , interpretedValueKind
  , interpretedStringTemplate
  , interpretedNamedMapView
  , withStringTemplatePlan
  , interpretedDatraType
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , PresentationDependency (..)
  , interpretedCanonicalResult
  , interpretedSemanticResult
  , interpretedCanonicalPresentation
  , withCanonicalReference
  , withCanonicalNamedAccess
  , withCanonicalApplication
  , withoutCanonicalPresentation
  , withoutCanonicalDependencies
  , interpretedEvaluationSource
  , withEvaluationSource
  , interpretedExplicitOrdinal
  , interpretedSpecificationSourceValue
  , interpretedFederationSpecificationBranches
  , interpretedFederationSpecificationSourceValue
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , asciiStringFromInterpretedMap
  , interpretedMapCardinality
  , interpretedMapPageCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedMapValueAtChecked
  , decideClosedPublicResultContract
  ) where

import Evaluation.Error
  ( AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  , FunctionFailure (..)
  , InterpretedValueKind (..)
  , InterpretingError (..)
  , MapLengthFailure (..)
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
  , makeFormulation
  , makeSkip
  , makeNatural
  , makeInteger
  )
import Evaluation.Coalization (coalizeMapMemberAt, coalizeValue)
import Evaluation.SyntaxCapture
  ( captureSyntaxExpression, specializeSyntaxHoleKind )
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
  , compileParametersWithGenerics
  , compileDependentParameter
  , matchArguments
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , prepareArguments
  , selectFunctionCandidate
  )
import Evaluation.Arguments
  ( argumentMapMembers
  , argumentPresentations
  , argumentRows
  , functionArgumentValue
  , makeArgumentMap
  , makeArgumentMapPreservingSingleton
  , overloadArgumentRows
  )
import Evaluation.Optional
  ( justUnderlying
  , makeNothing
  , makeOptionalValue
  , optionalPresentType
  , optionalUnderlying
  )
import Evaluation.ToString
  ( CanonicalStringCodec (..)
  , templateValue
  , toStringValue
  )
import Evaluation.IdentifierErasure
  ( stripOuterIdentifierValue
  , stripOuterIdentifierType
  )
import Evaluation.Eval (evalValues)
import BooleanType qualified
import Evaluation.Map
  ( concatenateValues
  , concatenateValuesWithEquivalenceView
  , isEmptyMap
  , makeAtlasExpansion
  , makeAtlasMap
  , makeAtlasMapPreservingSingleton
  )
import Evaluation.Overload
  ( ArgumentSchema
  , GenericArgumentBinder (..)
  , argumentSchemaFromValue
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaBodyDomain
  , argumentSchemaBodyValues
  , argumentSchemaPositionalDomain
  , argumentSchemaVariadicElementType
  , argumentSchemaValuesComplete
  , optionalArgumentSlot
  , argumentValuesComplete
  , suppliedArgumentValue
  , foliageArgumentValuesComplete
  , argumentSlotSchema
  , concatenatedArgumentSchema
  , projectedArgumentSchema
  , orderedArgumentSchema
  , overloadArgumentSchemaComplete
  , overloadArgumentSchemaCompleteWithGenerics
  , overloadArgumentSchemaCompleteWithTrustedGenerics
  , argumentSchemaHasInferredGenerics
  , argumentSchemaInferredGenericNames
  , argumentSchemaValidationArgument
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  , unorderedArgumentSchema
  )
import Evaluation.Numerical
  ( addValues
  , compareIntegerLimitValues
  , IntegerLimit (..)
  , integerLimitProjection
  , makeIntegerLimit
  , requireIntegerLimit
  , requireFiniteInteger
  , subtractValues
  , plusValue
  , minusValue
  , exponentiateValues
  , multiplyValues
  )
import Evaluation.Ordinal
  ( ordinalSumValues
  , ordinalProductValues
  , ordinalMinusValues
  , ordinalExponentValues
  , ordinalLTValues
  , ordinalLTEValues
  , ordinalGTValues
  , ordinalGTEValues
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
import Evaluation.LimitRange
  ( IntegerRangeKind (..)
  , integerLimitRangeValue
  )
import Evaluation.Length (mapLengthValue)
import Evaluation.Identifier
  ( dependentIdentifierTypeValue
  , dependentIdentifierTemplateTypeValue
  , identifierTemplateTypeValue
  , canonicalValueMarker
  , hasTrailingIdentifierMarker
  , simpleIdentifierName
  , identifierUnderlyingValue
  , simpleIdentifierTypeValue
  , inferredIdentifierAssignmentValue
  , withTrailingIdentifierMarker
  )
import Evaluation.OrdinalIndexedFamily
  ( OrdinalIndexedFamily (..)
  , ordinalIndexedValueFamily
  , ordinalIndexedProductFamily
  )
import Evaluation.Specification
  ( assignIdentifierValues
  , contextuallySpecifyValues
  , validateFunctionInput
  , specifyValues
  )
import Evaluation.Specification.Subfederation
  ( IdentifierNameDisjointness (..)
  , identifierNameDisjointness
  )
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.ResultContract
  ( decideClosedPublicResultContract )
import Evaluation.Value
  ( ASTMetaCategory (..)
  , DatraType
  , PreparedFunctionArgument (..)
  , EvaluatedFunction (..)
  , EvaluatedFunctionBody (..)
  , functionBodySource
  , EvaluatedFunctionInvocation (..)
  , ReductionContext (..)
  , DependentSumStructure (..)
  , functionSyntaxEquivalent
  , makeFunctionValue
  , makeFunctionBodyValue
  , interpretedFunctionBody
  , makeDependentSumValue
  , dependentSumView
  , withDependentSumView
  , orderedAtlasMapView
  , withOrderedAtlasMapView
  , withOrderedAtlasMapValues
  , withMapView
  , withDependentSumStructure
  , withDependentSumAccess
  , withDependentSumFamily
  , withDependentSumReservationTarget
  , makeLazyMapValue
  , makeCheckedLazyMapValue
  , syntaxCategoryTypeValue
  , functionAlternatives
  , templateTypeValue
  , syntaxTemplateTypeValue
  , anyTypeValue
  , ordinalTypeValue
  , builtinMetaTypeName
  , builtinMetaTypeCanonicalString
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , naturalValuedRangeTypeValue
  , integerValuedRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , PresentationDependency (..)
  , CanonicalResult (..)
  , InterpretedMap
  , InterpretedValue
  , NamedMember (..)
  , NamedMapProjection (..)
  , NamedMapView (..)
  , namedMapView
  , namedMapOrderType
  , namedMapMemberAt
  , namedMapMemberByName
  , namedMapContainsName
  , namedMapViewForValue
  , appendNamedMapViews
  , namedMapValue
  , withNamedMapView
  , EvaluatedStringTemplate (..)
  , EvaluatedStringTemplateSegment (..)
  , DynamicScopeLabel (..)
  , ScopeActivation (..)
  , ScopeProtectionPolicy (..)
  , ScopeProtection (..)
  , neverValue
  , interpretedScopeProtection
  , protectInterpretedValue
  , withoutScopeProtection
  , interpretedCanonicalResult
  , interpretedSemanticResult
  , interpretedCanonicalPresentation
  , interpretedNamedMapView
  , withCanonicalReference
  , withCanonicalNamedAccess
  , withCanonicalApplication
  , withoutCanonicalPresentation
  , withoutCanonicalDependencies
  , interpretedDatraType
  , interpretedEvaluationSource
  , withEvaluationSource
  , interpretedExplicitOrdinal
  , interpretedSpecificationSourceValue
  , interpretedFederationSpecificationBranches
  , interpretedFederationSpecificationSourceValue
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedMap
  , asciiStringFromInterpretedMap
  , interpretedMapCardinality
  , interpretedMapPageCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedMapValueAtChecked
  , interpretedRangeDescription
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , interpretedValueKind
  , interpretedStringTemplate
  , withStringTemplatePlan
  )
import Numeric.Natural (Natural)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal, naturalsBelow, omega)

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

charTypeValue :: Either InterpretingError InterpretedValue
charTypeValue = do
  characters <- valuedNaturalRangeValue 0 255
  pure
    (withDependentSumStructure CharacterDependentSum
      (makeDependentSumValue "Char" characters $ \source -> do
        _ <- specifyValues source characters
        pure source))

-- | A semantic recursive-list fixed point. The language layer supplies the
-- canonical source of the evaluated @fun@ expression; this semantic helper
-- has no knowledge of surface binders or standard-library names.
listTypeValue :: String -> InterpretedValue -> InterpretedValue
listTypeValue presentationSource elementType =
  withDependentSumStructure (ListDependentSum elementType) value
  where
    value = withDependentSumAccess project
      (makeDependentSumValue presentationSource staticTarget validate)
    staticTarget = makeLazyMapValue omega (const (Just elementType))
    project insertion =
      case interpretedValueKind insertion of
        NaturalValueKind -> Right elementType
        _ -> Right value
    validate source = do
      case interpretedValueKind source of
        MapValueKind -> validateMembers source
        AsciiStringValueKind -> pure ()
        -- Atlas normalization erases a singleton sequence, so @T; ()@ is
        -- represented by the element itself.  This is the one-element fibre
        -- of the same recursive list, not a separate special case in source.
        _ -> () <$ specifyValues source elementType
      pure source
    validateMembers source = do
      count <- maybe
        (Left (FunctionEvaluationFailed
          FunctionArgumentsRequireFinitePages))
        Right
        (naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap source)))
      mapM_ (validateAt source) (naturalsBelow count)
    validateAt source position = do
      member <- maybe
        (Left (FunctionEvaluationFailed
          (FunctionArgumentPageUnavailable position)))
        Right
        (interpretedMapValueAt
          (interpretedMap source) (finiteOrdinal position))
      () <$ specifyValues member elementType

identifierValueTypeValue :: InterpretedValue
identifierValueTypeValue = makeIdentifierValueType

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation

skipValue :: InterpretedValue
skipValue = makeSkip
