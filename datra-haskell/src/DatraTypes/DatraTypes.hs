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
  , SyntaxFunctionInsertion (..)
  , RuntimeFunctionInsertion (..)
  , EvaluatedFunctionBody (..)
  , functionBodySource
  , EvaluatedFunction (..)
  , ReductionContext (..)
  , functionSyntaxEquivalent
  , makeFunctionValue
  , withFunctionSyntax
  , makeFunctionBodyValue
  , interpretedFunctionBody
  , interpretedRuntimeFunctionInsertion
  , makeDependentSumValue
  , dependentSumView
  , dependentSumElementType
  , withDependentSumView
  , orderedAtlasMapView
  , withOrderedAtlasMapView
  , withOrderedAtlasMapValues
  , CoalizedMapView (..)
  , withCoalizedMapView
  , interpretedCoalizedMapView
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
  , EvaluatedGreedyStringTemplate (..)
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
  , NamedMapOrdinalProjection (..)
  , NamedMapProjection (..)
  , NamedMapView (..)
  , namedMapView
  , namedMapOrderType
  , namedMapMemberAt
  , namedMapOrdinalOrderType
  , namedMapOrdinalMemberAt
  , namedMapMemberByName
  , namedMapContainsName
  , namedMapDeclaredMembers
  , namedMapViewForValue
  , appendNamedMapViews
  , coalizeNamedMapView
  , coalizeNamedOrdinalMapView
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
  , streamTypeValue
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
  , integerLimitRangeIsSubfederationOf
  , integerTypeValue
  , dependentIdentifierTypeValue
  , dependentIdentifierTemplateTypeValue
  , identifierTemplateTypeValue
  , simpleIdentifierName
  , identifierUnderlyingValue
  , simpleIdentifierTypeValue
  , inferredIdentifierAssignmentValue
  , canonicalValueMarker
  , definitionMarker
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
  , dependentArgumentSlotSchema
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
  , specifyDependentSumElement
  , contextuallySpecifyValues
  , IdentifierNameDisjointness (..)
  , identifierNameDisjointness
  , interpretedValueKind
  , interpretedStringTemplate
  , interpretedGreedyStringTemplate
  , interpretedNamedMapView
  , withStringTemplatePlan
  , withGreedyStringTemplatePlan
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
  , dependentArgumentSlotSchema
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
  , integerLimitRangeIsSubfederationOf
  )
import Evaluation.Length (mapLengthValue)
import Evaluation.Identifier
  ( dependentIdentifierTypeValue
  , dependentIdentifierTemplateTypeValue
  , identifierTemplateTypeValue
  , canonicalValueMarker
  , definitionMarker
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
  , SyntaxFunctionInsertion (..)
  , RuntimeFunctionInsertion (..)
  , functionBodySource
  , EvaluatedFunctionInvocation (..)
  , ReductionContext (..)
  , DependentSumStructure (..)
  , functionSyntaxEquivalent
  , makeFunctionValue
  , withFunctionSyntax
  , makeFunctionBodyValue
  , interpretedFunctionBody
  , interpretedRuntimeFunctionInsertion
  , makeDependentSumValue
  , dependentSumView
  , dependentSumElementType
  , withDependentSumView
  , orderedAtlasMapView
  , withOrderedAtlasMapView
  , withOrderedAtlasMapValues
  , CoalizedMapView (..)
  , withCoalizedMapView
  , interpretedCoalizedMapView
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
  , NamedMapOrdinalProjection (..)
  , NamedMapProjection (..)
  , NamedMapView (..)
  , namedMapView
  , namedMapOrderType
  , namedMapMemberAt
  , namedMapOrdinalOrderType
  , namedMapOrdinalMemberAt
  , namedMapMemberByName
  , namedMapContainsName
  , namedMapDeclaredMembers
  , namedMapViewForValue
  , appendNamedMapViews
  , coalizeNamedMapView
  , coalizeNamedOrdinalMapView
  , withNamedMapView
  , EvaluatedStringTemplate (..)
  , EvaluatedStringTemplateSegment (..)
  , EvaluatedGreedyStringTemplate (..)
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
  , withSpecificationTargetEvidence
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
  , interpretedGreedyStringTemplate
  , withStringTemplatePlan
  , withGreedyStringTemplatePlan
  )
import Numeric.Natural (Natural)
import DatraOrdinal
  ( addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , naturalsBelow
  , ordinalLT
  , omega
  )
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )

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
        _ -> case interpretedCoalizedMapView source of
          Just view -> validateMembers (coalizedMapOrdinalValue view)
          -- Atlas normalization erases a singleton sequence, so @T; ()@ is
          -- represented by the element itself.  This is the one-element fibre
          -- of the same recursive list, not a separate special case in source.
          Nothing -> () <$ specifyDependentSumElement source elementType
      pure source
    validateMembers source = do
      count <- maybe
        (Left (FunctionEvaluationFailed
          NoApplicableFunctionAlternative))
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
      () <$ specifyDependentSumElement member elementType

-- | A semantic nonempty stream fixed point. Unlike a finite recursive list,
-- a stream has exactly the natural positions and validates each element only
-- when that position is demanded. This preserves type checking without
-- attempting to traverse an infinite source during specification.
streamTypeValue :: String -> InterpretedValue -> InterpretedValue
streamTypeValue presentationSource elementType =
  withDependentSumStructure (StreamDependentSum elementType) value
  where
    value = withDependentSumAccess project
      (makeDependentSumValue presentationSource staticTarget validate)
    staticTarget = makeLazyMapValue omega (const (Just elementType))
    project insertion =
      case interpretedValueKind insertion of
        NaturalValueKind -> Right elementType
        _ -> Right value
    validate source
      | interpretedValueKind sourceView == MapValueKind
      , interpretedMapFinalOrderType sourceMap == omega =
          Right (withCoalizedMapView checkedView source)
      | otherwise =
          Left (FunctionEvaluationFailed NoApplicableFunctionAlternative)
      where
        sourceView
          | interpretedValueKind source == MapValueKind = source
          | otherwise = maybe source coalizedMapOrdinalValue
              (interpretedCoalizedMapView source)
        sourceMap = interpretedMap sourceView
        checkedMap = makeCheckedLazyMapValue omega $ \position -> do
          selected <- interpretedMapValueAtChecked sourceMap position
          traverse
            (\member -> member <$ specifyDependentSumElement member elementType)
            selected
        checkedView = case interpretedNamedMapView sourceView of
          Just named -> withNamedMapView named checkedMap
          Nothing -> checkedMap

-- | Recursive homogeneous collections retain each original value after type
-- checking. Identifier values additionally have an ordinary structural map
-- view containing their canonical name, payload, and transparent metadata;
-- use that existing view for tuple-shaped element schemas without replacing
-- the identifier value returned to Datra.
specifyDependentSumElement
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyDependentSumElement source target =
  if interpretedValueKind source == DependentIdentifierTypeValueKind
    then do
      sourceView <- structuralMapView source
      let schema = argumentSchemaFromValue target
      _ <- argumentSchemaValuesComplete schema sourceView
      let evidenced = withSpecificationTargetEvidence target source
      pure (case namedFields schema sourceView of
        Just fields -> withNamedMapView fields evidenced
        Nothing -> evidenced)
    else specifyValues source target
  where
    namedFields schema value = do
      let names = map fst (argumentSchemaBindings schema)
          nameValues = foldl
            appendOrdinalOrderedValues
            emptyOrdinalOrderedValues
            (map singletonOrdinalOrderedValues names)
      if null names
        then Nothing
        else Just (viewFor nameValues (interpretedMap value))

    viewFor names values = namedMapView orderType memberAt memberByName
      (fmap (maybe False (const True)) . memberByName)
      where
        orderType = ordinalOrderedValuesOrderType names
        memberAt position = case ordinalOrderedValueAt names position of
          Nothing -> Right Nothing
          Just name -> fmap
            (fmap (NamedMember name . simpleIdentifierTypeValue name))
            (interpretedMapValueAtChecked values position)
        memberByName name = seek (finiteOrdinal 0)
          where
            seek position
              | not (position `ordinalLT` orderType) = Right Nothing
              | otherwise = do
                  member <- memberAt position
                  case member of
                    Just selected | namedMemberName selected == name ->
                      Right (Just selected)
                    _ -> seek (addOrdinals position (finiteOrdinal 1))

    structuralMapView value = do
      count <- maybe
        (Left (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        Right
        (naturalAtOrdinal orderType)
      members <- traverse memberAt (naturalsBelow count)
      pure (makeAtlasMap 2 members)
      where
        sourceMap = interpretedMap value
        orderType = interpretedMapFinalOrderType sourceMap
        memberAt position = maybe
          (Left (FunctionEvaluationFailed
            (FunctionArgumentPageUnavailable position)))
          Right
          =<< interpretedMapValueAtChecked sourceMap
            (finiteOrdinal position)

identifierValueTypeValue :: InterpretedValue
identifierValueTypeValue = makeIdentifierValueType

formulationValue :: Natural -> InterpretedValue
formulationValue = makeFormulation

skipValue :: InterpretedValue
skipValue = makeSkip
