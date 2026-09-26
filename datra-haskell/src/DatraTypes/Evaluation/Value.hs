{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( BuiltinMetaType (..)
  , CanonicalType
  , DatraType
  , DatraTypeFamily (..)
  , StringRepresentation (..)
  , makeCanonicalType
  , canonicalTypeAsDatraType
  , makeNonCanonicalDatraType
  , structuralDatraType
  , weakStructuralDatraType
  , structuralDatraTypeWith
  , composedStructuralDatraType
  , functionDatraType
  , builtinMetaDatraType
  , totalBlockDatraType
  , datraTypeFamily
  , datraCanonicalType
  , datraStringRepresentation
  , EvaluatedFunction (..)
  , makeFunctionValue
  , syntaxCategoryTypeValue
  , astTypeValue
  , functionAlternatives
  , isFunctionFamily
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
  , ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , EvaluatedRange (..)
  , EvaluatedNaturalRange (..)
  , EvaluatedValuedNaturalRange (..)
  , EvaluatedIntegerRange (..)
  , EvaluatedValuedIntegerRange (..)
  , EvaluatedEither (..)
  , IdentifierDependency (..)
  , identifierDependencyStringFor
  , identifierDependencyRepresentativeString
  , identifierDependenciesCompatible
  , EvaluatedDependentIdentifierType (..)
  , EvaluatedDependentSum (..)
  , InterpretedTotalAtlasMap (..)
  , EvaluatedAtlasMapFederationMember (..)
  , EvaluatedSpecification (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , interpretedMapCardinality
  , ToStringInverseDecision (..)
  , ProvenInjectiveToString (..)
  , InterpretedAtlasMapFederationPrimitive (..)
  , InterpretedAtlasMapFederation
  , ValueSemantics (..)
  , CanonicalResult (..)
  , InterpretedValue
  , InterpretedValueTotality (..)
  , makeInterpretedValue
  , makeSingletonInterpretedValue
  , makeDependentSumValue
  , withIdentifierErasureType
  , interpretedIdentifierErasureType
  , withDependentSumAccess
  , makeLazyMapValue
  , interpretedForm
  , interpretedInsertionCapability
  , interpretedMap
  , interpretedAtlasMapFederation
  , interpretedTotalAtlasMap
  , interpretedSemantics
  , interpretedDatraType
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , interpretedCanonicalResult
  , interpretedEvaluationSource
  , withEvaluationSource
  , interpretedValueKind
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , asciiStringFromInterpretedMap
  , explicitOrdinal
  , explicitInsertion
  , rangeDescription
  , evaluatedRangeLevel
  , rangeInsertion
  , naturalRangeAsEvaluatedRange
  , valueRanges
  , emptyInterpretedMap
  , singletonMap
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  , appendOrdinalOrderedValues
  , appendSomeSuperEllipsisInsertion
  ) where

import Control.Monad (guard)
import BooleanType (DatraBoolean)
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (SingletonAtlasMapFederation) )
import Data.Char (chr)
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import Evaluation.Error (InterpretedValueKind (..), InterpretingError)
import Evaluation.DatraType
import Evaluation.Value.Semantics
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
import NaturalRange qualified
import ValuedNaturalRange qualified
import IntegerRange qualified
import ValuedIntegerRange qualified
import NumericalOperators.NumericalOperand
  ( SomeSuperEllipsis
  , someSuperEllipsisLevel
  )
import SuperEllipsisInsertion
  ( SomeSuperEllipsisInsertion
  , appendSomeSuperEllipsisInsertion
  , eraseSuperEllipsisInsertion
  )
import SuperEllipsisRange qualified as Range
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueInsertion
  , superEllipsisValueOrdinal
  )

data ExplicitOrigin = NaturalOrigin | ComputedOrigin

data EvaluatedExplicit where
  EvaluatedExplicit
    :: Natural
    -> ExplicitOrigin
    -> SuperEllipsisValue target scope
    -> EvaluatedExplicit

data EvaluatedRange where
  EvaluatedRange
    :: Natural
    -> Range.SuperEllipsisRange target scope
    -> EvaluatedRange

data EvaluatedNaturalRange where
  EvaluatedNaturalRange
    :: NaturalRange.NaturalRange rangeScope federationScope
    -> EvaluatedNaturalRange

data EvaluatedValuedNaturalRange where
  EvaluatedValuedNaturalRange
    :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
    -> EvaluatedValuedNaturalRange

data EvaluatedIntegerRange where
  EvaluatedIntegerRange
    :: IntegerRange.IntegerRange rangeScope federationScope
    -> EvaluatedIntegerRange

data EvaluatedValuedIntegerRange where
  EvaluatedValuedIntegerRange
    :: ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
    -> EvaluatedValuedIntegerRange

-- | A proven-disjoint federation union. The alternatives remain separate so
-- selection can record its route, but that internal route does not make equal
-- or overlapping Atlas maps distinct.
data EvaluatedEither = EvaluatedEither
  { evaluatedEitherLeft :: InterpretedValue
  , evaluatedEitherRight :: InterpretedValue
  }

data EvaluatedDependentIdentifierType = EvaluatedDependentIdentifierType
  { evaluatedIdentifierDependency :: IdentifierDependency
  , evaluatedIdentifierUnderlying :: InterpretedValue
  }

-- | A dependent sum keeps its ordinary structural approximation for map
-- operations and its exact left-to-right membership procedure for typing.
data EvaluatedDependentSum = EvaluatedDependentSum
  { evaluatedDependentSumStaticTarget :: InterpretedValue
  , evaluatedDependentSumSpecify
      :: InterpretedValue -> Either InterpretingError InterpretedValue
  , evaluatedDependentSumAccess
      :: Maybe
          (InterpretedValue -> Either InterpretingError InterpretedValue)
  }

-- | Runtime erasure of the proof-bearing 'TotalAtlasMap'.  This certificate
-- is attached only by constructors known to give every final-page region a
-- singleton value; being a singleton federation is not sufficient by itself.
newtype InterpretedTotalAtlasMap = InterpretedTotalAtlasMap
  { interpretedTotalAtlasMapUnderlying :: InterpretedMap
  }

-- | The selected member stays tagged by federation family. Primitive range
-- members remain distinct even when they carry the same natural; a singleton
-- federation records the canonical identity of its sole total-map member.
data EvaluatedAtlasMapFederationMember
  = EvaluatedNaturalRangeMember NaturalRange.NaturalSubrangeDescription
  | EvaluatedValuedNaturalRangeMember Natural
  | EvaluatedIntegerRangeMember IntegerRange.IntegerSubrangeDescription
  | EvaluatedValuedIntegerRangeMember Integer
  | EvaluatedAsciiStringMember String
  | EvaluatedEitherMember
      DatraBoolean
      EvaluatedAtlasMapFederationMember
  | EvaluatedDependentIdentifierTypeMember EvaluatedAtlasMapFederationMember
  | EvaluatedToStringMember
      InterpretedValue
      EvaluatedAtlasMapFederationMember
  | EvaluatedCanonicalTypeMember CanonicalResult
  | EvaluatedSingletonAtlasMapMember CanonicalResult
  | EvaluatedSequentialAtlasMapMember [EvaluatedAtlasMapFederationMember]
  | EvaluatedExpansionAtlasMapMember
      EvaluatedAtlasMapFederationMember
      EvaluatedAtlasMapFederationMember
  | EvaluatedConcatenatedAtlasMapMember [EvaluatedAtlasMapFederationMember]

-- | Erased semantic witness for a successful specification.  The core
-- 'SpecificationOperator' module carries the non-erased categorical form used
-- when concrete Atlas witnesses remain available.
data EvaluatedSpecification = EvaluatedSpecification
  { evaluatedSpecificationSourceValue :: InterpretedValue
  , evaluatedSpecificationSource :: InterpretedTotalAtlasMap
  , evaluatedSpecificationTarget :: InterpretedValue
  , evaluatedSpecificationMember :: EvaluatedAtlasMapFederationMember
  }

data EvaluatedFunction = EvaluatedFunction
  { functionDomain :: InterpretedValue
  , functionCodomain :: InterpretedValue
  , functionPattern :: Maybe (String, Bool)
  , functionSource :: Maybe String
  , functionSignatureSource :: String
  , functionPrepare :: Maybe
      (InterpretedValue -> Either InterpretingError InterpretedValue)
  , functionInvoke :: Maybe (InterpretedValue -> Either InterpretingError InterpretedValue)
  , functionValidatesResult :: Bool
  }

makeFunctionValue :: EvaluatedFunction -> InterpretedValue
makeFunctionValue function = makeInterpretedValue functionDatraType
  (FunctionForm function) NoInsertion emptyInterpretedMap
  (SingletonAtlasMapFederation emptyInterpretedMap) NonTotalInterpretedMap
  (FunctionSemantics (interpretedSemantics (functionDomain function))
    (interpretedSemantics (functionCodomain function)) (functionPattern function) (Just canonicalSource))
  where
    signature = functionSignatureSource function
    canonicalSource = case functionPattern function of
      Nothing -> maybe signature id (functionSource function)
      Just (patternText, ordinary) ->
        let typed = "(" <> show patternText <> (if ordinary then " as? (" else " as (") <> signature <> "))"
        in maybe typed (\body -> "(" <> body <> ") ~> " <> typed) (functionSource function)

interpretedFunction :: InterpretedValue -> Maybe EvaluatedFunction
interpretedFunction value = case interpretedForm value of
  FunctionForm function -> Just function
  _ -> Nothing

callableFunction :: InterpretedValue -> Maybe EvaluatedFunction
callableFunction value = case interpretedForm value of
  DependentIdentifierTypeForm identifier -> callableFunction (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification -> callableFunction (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification -> callableFunction (evaluatedSpecificationSourceValue specification)
  _ -> interpretedFunction value

functionSignature :: InterpretedValue -> Maybe (InterpretedValue, InterpretedValue)
functionSignature value = (\function -> (functionDomain function, functionCodomain function)) <$> callableFunction value

functionAlternatives :: InterpretedValue -> [EvaluatedFunction]
functionAlternatives value = case interpretedForm value of
  EitherForm alternatives -> functionAlternatives (evaluatedEitherLeft alternatives) <> functionAlternatives (evaluatedEitherRight alternatives)
  DependentIdentifierTypeForm identifier -> functionAlternatives (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification -> functionAlternatives (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification -> functionAlternatives (evaluatedSpecificationSourceValue specification)
  FunctionForm function -> [function]
  _ -> []

-- | True only when every branch of the value is callable.  Merely finding a
-- function somewhere inside an Either is not enough: mixed federations still
-- use ordinary structural specification and subfederation rules.
isFunctionFamily :: InterpretedValue -> Bool
isFunctionFamily value =
  case interpretedForm value of
    EitherForm alternatives ->
      isFunctionFamily (evaluatedEitherLeft alternatives)
        && isFunctionFamily (evaluatedEitherRight alternatives)
    DependentIdentifierTypeForm identifier ->
      isFunctionFamily (evaluatedIdentifierUnderlying identifier)
    AssignmentForm specification ->
      isFunctionFamily (evaluatedSpecificationSourceValue specification)
    SpecificationForm specification ->
      isFunctionFamily (evaluatedSpecificationSourceValue specification)
    FunctionForm _ -> True
    _ -> False

builtinMetaTypeName :: BuiltinMetaType -> String
builtinMetaTypeName AnyMetaType = "Any"
builtinMetaTypeName (ASTMetaType name) = maybe "_AST" id name
builtinMetaTypeName NatRangeMetaType = "NatRange"
builtinMetaTypeName IntRangeMetaType = "IntRange"
builtinMetaTypeName NatValRangeMetaType = "NatValRange"
builtinMetaTypeName IntValRangeMetaType = "IntValRange"
builtinMetaTypeName StringTemplateMetaType = "StrTempl"

builtinMetaTypeValue :: BuiltinMetaType -> InterpretedValue
builtinMetaTypeValue kind = makeInterpretedValue
  (builtinMetaDatraType kind)
  (BuiltinMetaTypeForm kind) NoInsertion emptyInterpretedMap
  (SingletonAtlasMapFederation emptyInterpretedMap) NonTotalInterpretedMap (BuiltinMetaTypeSemantics kind)

anyTypeValue, astTypeValue, naturalRangeTypeValue, integerRangeTypeValue,
  naturalValuedRangeTypeValue, integerValuedRangeTypeValue,
  stringTemplateTypeValue :: InterpretedValue
anyTypeValue = builtinMetaTypeValue AnyMetaType
astTypeValue = builtinMetaTypeValue (ASTMetaType Nothing)
naturalRangeTypeValue = builtinMetaTypeValue NatRangeMetaType
integerRangeTypeValue = builtinMetaTypeValue IntRangeMetaType
naturalValuedRangeTypeValue = builtinMetaTypeValue NatValRangeMetaType
integerValuedRangeTypeValue = builtinMetaTypeValue IntValRangeMetaType
stringTemplateTypeValue = builtinMetaTypeValue StringTemplateMetaType

syntaxCategoryTypeValue :: String -> InterpretedValue
syntaxCategoryTypeValue = builtinMetaTypeValue . ASTMetaType . Just

data ValueForm
  = BuiltinMetaTypeForm BuiltinMetaType
  | FunctionForm EvaluatedFunction
  | ExplicitForm EvaluatedExplicit
  | IntegerForm Integer
  | BooleanForm DatraBoolean
  | NothingForm
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | NaturalRangeForm EvaluatedNaturalRange
  | ValuedNaturalRangeForm EvaluatedValuedNaturalRange
  | IntegerRangeForm EvaluatedIntegerRange
  | ValuedIntegerRangeForm EvaluatedValuedIntegerRange
  | EitherForm EvaluatedEither
  | ArgumentMapForm [InterpretedValue] InterpretedValue
  | SkipForm InterpretedValue
  | FederationSpecificationForm
      InterpretedValue InterpretedValue [InterpretedValue]
  | RangeConcatenationForm
      [EvaluatedRange]
      (Maybe (InterpretedValue, InterpretedValue))
  | AsciiStringForm String
  | StringTypeForm
  | IdentifierValueTypeForm
  | ToStringForm
  | WeakToStringForm
  | StringTemplateForm InterpretedValue
  | SpecificationForm EvaluatedSpecification
  | AssignmentForm EvaluatedSpecification
  | DependentIdentifierTypeForm EvaluatedDependentIdentifierType
  | IdentifierStringProjectionForm EvaluatedDependentIdentifierType
  | DependentSumForm EvaluatedDependentSum
  | SequentialMapForm
  | ExpansionMapForm InterpretedValue InterpretedValue
  | ConcatenatedMapForm InterpretedValue InterpretedValue
  | MapForm

data InsertionCapability
  = NoInsertion
  | ValidInsertion SomeSuperEllipsisInsertion
  | RejectedInsertion Range.SuperEllipsisRangeConcatError

data InterpretedMap = InterpretedMap
  { interpretedMapPageCardinality :: Natural
  , interpretedMapFinalValues :: OrdinalOrderedValues InterpretedValue
  , interpretedMapComponents :: [ValueSemantics]
  }

-- | Compatibility name for the number of Atlas pages represented by a map.
-- This is distinct from the final page's possibly-transfinite order type.
interpretedMapCardinality :: InterpretedMap -> Natural
interpretedMapCardinality = interpretedMapPageCardinality

-- | The partial inverse carried by a proven pointwise string conversion.
data ToStringInverseDecision
  = ToStringInverseMatched [InterpretedValue]
  | ToStringInverseRejected

data ProvenInjectiveToString = ProvenInjectiveToString
  { injectiveToStringCharacterAlphabet :: Maybe String
  , injectiveToStringExactStrings :: Maybe [String]
  , invertInjectiveToString :: String -> ToStringInverseDecision
  }

-- | Primitive Atlas-map federation kinds understood by the interpreter.
-- The injective string primitive carries the language facts and inverse that
-- justified its construction; the explicitly weak primitive does not.
data InterpretedAtlasMapFederationPrimitive
  = NaturalRangeAtlasMapFederation EvaluatedNaturalRange
  | ValuedNaturalRangeAtlasMapFederation EvaluatedValuedNaturalRange
  | IntegerRangeAtlasMapFederation EvaluatedIntegerRange
  | ValuedIntegerRangeAtlasMapFederation EvaluatedValuedIntegerRange
  | EitherAtlasMapFederation EvaluatedEither
  | DependentIdentifierTypeAtlasMapFederation EvaluatedDependentIdentifierType
  | IdentifierStringProjectionAtlasMapFederation EvaluatedDependentIdentifierType
  | StringTypeAtlasMapFederation
  | IdentifierValueTypeAtlasMapFederation
  | ToStringAtlasMapFederation
      InterpretedValue
      ProvenInjectiveToString
  | WeakToStringAtlasMapFederation InterpretedValue

type InterpretedAtlasMapFederation =
  AtlasMapFederationExpression
    InterpretedAtlasMapFederationPrimitive
    InterpretedMap

data InterpretedValue = InterpretedValue
  { interpretedDatraType :: DatraType
  , interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedAtlasMapFederation :: InterpretedAtlasMapFederation
  , interpretedTotalAtlasMap :: Maybe InterpretedTotalAtlasMap
  , interpretedSemantics :: ValueSemantics
  , interpretedIdentifierErasureType :: Maybe InterpretedValue
  , interpretedEvaluationSource :: Maybe String
  }

data InterpretedValueTotality = TotalInterpretedMap | NonTotalInterpretedMap

makeInterpretedValue
  :: DatraType
  -> ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedAtlasMapFederation
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeInterpretedValue datraType form capability valueMap federation totality semantics =
  InterpretedValue
    { interpretedDatraType = datraType
    , interpretedForm = form
    , interpretedInsertionCapability = capability
    , interpretedMap = valueMap
    , interpretedAtlasMapFederation = federation
    , interpretedTotalAtlasMap =
        case totality of
          TotalInterpretedMap -> Just (InterpretedTotalAtlasMap valueMap)
          NonTotalInterpretedMap -> Nothing
    , interpretedSemantics = semantics
    , interpretedIdentifierErasureType = Nothing
    , interpretedEvaluationSource = Nothing
    }

makeSingletonInterpretedValue
  :: DatraType
  -> ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeSingletonInterpretedValue datraType form capability valueMap totality =
  makeInterpretedValue
    datraType
    form
    capability
    valueMap
    (SingletonAtlasMapFederation valueMap)
    totality

makeDependentSumValue
  :: String
  -> InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
makeDependentSumValue source staticTarget specify =
  makeInterpretedValue
    structuralDatraType
    (DependentSumForm (EvaluatedDependentSum staticTarget specify Nothing))
    (interpretedInsertionCapability staticTarget)
    (interpretedMap staticTarget)
    (interpretedAtlasMapFederation staticTarget)
    NonTotalInterpretedMap
    (DependentSumSemantics source)

-- | Retain a symbolic family's erased view for inference, without enumerating
-- its unbounded collection of named slots.
withIdentifierErasureType :: InterpretedValue -> InterpretedValue -> InterpretedValue
withIdentifierErasureType erased value = value
  { interpretedIdentifierErasureType = Just erased }

-- | Attach the exact access map of a dependent family.  The structural
-- target remains available for ordinary static reasoning, while projection
-- is delayed until a concrete insertion is supplied.
withDependentSumAccess
  :: (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
withDependentSumAccess access value =
  case interpretedForm value of
    DependentSumForm dependent ->
      value
        { interpretedForm = DependentSumForm
            dependent { evaluatedDependentSumAccess = Just access }
        }
    _ -> value

-- | A lazily indexed Atlas map.  This is the erased runtime presentation of
-- a dependent family's page projection; values are demanded through normal
-- Atlas access rather than materialized eagerly.
makeLazyMapValue
  :: Ordinal
  -> (Ordinal -> Maybe InterpretedValue)
  -> InterpretedValue
makeLazyMapValue orderType valueAt =
  makeInterpretedValue
    structuralDatraType
    MapForm
    NoInsertion
    (InterpretedMap
      1
      (OrdinalOrderedValues orderType valueAt)
      [])
    (SingletonAtlasMapFederation
      (InterpretedMap
        1
        (OrdinalOrderedValues orderType valueAt)
        []))
    NonTotalInterpretedMap
    (MapSemantics 1 [])

interpretedValueHasTotalMap :: InterpretedValue -> Bool
interpretedValueHasTotalMap = maybe False (const True) . interpretedTotalAtlasMap

-- | Totality at the Datra type level. Begin/yield blocks are singleton types
-- even when the yielded value denotes a wider federation.
interpretedTypeIsTotal :: InterpretedValue -> Bool
interpretedTypeIsTotal value =
  interpretedValueHasTotalMap value
    || case datraTypeFamily
        (interpretedDatraType value) of
      TotalBlockTypeFamily -> True
      FunctionTypeFamily -> case interpretedFunction value of
        Just function -> maybe False (const True) (functionSource function)
        Nothing -> False
      _ -> False

-- | Retain evaluation provenance without changing the semantic map or codec.
withEvaluationSource :: Maybe String -> InterpretedValue -> InterpretedValue
withEvaluationSource source value =
  value
    { interpretedDatraType =
        maybe
          (interpretedDatraType value)
          (const totalBlockDatraType)
          source
    , interpretedEvaluationSource = source
    }

interpretedCanonicalResult :: InterpretedValue -> CanonicalResult
interpretedCanonicalResult = canonicalResult . interpretedSemantics

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    BuiltinMetaTypeForm (ASTMetaType _) -> FunctionValueKind
    BuiltinMetaTypeForm StringTemplateMetaType -> AsciiStringValueKind
    BuiltinMetaTypeForm _ -> RangeValueKind
    FunctionForm _ -> FunctionValueKind
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    IntegerForm _ -> IntegerValueKind
    BooleanForm _ -> BooleanValueKind
    NothingForm -> MapValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    NaturalRangeForm _ -> RangeValueKind
    ValuedNaturalRangeForm _ -> RangeValueKind
    IntegerRangeForm _ -> RangeValueKind
    ValuedIntegerRangeForm _ -> RangeValueKind
    EitherForm _ -> EitherValueKind
    ArgumentMapForm _ _ -> MapValueKind
    SkipForm _ -> FormulationValueKind
    FederationSpecificationForm _ _ _ -> SpecificationValueKind
    RangeConcatenationForm _ _ -> RangeConcatenationValueKind
    AsciiStringForm _ -> AsciiStringValueKind
    StringTypeForm -> AsciiStringValueKind
    IdentifierValueTypeForm -> AsciiStringValueKind
    ToStringForm -> AsciiStringValueKind
    WeakToStringForm -> AsciiStringValueKind
    StringTemplateForm _ -> AsciiStringValueKind
    SpecificationForm _ -> SpecificationValueKind
    AssignmentForm _ -> SpecificationValueKind
    DependentIdentifierTypeForm _ -> DependentIdentifierTypeValueKind
    IdentifierStringProjectionForm _ -> DependentIdentifierTypeValueKind
    DependentSumForm _ -> MapValueKind
    SequentialMapForm -> MapValueKind
    ExpansionMapForm _ _ -> MapValueKind
    ConcatenatedMapForm _ _ -> MapValueKind
    MapForm -> MapValueKind

interpretedExplicitOrdinal
  :: InterpretedValue
  -> Maybe (Natural, Ordinal)
interpretedExplicitOrdinal value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Just (explicitOrdinal explicitValue)
    _ -> Nothing

interpretedInteger :: InterpretedValue -> Maybe Integer
interpretedInteger value =
  case interpretedForm value of
    IntegerForm integer -> Just integer
    ExplicitForm (EvaluatedExplicit 1 _ explicitValue) ->
      toInteger <$> naturalAtOrdinal (superEllipsisValueOrdinal explicitValue)
    _ -> Nothing

interpretedFormulationLevel :: InterpretedValue -> Maybe Natural
interpretedFormulationLevel value =
  case interpretedForm value of
    FormulationForm formulation ->
      Just (someSuperEllipsisLevel formulation)
    _ -> Nothing

interpretedRangeDescription
  :: InterpretedValue
  -> Maybe Range.SuperEllipsisRangeDescription
interpretedRangeDescription value =
  case interpretedForm value of
    RangeForm valueRange -> Just (rangeDescription valueRange)
    NaturalRangeForm valueRange ->
      Just (rangeDescription (naturalRangeAsEvaluatedRange valueRange))
    ValuedNaturalRangeForm valueRange ->
      Just (rangeDescription (valuedNaturalRangeAsEvaluatedRange valueRange))
    _ -> Nothing

interpretedMapFinalOrderType :: InterpretedMap -> Ordinal
interpretedMapFinalOrderType =
  ordinalOrderedValuesOrderType . interpretedMapFinalValues

interpretedMapValueAt
  :: InterpretedMap
  -> Ordinal
  -> Maybe InterpretedValue
interpretedMapValueAt = ordinalOrderedValueAt . interpretedMapFinalValues

-- | Recover ASCII characters from a finite interpreted map. String operators
-- use this after delegating their ordering to the ordinary map operations.
asciiStringFromInterpretedMap :: InterpretedMap -> Maybe String
asciiStringFromInterpretedMap valueMap = do
  cardinality <- naturalAtOrdinal (interpretedMapFinalOrderType valueMap)
  traverse characterAt (finitePositions cardinality)
  where
    characterAt position = do
      value <- interpretedMapValueAt valueMap position
      (_, ordinalValue) <- interpretedExplicitOrdinal value
      characterCode <- naturalAtOrdinal ordinalValue
      guard (characterCode < 256)
      pure (chr (fromIntegral characterCode))

    finitePositions 0 = []
    finitePositions cardinality =
      map finiteOrdinal [0 .. cardinality - 1]

explicitOrdinal :: EvaluatedExplicit -> (Natural, Ordinal)
explicitOrdinal (EvaluatedExplicit level _ value) =
  (level, superEllipsisValueOrdinal value)

explicitInsertion :: EvaluatedExplicit -> SomeSuperEllipsisInsertion
explicitInsertion (EvaluatedExplicit _ _ value) =
  eraseSuperEllipsisInsertion (superEllipsisValueInsertion value)

rangeDescription
  :: EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
rangeDescription (EvaluatedRange _ valueRange) =
  Range.describeSuperEllipsisRange valueRange

evaluatedRangeLevel :: EvaluatedRange -> Natural
evaluatedRangeLevel (EvaluatedRange level _) = level

rangeInsertion :: EvaluatedRange -> SomeSuperEllipsisInsertion
rangeInsertion (EvaluatedRange _ valueRange) =
  eraseSuperEllipsisInsertion
    (Range.superEllipsisRangeInsertion valueRange)

naturalRangeAsEvaluatedRange :: EvaluatedNaturalRange -> EvaluatedRange
naturalRangeAsEvaluatedRange (EvaluatedNaturalRange valueRange) =
  EvaluatedRange 1 (NaturalRange.naturalRangeEllipsisRange valueRange)

valuedNaturalRangeAsEvaluatedRange
  :: EvaluatedValuedNaturalRange
  -> EvaluatedRange
valuedNaturalRangeAsEvaluatedRange
    (EvaluatedValuedNaturalRange valueRange) =
  EvaluatedRange
    1
    (ValuedNaturalRange.valuedNaturalRangeEllipsisRange valueRange)

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
    NaturalRangeForm valueRange ->
      Just [naturalRangeAsEvaluatedRange valueRange]
    ValuedNaturalRangeForm valueRange ->
      Just [valuedNaturalRangeAsEvaluatedRange valueRange]
    RangeConcatenationForm ranges _ -> Just ranges
    _ -> Nothing

emptyInterpretedMap :: InterpretedMap
emptyInterpretedMap = InterpretedMap 0 emptyOrdinalOrderedValues []

singletonMap :: ValueSemantics -> InterpretedValue -> InterpretedMap
singletonMap semantics value =
  InterpretedMap
    1
    (singletonOrdinalOrderedValues value)
    [semantics]
