{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , EvaluatedRange (..)
  , EvaluatedNaturalRange (..)
  , EvaluatedValuedNaturalRange (..)
  , InterpretedTotalAtlasMap (..)
  , EvaluatedAtlasMapFederationMember (..)
  , EvaluatedSpecification (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , interpretedMapCardinality
  , InterpretedAtlasMapFederationPrimitive (..)
  , InterpretedAtlasMapFederation
  , ValueSemantics (..)
  , CanonicalResult (..)
  , InterpretedValue
  , InterpretedValueTotality (..)
  , makeInterpretedValue
  , makeSingletonInterpretedValue
  , interpretedForm
  , interpretedInsertionCapability
  , interpretedMap
  , interpretedAtlasMapFederation
  , interpretedTotalAtlasMap
  , interpretedSemantics
  , interpretedValueHasTotalMap
  , interpretedCanonicalResult
  , interpretedValueKind
  , interpretedExplicitOrdinal
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
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (SingletonAtlasMapFederation) )
import Data.Char (chr)
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import Evaluation.Error (InterpretedValueKind (..))
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
import NaturalRange qualified
import ValuedNaturalRange qualified
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

data ValueForm
  = ExplicitForm EvaluatedExplicit
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | NaturalRangeForm EvaluatedNaturalRange
  | ValuedNaturalRangeForm EvaluatedValuedNaturalRange
  | RangeConcatenationForm
      [EvaluatedRange]
      (Maybe (InterpretedValue, InterpretedValue))
  | AsciiStringForm String
  | SpecificationForm EvaluatedSpecification
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

-- | Primitive Atlas-map federation kinds understood by the interpreter.
-- The generic construction tree lives in 'AtlasMapFederation'; extending the
-- language with another primitive family only extends this open semantic
-- boundary and its decision procedures.
data InterpretedAtlasMapFederationPrimitive
  = NaturalRangeAtlasMapFederation EvaluatedNaturalRange
  | ValuedNaturalRangeAtlasMapFederation EvaluatedValuedNaturalRange

type InterpretedAtlasMapFederation =
  AtlasMapFederationExpression
    InterpretedAtlasMapFederationPrimitive
    InterpretedMap

-- | Semantic provenance retained after existential Atlas witnesses have been
-- erased. Evaluation modules inspect this structure; presentation is derived
-- separately as 'CanonicalResult'.
data ValueSemantics
  = ExplicitSemantics Natural Ordinal
  | FormulationSemantics Natural
  | RangeSemantics Range.SuperEllipsisRangeDescription
  | NaturalRangeSemantics Natural NaturalRange.NaturalRangeTarget
  | ValuedNaturalRangeSemantics Natural NaturalRange.NaturalRangeTarget
  | NaturalTypeSemantics
  | RangeConcatenationSemantics [Range.SuperEllipsisRangeDescription]
  | ConcatenationSemantics [ValueSemantics]
  | AsciiStringSemantics String
  | MapSemantics Natural [ValueSemantics]
  | SpecificationSemantics ValueSemantics ValueSemantics

-- | A normalized, source-independent presentation of an evaluated value.
data CanonicalResult
  = CanonicalExplicit Natural Ordinal
  | CanonicalFormulation Natural
  | CanonicalRange Range.SuperEllipsisRangeDescription
  | CanonicalNaturalRange Natural NaturalRange.NaturalRangeTarget
  | CanonicalValuedNaturalRange Natural NaturalRange.NaturalRangeTarget
  | CanonicalNaturalType
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalConcatenation [CanonicalResult]
  | CanonicalAsciiString String
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalSpecification CanonicalResult CanonicalResult
  deriving (Eq, Show)

data InterpretedValue = InterpretedValue
  { interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedAtlasMapFederation :: InterpretedAtlasMapFederation
  , interpretedTotalAtlasMap :: Maybe InterpretedTotalAtlasMap
  , interpretedSemantics :: ValueSemantics
  }

data InterpretedValueTotality = TotalInterpretedMap | NonTotalInterpretedMap

makeInterpretedValue
  :: ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedAtlasMapFederation
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeInterpretedValue form capability valueMap federation totality semantics =
  InterpretedValue
    { interpretedForm = form
    , interpretedInsertionCapability = capability
    , interpretedMap = valueMap
    , interpretedAtlasMapFederation = federation
    , interpretedTotalAtlasMap =
        case totality of
          TotalInterpretedMap -> Just (InterpretedTotalAtlasMap valueMap)
          NonTotalInterpretedMap -> Nothing
    , interpretedSemantics = semantics
    }

makeSingletonInterpretedValue
  :: ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeSingletonInterpretedValue form capability valueMap totality =
  makeInterpretedValue
    form
    capability
    valueMap
    (SingletonAtlasMapFederation valueMap)
    totality

interpretedValueHasTotalMap :: InterpretedValue -> Bool
interpretedValueHasTotalMap = maybe False (const True) . interpretedTotalAtlasMap

interpretedCanonicalResult :: InterpretedValue -> CanonicalResult
interpretedCanonicalResult = canonicalResult . interpretedSemantics

canonicalResult :: ValueSemantics -> CanonicalResult
canonicalResult semantics =
  case semantics of
    ExplicitSemantics level value -> CanonicalExplicit level value
    FormulationSemantics level -> CanonicalFormulation level
    RangeSemantics description -> CanonicalRange description
    NaturalRangeSemantics start target -> CanonicalNaturalRange start target
    ValuedNaturalRangeSemantics start target ->
      CanonicalValuedNaturalRange start target
    NaturalTypeSemantics -> CanonicalNaturalType
    RangeConcatenationSemantics descriptions ->
      CanonicalRangeConcatenation descriptions
    ConcatenationSemantics members ->
      CanonicalConcatenation (map canonicalResult members)
    AsciiStringSemantics characters -> CanonicalAsciiString characters
    MapSemantics cardinality components ->
      CanonicalMap cardinality (map canonicalResult components)
    SpecificationSemantics source target ->
      CanonicalSpecification (canonicalResult source) (canonicalResult target)

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    NaturalRangeForm _ -> RangeValueKind
    ValuedNaturalRangeForm _ -> RangeValueKind
    RangeConcatenationForm _ _ -> RangeConcatenationValueKind
    AsciiStringForm _ -> AsciiStringValueKind
    SpecificationForm _ -> SpecificationValueKind
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
