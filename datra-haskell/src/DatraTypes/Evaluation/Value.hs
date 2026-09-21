{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , EvaluatedRange (..)
  , EvaluatedNaturalRange (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , InterpretedAtlasMapFederationPrimitive (..)
  , InterpretedAtlasMapFederation
  , CanonicalResult (..)
  , InterpretedValue (..)
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
import AtlasMapFederation (AtlasMapFederationExpression)
import Data.Char (chr)
import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal)
import DatraLanguage.Diagnostics.Interpreter (InterpretedValueKind (..))
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
import NaturalRange qualified
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

data ValueForm
  = ExplicitForm EvaluatedExplicit
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | NaturalRangeForm EvaluatedNaturalRange
  | RangeConcatenationForm [EvaluatedRange]
  | AsciiStringForm String
  | MapForm

data InsertionCapability
  = NoInsertion
  | ValidInsertion SomeSuperEllipsisInsertion
  | RejectedInsertion Range.SuperEllipsisRangeConcatError

data InterpretedMap = InterpretedMap
  { interpretedMapCardinality :: Natural
  , interpretedMapFinalValues :: OrdinalOrderedValues InterpretedValue
  , interpretedMapComponents :: [CanonicalResult]
  }

-- | Primitive Atlas-map federation kinds understood by the interpreter.
-- The generic construction tree lives in 'AtlasMapFederation'; extending the
-- language with another primitive family only extends this open semantic
-- boundary and its decision procedures.
data InterpretedAtlasMapFederationPrimitive
  = NaturalRangeAtlasMapFederation EvaluatedNaturalRange

type InterpretedAtlasMapFederation =
  AtlasMapFederationExpression
    InterpretedAtlasMapFederationPrimitive
    InterpretedMap

-- | A normalized, source-independent presentation of an evaluated value.
-- Maps contain compact final-page components, so an infinite range remains
-- renderable without attempting to enumerate it.
data CanonicalResult
  = CanonicalExplicit Natural Ordinal
  | CanonicalFormulation Natural
  | CanonicalRange Range.SuperEllipsisRangeDescription
  | CanonicalNaturalRange Natural NaturalRange.NaturalRangeTarget
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalConcatenation [CanonicalResult]
  | CanonicalAsciiString String
  | CanonicalMap Natural [CanonicalResult]
  deriving (Eq, Show)

data InterpretedValue = InterpretedValue
  { interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedAtlasMapFederation :: InterpretedAtlasMapFederation
  , interpretedCanonicalResult :: CanonicalResult
  }

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    NaturalRangeForm _ -> RangeValueKind
    RangeConcatenationForm _ -> RangeConcatenationValueKind
    AsciiStringForm _ -> AsciiStringValueKind
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

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
    NaturalRangeForm valueRange ->
      Just [naturalRangeAsEvaluatedRange valueRange]
    RangeConcatenationForm ranges -> Just ranges
    _ -> Nothing

emptyInterpretedMap :: InterpretedMap
emptyInterpretedMap = InterpretedMap 0 emptyOrdinalOrderedValues []

singletonMap :: CanonicalResult -> InterpretedValue -> InterpretedMap
singletonMap canonical value =
  InterpretedMap
    1
    (singletonOrdinalOrderedValues value)
    [canonical]
