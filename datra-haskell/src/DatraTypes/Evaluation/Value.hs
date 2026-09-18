{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , EvaluatedRange (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , CanonicalResult (..)
  , InterpretedValue (..)
  , interpretedValueKind
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , explicitOrdinal
  , explicitInsertion
  , rangeDescription
  , evaluatedRangeLevel
  , rangeInsertion
  , valueRanges
  , emptyInterpretedMap
  , singletonMap
  , emptyOrdinalOrderedValues
  , appendOrdinalOrderedValues
  , appendSomeSuperEllipsisInsertion
  ) where

import DatraOrdinal (Ordinal)
import Diagnostics.Interpreter (InterpretedValueKind (..))
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
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

data ValueForm
  = ExplicitForm EvaluatedExplicit
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | RangeConcatenationForm [EvaluatedRange]
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

-- | A normalized, source-independent presentation of an evaluated value.
-- Maps contain compact final-page components, so an infinite range remains
-- renderable without attempting to enumerate it.
data CanonicalResult
  = CanonicalExplicit Natural Ordinal
  | CanonicalFormulation Natural
  | CanonicalRange Range.SuperEllipsisRangeDescription
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalSuperEllipsisInsertion
  deriving (Eq, Show)

data InterpretedValue = InterpretedValue
  { interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedCanonicalResult :: CanonicalResult
  }

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    RangeConcatenationForm _ -> RangeConcatenationValueKind
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
    _ -> Nothing

interpretedMapFinalOrderType :: InterpretedMap -> Ordinal
interpretedMapFinalOrderType =
  ordinalOrderedValuesOrderType . interpretedMapFinalValues

interpretedMapValueAt
  :: InterpretedMap
  -> Ordinal
  -> Maybe InterpretedValue
interpretedMapValueAt = ordinalOrderedValueAt . interpretedMapFinalValues

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

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
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
