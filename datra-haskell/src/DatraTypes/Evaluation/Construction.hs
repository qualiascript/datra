-- | Total constructors for primitive evaluated Datra values.
module Evaluation.Construction
  ( makeNatural
  , makeExplicit
  , makeExplicitValue
  , makeFormulation
  , mapFromInsertion
  ) where

import DatraOrdinal (Ordinal, finiteOrdinal)
import Evaluation.Value
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand (someSuperEllipsis)
import SuperEllipsisValue
  ( canonicalSuperEllipsisValue
  , minimumSuperEllipsisValueRank
  )
import SuperEllipsisInsertion
  ( fullSomeSuperEllipsisInsertion
  , someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  )

makeNatural :: Natural -> InterpretedValue
makeNatural = makeExplicit NaturalOrigin . finiteOrdinal

makeExplicit :: ExplicitOrigin -> Ordinal -> InterpretedValue
makeExplicit origin = explicitInterpretedValue . makeExplicitValue origin

makeExplicitValue :: ExplicitOrigin -> Ordinal -> EvaluatedExplicit
makeExplicitValue origin ordinalValue =
  canonicalSuperEllipsisValue ordinalValue $ \value ->
    EvaluatedExplicit level origin value
  where
    level = minimumSuperEllipsisValueRank ordinalValue

explicitInterpretedValue :: EvaluatedExplicit -> InterpretedValue
explicitInterpretedValue explicitValue = value
  where
    (level, ordinalValue) = explicitOrdinal explicitValue
    insertion = explicitInsertion explicitValue
    canonical = CanonicalExplicit level ordinalValue
    value =
      InterpretedValue
        (ExplicitForm explicitValue)
        (ValidInsertion insertion)
        (singletonMap canonical value)
        canonical

makeFormulation :: Natural -> InterpretedValue
makeFormulation level = value
  where
    formulation = someSuperEllipsis level
    insertion = fullSomeSuperEllipsisInsertion level
    values =
      OrdinalOrderedValues
        (someSuperEllipsisInsertionOrderType insertion)
        (\position -> do
          absolute <- someSuperEllipsisInsertionPositionAt insertion position
          pure (makeExplicit ComputedOrigin absolute))
    value =
      InterpretedValue
        (FormulationForm formulation)
        (ValidInsertion insertion)
        (InterpretedMap 1 values [canonical])
        canonical
    canonical = CanonicalFormulation level

mapFromInsertion
  :: SomeSuperEllipsisInsertion
  -> [CanonicalResult]
  -> InterpretedMap
mapFromInsertion insertion components =
  InterpretedMap
    (if isEmpty then 0 else 1)
    (OrdinalOrderedValues
      (someSuperEllipsisInsertionOrderType insertion)
      (\position -> do
        absolute <- someSuperEllipsisInsertionPositionAt insertion position
        pure (makeExplicit ComputedOrigin absolute)))
    (if isEmpty then [] else components)
  where
    isEmpty =
      someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0
