-- | Canonical ordinal-indexed value families.
--
-- Any semantic ordered Atlas map of order type at most @omega@ is an atomic
-- family. A sequential map whose members are all such families is their
-- lexicographic product: its first member is the outermost coordinate and its
-- last member varies fastest.
module Evaluation.OrdinalIndexedFamily
  ( OrdinalIndexedFamily (..)
  , ordinalIndexedValueFamily
  ) where

import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , multiplyOrdinals
  , omega
  , ordinal
  , ordinalCoefficients
  , ordinalLTE
  )
import Evaluation.Federation.Structure (sequenceOperands)
import Evaluation.Map (makeAtlasMap)
import Evaluation.Value
import Numeric.Natural (Natural)

data OrdinalIndexedFamily = OrdinalIndexedFamily
  { ordinalIndexedFamilyOrderType :: Ordinal
  , ordinalIndexedFamilyValueAt :: Ordinal -> Maybe InterpretedValue
  }

-- | Recognize the closed fragment whose values have a canonical ordinal
-- order. Limit endpoints such as @from 0 to Infinity@ deliberately do not
-- enter this fragment: they are coalized composites, not valued-range forms.
ordinalIndexedValueFamily
  :: InterpretedValue
  -> Maybe OrdinalIndexedFamily
ordinalIndexedValueFamily value =
  case interpretedForm value of
    SequentialMapForm -> do
      members <- sequenceOperands value
      productFamily <$> traverse ordinalIndexedValueFamily members
    _ -> atomicFamily value

atomicFamily :: InterpretedValue -> Maybe OrdinalIndexedFamily
atomicFamily value = do
  values <- orderedAtlasMapView value
  let orderType = ordinalOrderedValuesOrderType values
  if ordinalLTE orderType omega then pure () else Nothing
  pure OrdinalIndexedFamily
    { ordinalIndexedFamilyOrderType = orderType
    , ordinalIndexedFamilyValueAt = ordinalOrderedValueAt values
    }

productFamily :: [OrdinalIndexedFamily] -> OrdinalIndexedFamily
productFamily members = OrdinalIndexedFamily
  { ordinalIndexedFamilyOrderType = componentFamilyOrderType components
  , ordinalIndexedFamilyValueAt = \position ->
      makeProductWitness <$> componentFamilyValueAt components position
  }
  where
    components = componentFamily members
    makeProductWitness [] = makeAtlasMap 0 []
    makeProductWitness values = makeAtlasMap 2 values

data ComponentFamily = ComponentFamily
  { componentFamilyOrderType :: Ordinal
  , componentFamilyValueAt :: Ordinal -> Maybe [InterpretedValue]
  }

-- The lexicographic product A x B has B as its contiguous block, hence order
-- type |B| * |A|. Primitive coordinates have finite or omega order, so finite
-- products remain monomials below omega^omega.
componentFamily :: [OrdinalIndexedFamily] -> ComponentFamily
componentFamily [] = ComponentFamily
  { componentFamilyOrderType = finiteOrdinal 1
  , componentFamilyValueAt = \position ->
      if position == finiteOrdinal 0 then Just [] else Nothing
  }
componentFamily (outer : remaining) = ComponentFamily
  { componentFamilyOrderType =
      multiplyOrdinals tailOrder outerOrder
  , componentFamilyValueAt = \position -> do
      (outerPosition, tailPosition) <-
        splitOrdinalBlock tailOrder position
      outerValue <- ordinalIndexedFamilyValueAt outer outerPosition
      tailValues <- componentFamilyValueAt tailFamily tailPosition
      pure (outerValue : tailValues)
  }
  where
    tailFamily = componentFamily remaining
    tailOrder = componentFamilyOrderType tailFamily
    outerOrder = ordinalIndexedFamilyOrderType outer

-- For a block c*omega^k, quotient and remainder are obtained from the
-- degree-k coefficient. The quotient is finite because every primitive
-- coordinate is indexed below omega.
splitOrdinalBlock
  :: Ordinal
  -> Ordinal
  -> Maybe (Ordinal, Ordinal)
splitOrdinalBlock block position = do
  (coefficient, width) <- monomial block
  let positionCoefficients = ordinalCoefficients position
  if length positionCoefficients > width
    then Nothing
    else
      let padded =
            replicate (width - length positionCoefficients) 0
              <> positionCoefficients
          leading = case padded of
            value : _ -> value
            [] -> 0
          trailing = case padded of
            _ : values -> values
            [] -> []
      in Just
          ( finiteOrdinal (leading `div` coefficient)
          , ordinal ((leading `mod` coefficient) : trailing)
          )

monomial :: Ordinal -> Maybe (Natural, Int)
monomial value =
  case ordinalCoefficients value of
    coefficient : remaining
      | coefficient > 0
      , all (== 0) remaining ->
          Just (coefficient, 1 + length remaining)
    _ -> Nothing
