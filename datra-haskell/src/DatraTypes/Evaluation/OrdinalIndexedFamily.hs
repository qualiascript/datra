-- | Canonical ordinal-indexed value families.
--
-- Any semantic ordered Atlas map is an atomic family. A sequential map whose
-- members are such families is their lexicographic product: its first member
-- is the outermost coordinate and its last member varies fastest.
module Evaluation.OrdinalIndexedFamily
  ( OrdinalIndexedFamily (..)
  , ordinalIndexedProductFamily
  , ordinalIndexedValueFamily
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , multiplyOrdinals
  , ordinal
  , ordinalCoefficients
  , ordinalLT
  , subtractOrdinal
  )
import Evaluation.Federation.Structure (sequenceOperands)
import Evaluation.Coalization (coalizeValue)
import Evaluation.Identifier
  ( identifierUnderlyingValue
  , identifierValueAtUnderlying
  )
import Evaluation.Map (makeAtlasMap)
import Evaluation.Value
import Numeric.Natural (Natural)

data OrdinalIndexedFamily = OrdinalIndexedFamily
  { ordinalIndexedFamilyOrderType :: Ordinal
  , ordinalIndexedFamilyValueAt :: Ordinal -> Maybe InterpretedValue
  }

-- | Recognize values with a canonical ordinal order. Limit endpoints such as
-- @from 0 to Infinity@ still do not enter this fragment: they are coalized
-- composites and therefore do not expose an ordered Atlas-map view.
ordinalIndexedValueFamily
  :: InterpretedValue
  -> Maybe OrdinalIndexedFamily
ordinalIndexedValueFamily value =
  case identifierUnderlyingValue value of
    Just underlying -> do
      family <- ordinalIndexedValueFamily underlying
      pure family
        { ordinalIndexedFamilyValueAt = \position -> do
            selected <- ordinalIndexedFamilyValueAt family position
            identifierValueAtUnderlying value selected
        }
    Nothing -> case interpretedForm value of
      CoalizationForm operand -> do
        family <- ordinalIndexedValueFamily operand
        pure family
          { ordinalIndexedFamilyValueAt =
              fmap coalizeValue . ordinalIndexedFamilyValueAt family
          }
      SequentialMapForm -> do
        members <- sequenceOperands value
        productFamily <$> traverse ordinalIndexedValueFamily members
      EitherForm alternatives -> do
        left <- ordinalIndexedValueFamily (evaluatedEitherLeft alternatives)
        right <- ordinalIndexedValueFamily (evaluatedEitherRight alternatives)
        pure (sumFamily left right)
      _ -> atomicFamily value

-- | Form the lexicographic product without first erasing its components into
-- an Atlas map. This matters for infinite coordinates: the map's flattened
-- order cannot be inspected as a finite list, while the component values can
-- each expose their own ordinal-indexed capability directly.
ordinalIndexedProductFamily
  :: [InterpretedValue]
  -> Maybe OrdinalIndexedFamily
ordinalIndexedProductFamily values =
  productFamily <$> traverse ordinalIndexedValueFamily values

atomicFamily :: InterpretedValue -> Maybe OrdinalIndexedFamily
atomicFamily value = do
  values <- orderedAtlasMapView value
  let orderType = ordinalOrderedValuesOrderType values
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

sumFamily
  :: OrdinalIndexedFamily
  -> OrdinalIndexedFamily
  -> OrdinalIndexedFamily
sumFamily left right = OrdinalIndexedFamily
  { ordinalIndexedFamilyOrderType =
      addOrdinals leftOrder rightOrder
  , ordinalIndexedFamilyValueAt = \position ->
      if ordinalLT position leftOrder
        then ordinalIndexedFamilyValueAt left position
        else do
          rightPosition <- subtractOrdinal leftOrder position
          ordinalIndexedFamilyValueAt right rightPosition
  }
  where
    leftOrder = ordinalIndexedFamilyOrderType left
    rightOrder = ordinalIndexedFamilyOrderType right

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
