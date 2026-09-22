{-# LANGUAGE TypeFamilies #-}

-- | Possibly-empty Atlas maps with an explicit final-page ordering.
module MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (..)
  , OrdinalOrderedValues (..)
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  , appendOrdinalOrderedValues
  , orderedAtlasMapIndexed
  , orderedAtlasMapCardinality
  , orderedAtlasMapValueAt
  , orderedAtlasMapValueAtOrdinal
  , HasOrderedAtlasMap (OrderedAtlasElement, orderedAtlasMap)
  ) where

import Data.Kind (Type)
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  )
import MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
  )
import Numeric.Natural (Natural)
import OrdinalSequence
  ( OrdinalSequence (..)
  , appendOrdinalSequence
  , emptyOrdinalSequence
  , singletonOrdinalSequence
  )

-- | The ordered map presentation shared by ranges, insertions, and their
-- concatenations.  'IndexedAtlasMap' is intrinsically nonempty, so emptiness
-- is represented once at this boundary instead of being encoded separately
-- by every producer.
data OrderedAtlasMap value
  = EmptyOrderedAtlasMap
  | NonEmptyOrderedAtlasMap (IndexedAtlasMap value)

-- | A lightweight ordinal-indexed ordering used after existential Atlas
-- witnesses have been erased. Unlike 'OrderedAtlasMap', this representation
-- can also describe transfinite sequences without exposing their source type.
data OrdinalOrderedValues value = OrdinalOrderedValues
  { ordinalOrderedValuesOrderType :: Ordinal
  , ordinalOrderedValueAt :: Ordinal -> Maybe value
  }

emptyOrdinalOrderedValues :: OrdinalOrderedValues value
emptyOrdinalOrderedValues = fromOrdinalSequence emptyOrdinalSequence

singletonOrdinalOrderedValues :: value -> OrdinalOrderedValues value
singletonOrdinalOrderedValues =
  fromOrdinalSequence . singletonOrdinalSequence

appendOrdinalOrderedValues
  :: OrdinalOrderedValues value
  -> OrdinalOrderedValues value
  -> OrdinalOrderedValues value
appendOrdinalOrderedValues left right =
  fromOrdinalSequence
    (appendOrdinalSequence
      (toOrdinalSequence left)
      (toOrdinalSequence right))

toOrdinalSequence :: OrdinalOrderedValues value -> OrdinalSequence value
toOrdinalSequence values =
  OrdinalSequence
    (ordinalOrderedValuesOrderType values)
    (ordinalOrderedValueAt values)

fromOrdinalSequence :: OrdinalSequence value -> OrdinalOrderedValues value
fromOrdinalSequence values =
  OrdinalOrderedValues
    (ordinalSequenceOrderType values)
    (ordinalSequenceValueAt values)

orderedAtlasMapIndexed :: OrderedAtlasMap value -> Maybe (IndexedAtlasMap value)
orderedAtlasMapIndexed EmptyOrderedAtlasMap = Nothing
orderedAtlasMapIndexed (NonEmptyOrderedAtlasMap valueMap) = Just valueMap

orderedAtlasMapCardinality :: OrderedAtlasMap value -> Ordinal
orderedAtlasMapCardinality EmptyOrderedAtlasMap = finiteOrdinal 0
orderedAtlasMapCardinality (NonEmptyOrderedAtlasMap valueMap) =
  indexedAtlasCardinality valueMap

orderedAtlasMapValueAt
  :: OrderedAtlasMap value
  -> Natural
  -> Maybe value
orderedAtlasMapValueAt EmptyOrderedAtlasMap _ = Nothing
orderedAtlasMapValueAt (NonEmptyOrderedAtlasMap valueMap) position =
  indexedAtlasValueAt valueMap position

orderedAtlasMapValueAtOrdinal
  :: OrderedAtlasMap value
  -> Ordinal
  -> Maybe value
orderedAtlasMapValueAtOrdinal EmptyOrderedAtlasMap _ = Nothing
orderedAtlasMapValueAtOrdinal
    (NonEmptyOrderedAtlasMap valueMap) position =
  indexedAtlasValueAtOrdinal valueMap position

-- | A value with an ordered Atlas-map presentation.
class HasOrderedAtlasMap operand where
  type OrderedAtlasElement operand :: Type
  orderedAtlasMap :: operand -> OrderedAtlasMap (OrderedAtlasElement operand)

instance HasOrderedAtlasMap (IndexedAtlasMap value) where
  type OrderedAtlasElement (IndexedAtlasMap value) = value
  orderedAtlasMap = NonEmptyOrderedAtlasMap

instance HasOrderedAtlasMap (OrderedAtlasMap value) where
  type OrderedAtlasElement (OrderedAtlasMap value) = value
  orderedAtlasMap = id
