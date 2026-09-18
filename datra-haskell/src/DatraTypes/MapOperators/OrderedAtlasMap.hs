{-# LANGUAGE TypeFamilies #-}

-- | Possibly-empty Atlas maps with an explicit final-page ordering.
module MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (..)
  , orderedAtlasMapIndexed
  , orderedAtlasMapCardinality
  , orderedAtlasMapValueAt
  , orderedAtlasMapValueAtOrdinal
  , HasOrderedAtlasMap (OrderedAtlasElement, orderedAtlasMap)
  ) where

import Data.Kind (Type)
import DatraOrdinal (Ordinal, finiteOrdinal)
import MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
  )
import Numeric.Natural (Natural)

-- | The ordered map presentation shared by ranges, insertions, and their
-- concatenations.  'IndexedAtlasMap' is intrinsically nonempty, so emptiness
-- is represented once at this boundary instead of being encoded separately
-- by every producer.
data OrderedAtlasMap value
  = EmptyOrderedAtlasMap
  | NonEmptyOrderedAtlasMap (IndexedAtlasMap value)

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
