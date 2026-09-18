{-# LANGUAGE TypeFamilies #-}

-- | Possibly-empty Atlas maps with an explicit final-page ordering.
module MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (..)
  , orderedAtlasMapIndexed
  , HasOrderedAtlasMap (OrderedAtlasElement, orderedAtlasMap)
  ) where

import Data.Kind (Type)
import MapOperators.IndexedAtlasMap (IndexedAtlasMap)

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

-- | A value with an ordered Atlas-map presentation.
class HasOrderedAtlasMap operand where
  type OrderedAtlasElement operand :: Type
  orderedAtlasMap :: operand -> OrderedAtlasMap (OrderedAtlasElement operand)

instance HasOrderedAtlasMap (IndexedAtlasMap value) where
  type OrderedAtlasElement (IndexedAtlasMap value) = value
  orderedAtlasMap = NonEmptyOrderedAtlasMap
