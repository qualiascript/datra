{-# LANGUAGE RankNTypes #-}

-- | Recover the Atlas witness carried by an existential ellipsis range.
module EllipsisRange.Witness
  ( withRangeAtlasWitness
  ) where

import Atlas (AtlasWitness, atlasWitness)
import EllipsisRange (EllipsisRange)
import EmptyAtlas (emptyAtlas)
import MapOperators.IndexedAtlasMap (indexedAtlasAtlas)
import MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (EmptyOrderedAtlasMap, NonEmptyOrderedAtlasMap)
  )
import SuperEllipsisRange (superEllipsisRangeOrderedMap)

withRangeAtlasWitness
  :: EllipsisRange scope
  -> (forall atlasObject. AtlasWitness atlasObject -> result)
  -> result
withRangeAtlasWitness valueRange useWitness =
  case superEllipsisRangeOrderedMap valueRange of
    EmptyOrderedAtlasMap ->
      emptyAtlas (useWitness . atlasWitness)
    NonEmptyOrderedAtlasMap valueMap ->
      useWitness (atlasWitness (indexedAtlasAtlas valueMap))
