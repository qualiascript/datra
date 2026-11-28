{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | The extent of an Atlas.
module AtlasExtent
  ( AtlasCellDominion
  , atlasCellOriginRankInsertion
  , atlasCellOriginRankAt
  , cellHasOrigin
  , cellTraceHasOrigin
  , cellOriginRankMap
  , cellTraceValid
  , cellNativeTrace
  , extentContainsRank
  , cellContainsRank
  , cellContainsRankDisjoint
  , cellContainsRankInExtent
  , cellContainsRankPreserved
  , withAtlasCellTrace
  , AtlasCellDominionHandler
  , atlasExtent
  , atlasCellDominion
  , atlasCellDominionElement
  , withAtlasCellDominion
  ) where

import AtlasExtent.Internal
  ( AtlasCellDominion
  , atlasCellOriginRankInsertion
  , cellHasOrigin
  , cellOriginRankMap
  , cellTraceValid
  , cellNativeTrace
  , extentContainsRank
  , cellContainsRank
  , cellContainsRankDisjoint
  , cellContainsRankInExtent
  , cellContainsRankPreserved
  , withAtlasCellTrace
  , AtlasCellDominionHandler
  , atlasExtent
  , atlasCellDominionElement
  , withAtlasCellDominion
  )

import qualified AtlasExtent.Internal as Internal (atlasCellDominion, cellTraceHasOrigin, atlasCellOriginRankAt)
import Atlas (Atlas, atlasPageElements, atlasDataAt, atlasAcceptsDatum, mapAtlasData)
import Dominion (rank)
import DomanialInsertion.Core (applyInsertion)
import PageElements (PageElement, somePageElementTraceValid, originPageElement)
import PageElements.Structure (SomePageElement (..), pageElementArrow)

{-@ opaque-reflect rank @-}
{-@ opaque-reflect atlasDataAt @-}

-- | Package a certified cell using its owning Atlas's actual dominion.
{-@ atlasCellDominion :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> {result:AtlasCellDominion s d |
           atlasCellDominionElement result == SomePageElement source
           && somePageElementTraceValid (atlasPageElements owner) (atlasCellDominionElement result)} @-}
atlasCellDominion :: Atlas a s d o f -> PageElement s object -> AtlasCellDominion s d
atlasCellDominion = Internal.atlasCellDominion

{-@ cellTraceHasOrigin :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> {cellHasOrigin owner source} @-}
cellTraceHasOrigin :: Atlas a s d o f -> PageElement s object -> ()
cellTraceHasOrigin = Internal.cellTraceHasOrigin

-- | Retain the exact origin-rank equation through the public interface.
{-@ atlasCellOriginRankAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellHasOrigin owner source && cellTraceValid owner source}
      -> origin:{PageElement s originObject | cellTraceValid owner origin
           && SomePageElement origin == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> {applyInsertion (atlasCellOriginRankInsertion owner source) datum
           == rank (atlasDataAt owner origin)
                (applyInsertion (mapAtlasData owner (pageElementArrow source origin)) datum)} @-}
atlasCellOriginRankAt :: Atlas a s d o f -> PageElement s object
  -> PageElement s originObject -> d object -> ()
atlasCellOriginRankAt = Internal.atlasCellOriginRankAt
