{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | The extent of an Atlas.
module AtlasExtent
  ( AtlasCellDominion
  , atlasCellOriginRankInsertion
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

import qualified AtlasExtent.Internal as Internal (atlasCellDominion, cellTraceHasOrigin)
import Atlas (Atlas, atlasPageElements)
import PageElements (PageElement, somePageElementTraceValid)
import PageElements.Structure (SomePageElement (..))

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
