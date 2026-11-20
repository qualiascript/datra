{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | The extent of an Atlas.
module AtlasExtent
  ( AtlasCellDominion
  , atlasCellOriginRankInsertion
  , cellHasOrigin
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
  , withAtlasCellDominion
  ) where

import AtlasExtent.Internal
  ( AtlasCellDominion
  , atlasCellOriginRankInsertion
  , cellHasOrigin
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
  , withAtlasCellDominion
  )
