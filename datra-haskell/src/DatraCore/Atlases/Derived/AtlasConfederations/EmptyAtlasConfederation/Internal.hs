-- | Hidden implementation of the empty Atlas confederation.
module EmptyAtlasConfederation.Internal
  ( EmptyAtlasConfederationScope
  , emptyAtlasConfederation
  ) where

import AtlasConfederation.Internal
  ( AtlasConfederation (..)
  , AtlasMergePresentation (EmptyAtlasMergePresentation)
  )
import Data.Void (Void, absurd)
import Dominion (Dominion, dominion)

-- | Type-level name for the canonical empty confederation.
data EmptyAtlasConfederationScope

emptyDominion :: Dominion Void
emptyDominion = dominion absurd (const Nothing) absurd

-- | The confederation with no tagged components and an 'EmptyAtlas' result.
emptyAtlasConfederation
  :: AtlasConfederation EmptyAtlasConfederationScope Void
emptyAtlasConfederation =
  AtlasConfederation
    emptyDominion
    absurd
    EmptyAtlasMergePresentation
