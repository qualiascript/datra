-- | Hidden implementation of Atlas territories and regions.
module AtlasTerritory.Internal
  ( AtlasTerritoryIndex
  , atlasTerritoryChain
  , atlasTerritory
  , atlasRegion
  ) where

import Atlas.Internal
  ( Atlas
  , atlasDataAt
  , atlasFolio
  , atlasPageElements
  )
import AtlasExtent.Internal
  ( AtlasCellDominion (..)
  )
import Chain
  ( Chain
  , ChainIndex
  )
import Folio (lastChain)
import PageElements.LiquidInternal
  ( SomePageElement (..)
  )
import qualified PageElements.Internal as Elements

-- | A certified index into an Atlas's final genuine page. Lean uses the page
-- cell itself as the index; Haskell retains its chain certificate as well.
type AtlasTerritoryIndex final = ChainIndex final

-- | The final genuine page whose certified indices select territory members.
-- Pair this chain with 'Chain.chainIndex' when starting from an unchecked
-- ordinal; 'atlasTerritory' itself only accepts the resulting witness.
atlasTerritoryChain
  :: Atlas atlasScope scope cellData origin final
  -> Chain final
atlasTerritoryChain = lastChain . atlasFolio

-- | The territory member selected by a certified final-page index.
atlasTerritory
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasTerritory valueAtlas index =
  case Elements.lastPageElement (atlasPageElements valueAtlas) index of
    SomePageElement occurrence ->
      AtlasCellDominion occurrence (atlasDataAt valueAtlas occurrence)

-- | The @n@th region of an Atlas. As in Lean, this is definitionally the
-- corresponding territory member.
atlasRegion
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasRegion = atlasTerritory
