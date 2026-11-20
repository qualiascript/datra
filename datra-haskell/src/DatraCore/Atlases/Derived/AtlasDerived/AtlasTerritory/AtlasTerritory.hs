{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Atlas territories and regions through their checked cell interfaces.
module AtlasTerritory
  ( AtlasTerritoryIndex
  , atlasTerritoryChain
  , atlasTerritory
  , atlasRegion
  , withAtlasTerritory
  ) where

import Atlas
  ( Atlas
  , atlasFolio
  , atlasPageElements
  )
import AtlasExtent (AtlasCellDominion, atlasCellDominion, cellTraceValid)
import Chain
  ( Chain
  , ChainIndex
  , chainPosition
  , chainObjectAt
  , chainIndexPosition
  )
import Folio (lastChain, folioLength)
import PageElements.Structure
  ( SomePageElement (..)
  , PageElement
  , pageElementPage
  , pageElementPosition
  )
import qualified PageElements as Elements

-- | A certified index into an Atlas's final genuine page. Lean uses the page
-- cell itself as the index; Haskell retains its chain certificate as well.
type AtlasTerritoryIndex final = ChainIndex final

-- | The final genuine page whose certified indices select territory members.
-- Pair this chain with 'Chain.chainIndex' when starting from an unchecked
-- ordinal; 'atlasTerritory' itself only accepts the resulting witness.
{-@ opaque-reflect atlasTerritoryChain @-}
{-@ atlasTerritoryChain :: owner:Atlas a s d o f
      -> {result:Chain f | result == lastChain (atlasFolio owner)} @-}
atlasTerritoryChain
  :: Atlas atlasScope scope cellData origin final
  -> Chain final
atlasTerritoryChain owner = lastChain (atlasFolio owner)

-- | The territory member selected by a certified final-page index.
-- ALIGN: ATLAS-TERRITORY-INTERPRETATION.
{-@ atlasTerritory :: owner:Atlas a s d o f
      -> index:{ChainIndex f | chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> AtlasCellDominion s d @-}
atlasTerritory
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasTerritory valueAtlas index =
  atlasTerritoryChain valueAtlas `seq`
  case Elements.lastPageElement (atlasPageElements valueAtlas) index of
    SomePageElement occurrence ->
      atlasCellDominion valueAtlas occurrence

-- | The @n@th region of an Atlas. As in Lean, this is definitionally the
-- corresponding territory member.
{-@ atlasRegion :: owner:Atlas a s d o f
      -> index:{ChainIndex f | chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> AtlasCellDominion s d @-}
atlasRegion
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasRegion = atlasTerritory

-- | Consume a territory's certified cell. Its owning Atlas supplies the
-- membership-refined dominion through 'Atlas.atlasDataAt'.
-- ALIGN: ATLAS-TERRITORY-POSITION.
{-@ withAtlasTerritory :: owner:Atlas a s d o f
      -> index:{ChainIndex f | chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
             && pageElementPage source == folioLength (atlasFolio owner) - 1
             && pageElementPosition source == chainIndexPosition index}
            -> result)
      -> result @-}
withAtlasTerritory
  :: Atlas a s d o f -> AtlasTerritoryIndex f
  -> (forall object. PageElement s object -> result)
  -> result
withAtlasTerritory owner index useTerritory =
  atlasTerritoryChain owner `seq`
  case Elements.lastPageElement (atlasPageElements owner) index of
    SomePageElement source -> useTerritory source
