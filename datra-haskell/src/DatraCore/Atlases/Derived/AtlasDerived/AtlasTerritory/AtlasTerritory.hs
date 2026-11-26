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
  , atlasTerritoryElement
  , atlasTerritory
  , atlasRegion
  , withAtlasTerritory
  , withAtlasTerritoryOf
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
  , chainIndex
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
  , PageElementArrow
  , pageElementArrow
  , arrowSource
  , arrowTarget
  )
import qualified PageElements.Structure as Trace
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

-- | Retain the exact selected occurrence before hiding its cell carrier.
-- ALIGN: ATLAS-TERRITORY-SELECTED-ELEMENT.
{-@ opaque-reflect atlasTerritoryElement @-}
{-@ atlasTerritoryElement :: owner:Atlas a s d o f
      -> index:{ChainIndex f | chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> {result:SomePageElement s | Elements.somePageElementTraceValid (atlasPageElements owner) result
           && Trace.somePageElementPage result == folioLength (atlasFolio owner) - 1
           && Trace.somePageElementPosition result == chainIndexPosition index} @-}
atlasTerritoryElement :: Atlas a s d o f -> ChainIndex f -> SomePageElement s
atlasTerritoryElement owner index =
  atlasTerritoryChain owner `seq` Elements.lastPageElement (atlasPageElements owner) index

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
  withAtlasTerritory valueAtlas index (atlasCellDominion valueAtlas)

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
{-@ reflect withAtlasTerritory @-}
{-@ withAtlasTerritory :: owner:Atlas a s d o f
      -> index:{ChainIndex f | chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
             && pageElementPage source == folioLength (atlasFolio owner) - 1
             && pageElementPosition source == chainIndexPosition index
             && SomePageElement source == atlasTerritoryElement owner index}
            -> result)
      -> result @-}
withAtlasTerritory
  :: Atlas a s d o f -> AtlasTerritoryIndex f
  -> (forall object. PageElement s object -> result)
  -> result
withAtlasTerritory owner index useTerritory =
  case atlasTerritoryElement owner index of
    SomePageElement source -> useTerritory source

-- | Reconstruct a final occurrence through its owning territory and expose
-- the certified transport from the retained occurrence to that representative.
-- ALIGN: ATLAS-TERRITORY-RECONSTRUCT.
{-@ withAtlasTerritoryOf :: owner:Atlas a s d o f
      -> source:{PageElement s sourceObject | cellTraceValid owner source
           && pageElementPage source == folioLength (atlasFolio owner) - 1}
      -> (forall targetObject. index:{ChainIndex f |
             chainIndex (atlasTerritoryChain owner) (pageElementPosition source) == Just index
             && chainIndexPosition index == pageElementPosition source
             && chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
            -> arrow:{PageElementArrow s sourceObject targetObject |
             arrowSource arrow == source && cellTraceValid owner (arrowTarget arrow)
             && SomePageElement (arrowTarget arrow) == atlasTerritoryElement owner index
             && pageElementPage (arrowTarget arrow) == pageElementPage source
             && pageElementPosition (arrowTarget arrow) == pageElementPosition source}
            -> result)
      -> {resolved:Maybe result | Elements.traceLookupPresent resolved} @-}
withAtlasTerritoryOf
  :: Atlas a s d o f -> PageElement s sourceObject
  -> (forall targetObject. ChainIndex f -> PageElementArrow s sourceObject targetObject -> result)
  -> Maybe result
withAtlasTerritoryOf owner source useTerritory =
  atlasTerritoryChain owner `seq`
  case Elements.finalPageElementIndex (atlasPageElements owner) source of
    Nothing -> Nothing
    Just index -> withAtlasTerritory owner index $ \target ->
      Trace.pageElementTransportedReflexive source `seq`
        Just (useTerritory index (pageElementArrow source target))
