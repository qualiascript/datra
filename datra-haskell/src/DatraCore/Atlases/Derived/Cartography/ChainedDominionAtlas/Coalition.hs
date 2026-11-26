{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Canonical coalition data retaining the value in the chained extent.
module ChainedDominionAtlas.Coalition
  ( chainedDominionCoalitionElement, chainedCoalitionValue ) where

import Atlas (atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import ChainedDominionAtlas.Coverage (chainedDominionCoverage)
import ChainedDominionAtlas.Data (ChainedDominionCellData (..), cellValue)
import ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, chainedDominionAtlas, chainedDominionMembership )
import Coalition.Element
  ( CoalitionData, CoalitionView (..), viewCoalitionElement, coalitionElement
  , coalitionElementView, coalitionElementSource, coalitionElementValid )
import PageElements (PageElement, originPageElement, withPageElement)
import PageElements.Structure (SomePageElement (..))

-- ALIGN: CHAINED-COALITION-VALUE.
{-@ reflect chainedCoalitionValue @-}
chainedCoalitionValue :: CoalitionData owner scope (ChainedDominionCellData value) -> value
chainedCoalitionValue element = chainedViewValue (viewCoalitionElement element)

-- ALIGN: CHAINED-COALITION-VIEW-VALUE.
{-@ reflect chainedViewValue @-}
chainedViewValue :: CoalitionView scope (ChainedDominionCellData value) -> value
chainedViewValue (CoalitionView _ datum) = cellValue datum

-- ALIGN: CHAINED-OWNER-COALITION.
-- ALIGN: CHAINED-COALITION-VALUE-ROUNDTRIP.
{-@ opaque-reflect chainedDominionCoalitionElement @-}
{-@ chainedDominionCoalitionElement :: owner:ChainedDominionAtlas ownerScope scope value -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))} @-}
chainedDominionCoalitionElement :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
chainedDominionCoalitionElement owner value =
  withPageElement (originPageElement (atlasPageElements (chainedDominionAtlas owner))) $ \origin ->
    chainedCoalitionAt owner origin value

-- ALIGN: CHAINED-COALITION-AT.
{-@ chainedCoalitionAt :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source
           && SomePageElement source == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == SomePageElement source} @-}
chainedCoalitionAt :: ChainedDominionAtlas ownerScope scope value -> PageElement scope object -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
chainedCoalitionAt owner source value =
  let valueAtlas = chainedDominionAtlas owner
      datum = ChainedDominionExtentDatum value
  in chainedDominionMembership owner source datum `seq`
     let witness = chainedDominionCoverage owner source datum
     in coalitionElementView valueAtlas source datum witness `seq`
        coalitionElement valueAtlas source datum witness
