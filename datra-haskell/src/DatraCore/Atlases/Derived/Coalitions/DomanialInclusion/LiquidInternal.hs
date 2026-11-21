{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition-dependent assembly for Dominion inclusion.
module DomanialInclusion.LiquidInternal (coalitionComponentInsertion) where

import Atlas (Atlas, AtlasObject)
import Coalition.Element (CoalitionElement, coalitionElementAt)
import DomanialInsertion (DomanialInsertion, domanialInsertion, composeInsertions)
import DomanialInclusion.Data (DominionCellData, dominionCellProjection)
import PageElements (PageElement)

-- | A coalition inverse is defined only on covered values. The component
-- inverse additionally handles arbitrary target data, including uncovered data.
{-@ reflect coalitionElementAt @-}
{-@
coalitionComponentInsertion
  :: targetAtlas:Atlas atlasScope scope cellData origin final
  -> targetOccurrence:PageElement scope object
  -> forward:(a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> backward:(cellData object -> Maybe a)
  -> (value:a -> { backward (coalitionElementAt targetAtlas targetOccurrence
                              (forward value)) == Just value })
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
@-}
-- ALIGN: DOMINC-COMPONENT-INVERSE.
coalitionComponentInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> (cellData object -> Maybe a)
  -> (a -> ())
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
coalitionComponentInsertion targetAtlas targetOccurrence forward backward leftInverse =
  composeInsertions
    (domanialInsertion (coalitionComponentMap targetAtlas targetOccurrence forward) backward
      (coalitionComponentRoundTrip targetAtlas targetOccurrence forward backward leftInverse))
    dominionCellProjection

{-@ reflect coalitionComponentMap @-}
coalitionComponentMap
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> a -> cellData object
coalitionComponentMap targetAtlas targetOccurrence forward value =
  coalitionElementAt targetAtlas targetOccurrence (forward value)

{-@ coalitionComponentRoundTrip
      :: targetAtlas:Atlas atlasScope scope cellData origin final
      -> targetOccurrence:PageElement scope object
      -> forward:(a -> CoalitionElement (AtlasObject atlasScope scope cellData))
      -> backward:(cellData object -> Maybe a)
      -> (value:a -> {backward (coalitionElementAt targetAtlas targetOccurrence (forward value)) == Just value})
      -> value:a
      -> {backward (coalitionComponentMap targetAtlas targetOccurrence forward value) == Just value} @-}
coalitionComponentRoundTrip
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> (cellData object -> Maybe a)
  -> (a -> ()) -> a -> ()
coalitionComponentRoundTrip _ _ _ _ leftInverse value = leftInverse value
