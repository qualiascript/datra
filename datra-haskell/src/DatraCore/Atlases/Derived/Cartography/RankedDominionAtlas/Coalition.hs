{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Ranked coalitions retain the original Dominion rank in their cache.
module RankedDominionAtlas.Coalition
  ( rankedDominionCoalitionElement, rankedCoalitionForward, rankedCoalitionBackward
  , rankedCoalitionInsertion ) where

import Atlas (atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (coverageWitnessRankMatches)
import Coalition.Element
  ( CoalitionData, coalitionElement, coalitionElementRank, coalitionElementSource
  , coalitionElementValid, coalitionUnitInsertion )
import Dominion (rank, unrank, dominionCoherence)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (PageElement, originPageElement, withPageElement)
import PageElements.Structure (SomePageElement (..))
import RankedDominionAtlas.Coverage (rankedDominionCoverage, rankedOriginImageRank)
import RankedDominionAtlas.Data (RankedDominionCellData (..), cellValue)
import RankedDominionAtlas.Owner
  ( RankedDominionAtlas, rankedDominionAtlas, rankedDominionValueDominion, rankedDominionMembership )
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)

-- ALIGN: RANKED-OWNER-COALITION.
{-@ opaque-reflect rankedDominionCoalitionElement @-}
-- ALIGN: RANKED-COALITION-RANK.
{-@ rankedDominionCoalitionElement :: owner:RankedDominionAtlas ownerScope value -> value:value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementRank element == rank (rankedDominionValueDominion owner) value
           && coalitionElementValid (rankedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (rankedDominionAtlas owner))} @-}
rankedDominionCoalitionElement :: RankedDominionAtlas ownerScope value -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedDominionCoalitionElement owner value =
  withPageElement (originPageElement (atlasPageElements (rankedDominionAtlas owner))) $ \origin ->
    rankedCoalitionAt owner origin value

{-@ rankedCoalitionAt :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) source
           && SomePageElement source == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> value:value
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementRank element == rank (rankedDominionValueDominion owner) value
           && coalitionElementValid (rankedDominionAtlas owner) element
           && coalitionElementSource element == SomePageElement source} @-}
rankedCoalitionAt :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedCoalitionAt owner source value =
  let valueAtlas = rankedDominionAtlas owner
      datum = RankedDominionExtentDatum value
  in rankedDominionMembership owner source datum `seq`
     let witness = rankedDominionCoverage owner source datum
     in rankedOriginImageRank owner source datum `seq`
        coverageWitnessRankMatches valueAtlas source datum witness `seq`
        coalitionElement valueAtlas source datum witness

{-@ reflect rankedCoalitionForward @-}
-- ALIGN: RANKED-COALITION-FORWARD.
{-@ rankedCoalitionForward :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementRank element == rank (rankedDominionValueDominion owner) (applyInsertion insertion value)
           && coalitionElementValid (rankedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (rankedDominionAtlas owner))} @-}
rankedCoalitionForward :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value -> source
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedCoalitionForward owner insertion value = rankedDominionCoalitionElement owner (applyInsertion insertion value)

-- Decode the cached rank even for raw, uncertified coalition records.
{-@ reflect rankedCoalitionBackward @-}
-- ALIGN: RANKED-COALITION-BACKWARD.
{-@ rankedCoalitionBackward :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
      -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
      -> Maybe source @-}
rankedCoalitionBackward :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) -> Maybe source
rankedCoalitionBackward owner insertion element =
  case unrank (rankedDominionValueDominion owner) (coalitionElementRank element) of
    Nothing -> Nothing
    Just value -> preimage insertion value

-- ALIGN: RANKED-COALITION-ROUNDTRIP.
{-@ rankedCoalitionRoundTrip :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {rankedCoalitionBackward owner insertion (rankedCoalitionForward owner insertion value) == Just value} @-}
rankedCoalitionRoundTrip :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value -> source -> ()
rankedCoalitionRoundTrip owner insertion value =
  rankedCoalitionForward owner insertion value `seq`
  dominionCoherence (rankedDominionValueDominion owner) (applyInsertion insertion value) `seq`
  insertionLeftInverse insertion value

-- ALIGN: RANKED-COALITION-INSERTION.
{-@ rankedCoalitionInsertion :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value
      -> {result:DomanialInsertion source
           ({element:CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
             coalitionElementValid (rankedDominionAtlas owner) element
             && coalitionElementSource element == originPageElement (atlasPageElements (rankedDominionAtlas owner))}) |
           applyInsertion result == rankedCoalitionForward owner insertion
           && preimage result == rankedCoalitionBackward owner insertion} @-}
rankedCoalitionInsertion :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> DomanialInsertion source (CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value))
rankedCoalitionInsertion owner insertion =
  let valueAtlas = rankedDominionAtlas owner
  in coalitionUnitInsertion (coalitionElementValid valueAtlas) coalitionElementSource
       (originPageElement (atlasPageElements valueAtlas))
       (rankedCoalitionForward owner insertion) (rankedCoalitionBackward owner insertion)
       (rankedCoalitionRoundTrip owner insertion)
