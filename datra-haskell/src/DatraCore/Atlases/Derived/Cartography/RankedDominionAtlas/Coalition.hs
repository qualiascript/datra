{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}

-- | Ranked coalitions retain the original Dominion rank in their cache.
module RankedDominionAtlas.Coalition
  ( rankedDominionCoalitionElement, rankedCoalitionForward, rankedCoalitionBackward
  , rankedCoalitionInsertion, rankedComponentBackward, rankedComponentLeftInverse ) where

import Atlas (atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (coverageWitnessRankMatches)
import Coalition.Element
  ( CoalitionData, coalitionElement, coalitionElementRank, coalitionElementSource
  , coalitionElementValid, coalitionUnitInsertion, coalitionElementAt, coalitionElementReaches )
import Dominion (rank, unrank, dominionCoherence)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (PageElement, originPageElement, withPageElement)
import PageElements.Structure (SomePageElement (..), pageElementTransportedReflexive)
import RankedDominionAtlas.Coverage (rankedDominionCoverage, rankedOriginImageRank)
import RankedDominionAtlas.Data (RankedDominionCellData (..), cellValue)
import RankedDominionAtlas.Owner
  ( RankedDominionAtlas, rankedDominionAtlas, rankedDominionValueDominion, rankedDominionMembership )
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)

-- ALIGN: RANKED-OWNER-COALITION.
{-@ opaque-reflect rankedDominionCoalitionElement @-}
-- ALIGN: RANKED-COALITION-RANK.
{-@ ple rankedDominionCoalitionElement @-}
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

{-@ ple rankedCoalitionAt @-}
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
{-@ ple rankedCoalitionForward @-}
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
{-@ ple rankedCoalitionBackward @-}
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
{-@ ple rankedCoalitionRoundTrip @-}
{-@ rankedCoalitionRoundTrip :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {rankedCoalitionBackward owner insertion (rankedCoalitionForward owner insertion value) == Just value} @-}
rankedCoalitionRoundTrip :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value -> source -> ()
rankedCoalitionRoundTrip owner insertion value =
  rankedCoalitionForward owner insertion value `seq`
  dominionCoherence (rankedDominionValueDominion owner) (applyInsertion insertion value) `seq`
  insertionLeftInverse insertion value

-- ALIGN: RANKED-COALITION-INSERTION.
{-@ ple rankedCoalitionInsertion @-}
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

-- | The data component handles every raw target datum, including uncovered data.
-- ALIGN: RANKED-COMPONENT-BACKWARD.
{-@ reflect rankedComponentBackward @-}
rankedComponentBackward :: DomanialInsertion source value -> RankedDominionCellData value object -> Maybe source
rankedComponentBackward insertion datum = preimage insertion (cellValue datum)

-- | The coalition's cache and the transported datum encode the same value.
-- ALIGN: RANKED-COMPONENT-LEFT-INVERSE.
{-@ rankedComponentLeftInverse :: owner:RankedDominionAtlas ownerScope value
      -> insertion:DomanialInsertion source value
      -> target:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) target
           && SomePageElement target == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> value:source
      -> {rankedComponentBackward insertion
             (coalitionElementAt (rankedDominionAtlas owner) target (rankedCoalitionForward owner insertion value))
           == Just value} @-}
rankedComponentLeftInverse :: RankedDominionAtlas ownerScope value -> DomanialInsertion source value
  -> PageElement (RankedDominionPaginationScope value) object -> source -> ()
rankedComponentLeftInverse owner insertion target value =
  let valueAtlas = rankedDominionAtlas owner
      valueDominion = rankedDominionValueDominion owner
      element = rankedCoalitionForward owner insertion value
  in rankedCoalitionReachesOrigin owner target element `seq`
     let datum = coalitionElementAt valueAtlas target element
     in rankedComponentBackward insertion datum `seq`
        rankedOriginImageRank owner target datum `seq`
        dominionCoherence valueDominion (cellValue datum) `seq`
        dominionCoherence valueDominion (applyInsertion insertion value) `seq`
        insertionLeftInverse insertion value

{-@ ple rankedCoalitionReachesOrigin @-}
{-@ rankedCoalitionReachesOrigin :: owner:RankedDominionAtlas ownerScope value
      -> target:{PageElement (RankedDominionPaginationScope value) object |
           SomePageElement target == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> element:{CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coalitionElementSource element == originPageElement (atlasPageElements (rankedDominionAtlas owner))}
      -> {coalitionElementReaches element target} @-}
rankedCoalitionReachesOrigin :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object
  -> CoalitionData ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) -> ()
rankedCoalitionReachesOrigin _ target _ = pageElementTransportedReflexive target
