{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition-dependent assembly for Dominion inclusion.
module DomanialInclusion.LiquidInternal (coalitionComponentInsertion, onePageCoverage) where

import Atlas
  ( Atlas, AtlasObject, atlasFolio, atlasPageElements, atlasAcceptsDatum
  , atlasNormalizationAgrees, atlasNormalizationArrow, atlasCoherenceWitness )
import AtlasCoveredPageElement
  ( CoverageWitness, atlasCoverageWitness, coverageWitnessCovers, coverageWitnessAlongArrow )
import AtlasExtent (cellTraceValid)
import Coalition.Element (CoalitionElement, coalitionElementAt)
import DomanialInsertion (DomanialInsertion, domanialInsertion, composeInsertions)
import DomanialInclusion.Data (DominionCellData, dominionCellProjection)
import Folio (folioLength)
import PageElements (PageElement, normalizePageElement)
import PageElements.Structure (pageElementPage)
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | On a one-page Atlas the normalized source is already a final region.
-- Coverage transports back to the original occurrence through coherence.
-- ALIGN: DOMINC-ONE-PAGE-COVERAGE.
{-@ onePageCoverage :: owner:{Atlas a s d o f | folioLength (atlasFolio owner) == 1}
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> {witness:CoverageWitness a s d | coverageWitnessCovers owner source datum witness} @-}
onePageCoverage :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
onePageCoverage owner source datum =
  atlasNormalizationAgrees owner source `seq`
  pageElementPage (normalizePageElement (atlasPageElements owner) source) `seq`
  let arrow = atlasNormalizationArrow owner source
      witness = atlasCoverageWitness owner source datum source datum ()
  in atlasCoherenceWitness owner source arrow datum `seq`
     coverageWitnessAlongArrow owner arrow datum witness `seq` witness

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
