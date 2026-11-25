{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition-dependent assembly for Dominion inclusion.
module DomanialInclusion.LiquidInternal
  ( coalitionComponentInsertion, onePageCoverage, dominionCoverage, dominionAtlasMap
  , dominionCoalitionElement ) where

import Atlas
  ( Atlas, AtlasObject, atlasFolio, atlasPageElements, atlasAcceptsDatum
  , atlasNormalizationAgrees, atlasNormalizationArrow, atlasCoherenceWitness )
import AtlasCoveredPageElement
  ( CoverageWitness, atlasCoverageWitness, coverageWitnessCovers, coverageWitnessAlongArrow )
import AtlasExtent (cellTraceValid)
import AtlasMap (AtlasMap, atlasMap)
import Coalition.Element (CoalitionElement, coalitionElementAt, coalitionElement)
import DomanialInsertion (DomanialInsertion, domanialInsertion, composeInsertions)
import DomanialInclusion.Data (DominionCellData, dominionCellProjection, dominionCellData)
import DomanialInclusion.Presentation
  ( DominionAtlas, DominionAtlasObject, DominionPaginationScope, dominionAtlas, dominionAcceptsDatum )
import Folio (folioLength)
import PageElements (PageElement, normalizePageElement, withPageElement, originPageElement)
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

-- | The public owner supplies the one-page premise to the general coverage law.
-- ALIGN: DOMINC-COVERAGE.
{-@ dominionCoverage :: owner:{Atlas a (DominionPaginationScope value) (DominionCellData value) () () |
           folioLength (atlasFolio owner) == 1}
      -> source:{PageElement (DominionPaginationScope value) object | cellTraceValid owner source}
      -> datum:{DominionCellData value object | atlasAcceptsDatum owner source datum}
      -> {witness:CoverageWitness a (DominionPaginationScope value) (DominionCellData value) |
           coverageWitnessCovers owner source datum witness} @-}
dominionCoverage
  :: forall a owner object. Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
  -> PageElement (DominionPaginationScope a) object
  -> DominionCellData a object
  -> CoverageWitness owner (DominionPaginationScope a) (DominionCellData a)
dominionCoverage = onePageCoverage

-- ALIGN: DOMINC-OWNER-MAP.
{-@ dominionAtlasMap :: DominionAtlas owner a -> AtlasMap (DominionAtlasObject owner a) @-}
dominionAtlasMap :: forall a owner. DominionAtlas owner a -> AtlasMap (DominionAtlasObject owner a)
dominionAtlasMap owner =
  let valueAtlas = dominionAtlas owner
  in atlasMap valueAtlas (\source datum -> dominionCoverage valueAtlas source datum)

-- | Constant membership and one-page coverage justify the public constructor.
-- ALIGN: DOMINC-OWNER-COALITION.
{-@ dominionCoalitionElement :: DominionAtlas owner a -> a
      -> CoalitionElement (DominionAtlasObject owner a) @-}
dominionCoalitionElement :: forall a owner. DominionAtlas owner a -> a
  -> CoalitionElement (DominionAtlasObject owner a)
dominionCoalitionElement owner value =
  let valueAtlas = dominionAtlas owner
  in withPageElement (originPageElement (atlasPageElements valueAtlas)) $ \origin ->
       let datum = dominionCellData value
       in dominionAcceptsDatum owner origin datum `seq`
          coalitionElement valueAtlas origin datum (dominionCoverage valueAtlas origin datum)

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
