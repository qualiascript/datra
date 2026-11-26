{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Coverage by the final region at the supplied datum's Dominion rank.
module RankedDominionAtlas.Coverage
  ( rankedDominionCoverage, rankedDominionAtlasMap, rankedOriginImageRank ) where

import Atlas
  ( atlasFolio, atlasPageElements, atlasAcceptsDatum, atlasDataAt, mapAtlasData )
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, coverageWitnessTransport, atlasOriginImageRank )
import AtlasExtent (cellTraceValid, cellTraceHasOrigin, atlasCellOriginRankAt)
import TwoPageCoverage (twoPageRegionCoverage)
import AtlasMap (AtlasMap, atlasMap)
import Chain (chainIndexOf, spine, spinePosition)
import DatraOrdinal (finiteOrdinal)
import Dominion (rank)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope)
import RankedDominionAtlas.Action (cellAt, cellMap, cellRank, spineRankFinite)
import RankedDominionAtlas.Data (RankedDominionCellData (..), cellValue, extentAccepts)
import RankedDominionAtlas.Owner
  ( RankedDominionAtlas, RankedDominionAtlasObject, rankedDominionAtlas, rankedDominionValueDominion
  , rankedDominionMembership, rankedDominionTransport, rankedDominionDataAt )
import RankedDominionAtlas.Presentation (rankedDominionAccepts)
import DomanialInsertion.Core (applyInsertion)
import PageElements
  ( PageElement, lastPageElement, withPageElement, originPageElement
  , pageElementTraceValidOrigin )
import PageElements.Structure
  ( SomePageElement (..), PageElementArrow, arrowSource, arrowTarget, pageElementArrow
  , pageElementPage, pageElementPosition )

-- ALIGN: RANKED-OWNER-COVERAGE.
{-@ rankedDominionCoverage :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) source}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coverageWitnessCovers (rankedDominionAtlas owner) source datum witness} @-}
rankedDominionCoverage :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedDominionCoverage owner source datum =
  let valueAtlas = rankedDominionAtlas owner
  in atlasFolio valueAtlas `seq`
     spinePosition (rank (rankedDominionValueDominion owner) (cellValue datum)) `seq`
     withPageElement
       (lastPageElement (atlasPageElements valueAtlas)
         (chainIndexOf spine (rank (rankedDominionValueDominion owner) (cellValue datum)))) $ \region ->
       rankedCoverageAt owner source datum region

-- ALIGN: RANKED-OWNER-COVERAGE-MAP.
{-@ rankedDominionAtlasMap :: RankedDominionAtlas owner value
      -> AtlasMap (RankedDominionAtlasObject owner value) @-}
rankedDominionAtlasMap :: RankedDominionAtlas owner value
  -> AtlasMap (RankedDominionAtlasObject owner value)
rankedDominionAtlasMap owner =
  atlasMap (rankedDominionAtlas owner) (rankedDominionCoverage owner)

-- ALIGN: RANKED-REGION-COVERAGE.
{-@ rankedRegionCoverage :: owner:RankedDominionAtlas ownerScope value
      -> region:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) region
           && pageElementPage region == 1}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) region datum}
      -> {witness:CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coverageWitnessCovers (rankedDominionAtlas owner) region datum witness} @-}
rankedRegionCoverage :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedRegionCoverage owner = twoPageRegionCoverage (rankedDominionAtlas owner)

-- ALIGN: RANKED-ORIGIN-IMAGE.
{-@ rankedOriginImage :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           cellTraceValid (rankedDominionAtlas owner) (arrowSource arrow)
           && cellTraceValid (rankedDominionAtlas owner) (arrowTarget arrow)
           && pageElementPage (arrowTarget arrow) == 0}
      -> datum:{RankedDominionCellData value source |
           atlasAcceptsDatum (rankedDominionAtlas owner) (arrowSource arrow) datum}
      -> {applyInsertion (mapAtlasData (rankedDominionAtlas owner) arrow) datum
           == RankedDominionExtentDatum (cellValue datum)} @-}
rankedOriginImage :: RankedDominionAtlas ownerScope value
  -> PageElementArrow (RankedDominionPaginationScope value) source target -> RankedDominionCellData value source -> ()
rankedOriginImage owner arrow datum =
  rankedDominionMembership owner (arrowSource arrow) datum `seq`
  rankedDominionTransport owner arrow datum `seq`
  if pageElementPage (arrowSource arrow) == 0
  then case datum of
    RankedDominionExtentDatum _ -> ()
    RankedDominionRegionDatum _ -> ()
  else case datum of
    RankedDominionExtentDatum _ -> ()
    RankedDominionRegionDatum _ -> ()

-- ALIGN: RANKED-ORIGIN-IMAGE-RANK.
{-@ rankedOriginImageRank :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object |
           cellTraceValid (rankedDominionAtlas owner) source}
      -> datum:{RankedDominionCellData value object |
           atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> {atlasOriginImageRank (rankedDominionAtlas owner) source datum
           == rank (rankedDominionValueDominion owner) (cellValue datum)} @-}
rankedOriginImageRank :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> ()
rankedOriginImageRank owner source datum =
  let valueAtlas = rankedDominionAtlas owner
      category = atlasPageElements valueAtlas
  in cellTraceHasOrigin valueAtlas source `seq`
     pageElementTraceValidOrigin category source `seq`
     case originPageElement category of
       SomePageElement origin ->
         let arrow = pageElementArrow source origin
         in rankedDominionDataAt owner origin `seq`
            rankedOriginImage owner arrow datum `seq`
            cellRank (rankedDominionValueDominion owner) (cellAt origin)
              (RankedDominionExtentDatum (cellValue datum)) `seq`
            atlasDataAt valueAtlas origin `seq`
            mapAtlasData valueAtlas arrow `seq`
            atlasCellOriginRankAt valueAtlas source origin datum `seq`
            atlasOriginImageRank valueAtlas source datum `seq` ()

-- ALIGN: RANKED-COVERAGE-AT.
{-@ rankedCoverageAt :: owner:RankedDominionAtlas ownerScope value
      -> source:{PageElement (RankedDominionPaginationScope value) object | cellTraceValid (rankedDominionAtlas owner) source}
      -> datum:{RankedDominionCellData value object | atlasAcceptsDatum (rankedDominionAtlas owner) source datum}
      -> region:{PageElement (RankedDominionPaginationScope value) regionObject | cellTraceValid (rankedDominionAtlas owner) region
           && pageElementPage region == 1
           && pageElementPosition region == finiteOrdinal (rank (rankedDominionValueDominion owner) (cellValue datum))}
      -> {witness:CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) |
           coverageWitnessCovers (rankedDominionAtlas owner) source datum witness} @-}
rankedCoverageAt :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object
  -> PageElement (RankedDominionPaginationScope value) regionObject -> CoverageWitness ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value)
rankedCoverageAt owner source datum region =
  let valueAtlas = rankedDominionAtlas owner
      category = atlasPageElements valueAtlas
      regionDatum = RankedDominionRegionDatum (cellValue datum)
  in atlasFolio valueAtlas `seq`
     spineRankFinite (rank (rankedDominionValueDominion owner) (cellValue datum)) `seq`
     rankedDominionMembership owner region regionDatum `seq`
     let witness = rankedRegionCoverage owner region regionDatum
     in pageElementTraceValidOrigin category source `seq`
        pageElementTraceValidOrigin category region `seq`
        withPageElement (originPageElement category) (\origin ->
          let sourceArrow = pageElementArrow source origin
              regionArrow = pageElementArrow region origin
          in rankedOriginImage owner sourceArrow datum `seq`
             rankedOriginImage owner regionArrow regionDatum `seq`
             coverageWitnessTransport valueAtlas regionArrow regionDatum witness `seq`
             coverageWitnessTransport valueAtlas sourceArrow datum witness `seq` witness)
