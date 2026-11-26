{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Coverage by the singleton region at the supplied datum's chain position.
module ChainedDominionAtlas.Coverage (chainedDominionCoverage, chainedDominionAtlasMap) where

import Atlas
  ( atlasFolio, atlasPageElements, atlasAcceptsDatum, mapAtlasData )
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, coverageWitnessTransport )
import AtlasExtent (cellTraceValid)
import TwoPageCoverage (twoPageRegionCoverage)
import AtlasMap (AtlasMap, atlasMap)
import Chain (chainIndexOf, chainPosition)
import ChainedDominionAtlas.Action (chainedDominionCell, cellMap)
import ChainedDominionAtlas.Data (ChainedDominionCellData (..), cellValue, extentAccepts, regionToExtent)
import ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, ChainedDominionAtlasObject, chainedDominionAtlas, chainedDominionFirst, chainedDominionChain
  , chainedDominionMembership, chainedDominionTransport )
import ChainedDominionAtlas.Presentation (chainedRegionPosition, chainedDominionAccepts)
import DomanialInsertion.Core (applyInsertion)
import PageElements
  ( PageElement, lastPageElement, withPageElement, originPageElement
  , pageElementTraceValidOrigin )
import PageElements.Structure
  ( SomePageElement (..), PageElementArrow, arrowSource, arrowTarget, pageElementArrow
  , pageElementPage, pageElementPosition )

-- ALIGN: CHAINED-OWNER-COVERAGE.
{-@ chainedDominionCoverage :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> {witness:CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           coverageWitnessCovers (chainedDominionAtlas owner) source datum witness} @-}
chainedDominionCoverage :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
chainedDominionCoverage owner source datum =
  let valueAtlas = chainedDominionAtlas owner
  in atlasFolio valueAtlas `seq`
     withPageElement
       (lastPageElement (atlasPageElements valueAtlas)
         (chainIndexOf (chainedDominionChain owner) (cellValue datum))) $ \region ->
       chainedCoverageAt owner source datum region

-- ALIGN: CHAINED-OWNER-COVERAGE-MAP.
{-@ chainedDominionAtlasMap :: ChainedDominionAtlas owner scope value
      -> AtlasMap (ChainedDominionAtlasObject owner scope value) @-}
chainedDominionAtlasMap :: ChainedDominionAtlas owner scope value
  -> AtlasMap (ChainedDominionAtlasObject owner scope value)
chainedDominionAtlasMap owner =
  atlasMap (chainedDominionAtlas owner) (chainedDominionCoverage owner)

-- ALIGN: CHAINED-REGION-COVERAGE.
{-@ chainedRegionCoverage :: owner:ChainedDominionAtlas ownerScope scope value
      -> region:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) region
           && pageElementPage region == 1}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) region datum}
      -> {witness:CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           coverageWitnessCovers (chainedDominionAtlas owner) region datum witness} @-}
chainedRegionCoverage :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
chainedRegionCoverage owner = twoPageRegionCoverage (chainedDominionAtlas owner)

-- ALIGN: CHAINED-ORIGIN-IMAGE.
{-@ chainedOriginImage :: owner:ChainedDominionAtlas ownerScope scope value
      -> arrow:{PageElementArrow scope source target |
           cellTraceValid (chainedDominionAtlas owner) (arrowSource arrow)
           && cellTraceValid (chainedDominionAtlas owner) (arrowTarget arrow)
           && pageElementPage (arrowTarget arrow) == 0}
      -> datum:{ChainedDominionCellData value source |
           atlasAcceptsDatum (chainedDominionAtlas owner) (arrowSource arrow) datum}
      -> {applyInsertion (mapAtlasData (chainedDominionAtlas owner) arrow) datum
           == ChainedDominionExtentDatum (cellValue datum)} @-}
chainedOriginImage :: ChainedDominionAtlas ownerScope scope value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source -> ()
chainedOriginImage owner arrow datum =
  chainedDominionMembership owner (arrowSource arrow) datum `seq`
  chainedDominionTransport owner arrow datum `seq`
  if pageElementPage (arrowSource arrow) == 0
  then case datum of
    ChainedDominionExtentDatum _ -> ()
    ChainedDominionRegionDatum _ -> ()
  else case datum of
    ChainedDominionExtentDatum _ -> ()
    ChainedDominionRegionDatum _ -> ()

-- ALIGN: CHAINED-COVERAGE-AT.
{-@ chainedCoverageAt :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> region:{PageElement scope regionObject | cellTraceValid (chainedDominionAtlas owner) region
           && pageElementPage region == 1
           && pageElementPosition region == chainPosition (chainedDominionChain owner) (cellValue datum)}
      -> {witness:CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           coverageWitnessCovers (chainedDominionAtlas owner) source datum witness} @-}
chainedCoverageAt :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object
  -> PageElement scope regionObject -> CoverageWitness ownerScope scope (ChainedDominionCellData value)
chainedCoverageAt owner source datum region =
  let valueAtlas = chainedDominionAtlas owner
      category = atlasPageElements valueAtlas
      regionDatum = ChainedDominionRegionDatum (cellValue datum)
  in atlasFolio valueAtlas `seq`
     chainedRegionPosition category (chainedDominionFirst owner) (chainedDominionChain owner) region `seq`
     chainedDominionMembership owner region regionDatum `seq`
     let witness = chainedRegionCoverage owner region regionDatum
     in pageElementTraceValidOrigin category source `seq`
        pageElementTraceValidOrigin category region `seq`
        withPageElement (originPageElement category) (\origin ->
          let sourceArrow = pageElementArrow source origin
              regionArrow = pageElementArrow region origin
          in chainedOriginImage owner sourceArrow datum `seq`
             chainedOriginImage owner regionArrow regionDatum `seq`
             coverageWitnessTransport valueAtlas regionArrow regionDatum witness `seq`
             coverageWitnessTransport valueAtlas sourceArrow datum witness `seq` witness)
