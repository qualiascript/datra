{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Self-coverage of accepted data on the final page of a two-page Atlas.
module TwoPageCoverage (twoPageRegionCoverage) where

import Atlas
  ( Atlas, atlasFolio, atlasPageElements, atlasAcceptsDatum
  , atlasNormalizationAgrees, atlasNormalizationArrow, atlasCoherenceWitness )
import AtlasCoveredPageElement
  ( CoverageWitness, atlasCoverageWitness, coverageWitnessCovers, coverageWitnessTransport )
import AtlasExtent (cellTraceValid)
import Folio (folioLength)
import PageElements (PageElement, normalizePageElement)
import PageElements.Structure (pageElementPage)

-- ALIGN: TWO-PAGE-REGION-COVERAGE.
{-@ twoPageRegionCoverage :: owner:{Atlas ownerScope scope cellData origin final |
           folioLength (atlasFolio owner) == 2}
      -> region:{PageElement scope object | cellTraceValid owner region && pageElementPage region == 1}
      -> datum:{cellData object | atlasAcceptsDatum owner region datum}
      -> {witness:CoverageWitness ownerScope scope cellData | coverageWitnessCovers owner region datum witness} @-}
twoPageRegionCoverage :: Atlas ownerScope scope cellData origin final
  -> PageElement scope object -> cellData object -> CoverageWitness ownerScope scope cellData
twoPageRegionCoverage owner region datum =
  let arrow = atlasNormalizationArrow owner region
  in atlasFolio owner `seq`
     atlasNormalizationAgrees owner region `seq`
     pageElementPage (normalizePageElement (atlasPageElements owner) region) `seq`
     let witness = atlasCoverageWitness owner region datum region datum ()
     in atlasCoherenceWitness owner region arrow datum `seq`
        coverageWitnessTransport owner arrow datum witness `seq` witness
