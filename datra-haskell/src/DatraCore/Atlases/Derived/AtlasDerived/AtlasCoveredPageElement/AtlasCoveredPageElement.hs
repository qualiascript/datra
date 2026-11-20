{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Evidence that Atlas data is covered by data in final regions.
module AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , AtlasCoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , atlasCoveredByWitness
  , atlasCoverageAt
  , coverageResultCovers
  , atlasCoveredAt
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  ) where

import AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness
  , AtlasCoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  , atlasCoverageAt
  , coverageResultCovers
  )

import qualified AtlasCoveredPageElement.Internal as Internal
import Atlas (Atlas, AtlasObject)
import AtlasExtent (cellTraceValid)
import PageElements (PageElement)
import Numeric.Natural (Natural)

-- | Retain coverage evidence for the exact cell and datum it certifies.
-- ALIGN: ATLAS-COVERED-BY-WITNESS.
{-@ atlasCoveredByWitness :: owner:Atlas a s d o f
      -> source:PageElement s object -> datum:d object
      -> witness:{AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum witness}
      -> AtlasCoveredPageElement (AtlasObject a s d) @-}
atlasCoveredByWitness
  :: Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d) -> AtlasCoveredPageElement (AtlasObject a s d)
atlasCoveredByWitness _ source datum witness = Internal.AtlasCoveredPageElement source datum witness

-- | Decode one finite enumeration index, retaining its checked coverage.
-- ALIGN: ATLAS-COVERED-DECODE.
{-@ ple atlasCoveredAt @-}
{-@ atlasCoveredAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe (AtlasCoveredPageElement (AtlasObject a s d)) @-}
atlasCoveredAt
  :: Atlas a s d o f -> PageElement s object -> Natural
  -> Maybe (AtlasCoveredPageElement (AtlasObject a s d))
atlasCoveredAt owner source candidate =
  case atlasCoverageAt owner source candidate of
    Nothing -> Nothing
    Just (datum, witness) -> Just (atlasCoveredByWitness owner source datum witness)
