{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Evidence that Atlas data is covered by data in final regions.
module AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , CoverageWitness
  , AtlasCoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessCode
  , coverageWitnessBound
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , atlasCoveredByWitness
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , coverageRankWitness
  , atlasCoverageRankWithin
  , atlasCoverageRank
  , atlasCoverageRankLeast
  , coverageRankCanonical
  , coverageRankCanonicalUnique
  , coverageRankAlongArrow
  , atlasCoveredAt
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  ) where

import AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness
  , CoverageWitness
  , AtlasCoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessCode
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , atlasCoverageRankWithin
  , atlasCoverageRankLeast
  , coverageRankCanonical
  , coverageRankCanonicalUnique
  )

import qualified AtlasCoveredPageElement.Internal as Internal
import Atlas (Atlas, AtlasObject, atlasAcceptsDatum, mapAtlasData)
import AtlasExtent (cellTraceValid)
import PageElements.Structure (PageElement, PageElementArrow, arrowSource, arrowTarget)
import DomanialInsertion.Core (applyInsertion)
import Numeric.Natural (Natural)

-- | Retain coverage evidence for the exact cell and datum it certifies.
-- ALIGN: ATLAS-COVERED-BY-WITNESS.
{-@ atlasCoveredByWitness :: owner:Atlas a s d o f
      -> source:PageElement s object -> datum:d object
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> AtlasCoveredPageElement (AtlasObject a s d) @-}
atlasCoveredByWitness
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> AtlasCoveredPageElement (AtlasObject a s d)
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

-- | A checked successful enumeration bound supplied by coverage evidence.
{-@ coverageWitnessBound :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {candidate:Natural | coverageRankCandidate owner source datum candidate} @-}
coverageWitnessBound
  :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
coverageWitnessBound = Internal.coverageWitnessBound

-- | Rank a covered datum using its retained witness as a finite search bound.
{-@ atlasCoverageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {found:Natural | coverageRankCandidate owner source datum found
           && coverageRankCanonical owner source datum found} @-}
atlasCoverageRank
  :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
atlasCoverageRank = Internal.atlasCoverageRank

-- | Recover the witness certified by an enumeration rank.
{-@ coverageRankWitness :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> candidate:{Natural | coverageRankCandidate owner source datum candidate}
      -> {result:Maybe ({witness:CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}) | result /= Nothing} @-}
coverageRankWitness
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe (CoverageWitness a s d)
coverageRankWitness = Internal.coverageRankWitness

-- | Transport a successful or canonical coverage code along a valid data arrow.
{-@ coverageRankAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> candidate:Natural
      -> {coverageRankCandidate owner (arrowSource arrow) datum candidate
           == coverageRankCandidate owner (arrowTarget arrow) (applyInsertion (mapAtlasData owner arrow) datum) candidate
           && coverageRankCanonical owner (arrowSource arrow) datum candidate
           == coverageRankCanonical owner (arrowTarget arrow) (applyInsertion (mapAtlasData owner arrow) datum) candidate} @-}
coverageRankAlongArrow
  :: Atlas a s d o f -> PageElementArrow s source target -> d source -> Natural -> ()
coverageRankAlongArrow = Internal.coverageRankAlongArrow
