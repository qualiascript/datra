{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Evidence that Atlas data is covered by data in final regions.
module AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , CoverageWitness
  , AtlasCoveredPageElement
  , CoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessRankMatches
  , atlasOriginImageRank
  , coverageWitnessCode
  , coverageWitnessBound
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , atlasCoveredByWitness
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , atlasCoveredPageElementAt
  , coverageRankCandidateExact
  , coverageRankWitness
  , atlasCoverageRankWithin
  , atlasCoverageRank
  , atlasCoverageRankLeast
  , coverageRankCanonical
  , coverageRankCanonicalUnique
  , coverageRankAlongArrow
  , coverageRankNormalized
  , atlasCoveredAt
  , withAtlasCoveredPageElement
  , coveredPageElementValid
  , coveredPageElementSource
  , withAtlasCoveredPageElementOf
  , atlasCoveredPageElementWitness
  ) where

import AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness
  , CoverageWitness
  , AtlasCoveredPageElement
  , CoveredPageElement
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessRankMatches
  , atlasOriginImageRank
  , coverageWitnessCode
  , coverageWitnessAlongArrow
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , coveredPageElementValid
  , coveredPageElementSource
  , withAtlasCoveredPageElementOf
  , atlasCoveredPageElementWitness
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , atlasCoveredPageElementAt
  , coverageRankCandidateExact
  , atlasCoverageRankWithin
  , atlasCoverageRankLeast
  , coverageRankCanonical
  , coverageRankCanonicalUnique
  )

import qualified AtlasCoveredPageElement.Internal as Internal
import Atlas (Atlas, AtlasObject, atlasAcceptsDatum, mapAtlasData, normalizeAtlasElement)
import AtlasExtent (cellTraceValid)
import PageElements.Structure (PageElement, SomePageElement (..), PageElementArrow, arrowSource, arrowTarget)
import DomanialInsertion.Core (applyInsertion)
import Numeric.Natural (Natural)

-- | Retain coverage evidence for the exact cell and datum it certifies.
-- ALIGN: ATLAS-COVERED-BY-WITNESS.
{-@ ple atlasCoveredByWitness @-}
{-@ atlasCoveredByWitness :: owner:Atlas a s d o f
      -> source:PageElement s object -> datum:d object
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> {element:CoveredPageElement a s d | coveredPageElementValid owner element
           && coveredPageElementSource element == SomePageElement source
           && atlasCoveredPageElementWitness element == witness} @-}
atlasCoveredByWitness
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoveredPageElement a s d
atlasCoveredByWitness _ source datum witness = Internal.AtlasCoveredPageElement source datum witness

-- | Decode one finite enumeration index, retaining its checked coverage.
-- ALIGN: ATLAS-COVERED-DECODE.
{-@ ple atlasCoveredAt @-}
{-@ atlasCoveredAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({element:CoveredPageElement a s d | coveredPageElementValid owner element}) @-}
atlasCoveredAt
  :: Atlas a s d o f -> PageElement s object -> Natural
  -> Maybe (CoveredPageElement a s d)
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

-- | Keep both coverage-code certificates across the owning normalization.
{-@ coverageRankNormalized :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> candidate:Natural
      -> {coverageRankCandidate owner source datum candidate
           == coverageRankCandidate owner (normalizeAtlasElement owner source) datum candidate
           && coverageRankCanonical owner source datum candidate
           == coverageRankCanonical owner (normalizeAtlasElement owner source) datum candidate} @-}
coverageRankNormalized :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> ()
coverageRankNormalized = Internal.coverageRankNormalized
