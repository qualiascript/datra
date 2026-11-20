{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed Natural as int @-}

-- | Hidden implementation of coverage by final Atlas regions.
module AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness (..)
  , AtlasCoveredPageElement (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessAlongArrow
  , coverageFinalPage
  , coverageNormalize
  , atlasOriginImageRank
  , findAtlasCoverage
  , findAtlasCoverageRank
  , atlasCoverageAt
  , coverageResultCovers
  , atlasCoveredPageElementAt
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , atlasCardinality
  , atlasDataAt
  , atlasAcceptsDatum
  , mapAtlasData
  , normalizeAtlasElementTraceValid
  , atlasAcceptsDatumNormalized
  , normalizeAtlasElement
  )
import AtlasExtent (atlasCellOriginRankInsertion, cellTraceHasOrigin, cellTraceValid, cellOriginRankMap)
import AtlasTerritory
  ( withAtlasTerritory
  , atlasTerritoryChain
  )
import DomanialInsertion.Core (applyInsertion, preimage)
import Chain (chainIndex)
import DatraOrdinal (ordinal)
import Dominion (rank, unrank)
import Numeric.Natural (Natural)
import NaturalEncoding (unpairNatural, decodeNaturalList)
import PageElements.Structure
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElementPage
  )

-- | The existential witness in Lean's @Covered X x t@ predicate: a datum in
-- a final region whose image in the origin is the image of the source datum.
-- Its constructor is hidden; 'atlasCoverageWitness' is the checked
-- introduction rule.
type role AtlasCoverageWitness nominal
data AtlasCoverageWitness atlasObject where
  AtlasCoverageWitness
    :: PageElement (AtlasObjectPaginationScope atlasObject) regionObject
    -> AtlasObjectCellData atlasObject regionObject
    -> Natural
    -> Natural
    -> AtlasCoverageWitness atlasObject

-- | A page element paired with its datum and evidence that it is covered by a
-- final region.
type role AtlasCoveredPageElement nominal
data AtlasCoveredPageElement atlasObject where
  AtlasCoveredPageElement
    :: PageElement (AtlasObjectPaginationScope atlasObject) object
    -> AtlasObjectCellData atlasObject object
    -> AtlasCoverageWitness atlasObject
    -> AtlasCoveredPageElement atlasObject

-- | Rank the image of a datum in the Atlas extent. Dominion ranks are
-- injective, so equality of these ranks is equality of the origin images.
-- ALIGN: ATLAS-COVERAGE-RANK-EQUALITY.
-- ALIGN: ATLAS-ORIGIN-IMAGE-INTERPRETATION.
-- ALIGN: ATLAS-ORIGIN-RANK-INTERPRETATION.
{-@ reflect atlasOriginImageRank @-}
-- ALIGN: ATLAS-ORIGIN-RANK-NORMALIZATION.
{-@ atlasOriginImageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural @-}
atlasOriginImageRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
atlasOriginImageRank valueAtlas occurrence datum =
  cellTraceHasOrigin valueAtlas occurrence `seq`
    applyInsertion (atlasCellOriginRankInsertion valueAtlas occurrence) datum

{-@ reflect coveragePage @-}
coveragePage :: PageElement scope object -> Natural
coveragePage = pageElementPage

{-@ reflect coverageNormalize @-}
coverageNormalize
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> PageElement scope object
coverageNormalize = normalizeAtlasElement

{-@ reflect coverageFinalPage @-}
coverageFinalPage
  :: Atlas atlasScope scope cellData origin final
  -> Natural
coverageFinalPage valueAtlas = atlasCardinality valueAtlas - 1

-- | Check the owning trace and carrier before comparing the cached final
-- page and origin rank with the source datum's actual origin image.
-- ALIGN: ATLAS-COVERAGE-INTERPRETATION.
{-@ reflect coverageWitnessCovers @-}
-- ALIGN: ATLAS-COVERAGE-WITNESS-SOUND.
coverageWitnessCovers
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness
       (AtlasObject atlasScope scope cellData)
  -> Bool
coverageWitnessCovers
  valueAtlas
  source
  sourceDatum
  (AtlasCoverageWitness _ _ regionPage regionOriginRank)
  | cellTraceValid valueAtlas source
  , atlasAcceptsDatum valueAtlas source sourceDatum =
      regionPage == coverageFinalPage valueAtlas
        && atlasOriginImageRank valueAtlas source sourceDatum == regionOriginRank
  | otherwise = False

-- | A witness for a transported datum also covers the original datum.
-- ALIGN: ATLAS-COVERAGE-TRANSPORT.
{-@ coverageWitnessAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> witness:{AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner (arrowTarget arrow)
             (applyInsertion (mapAtlasData owner arrow) datum) witness}
      -> {coverageWitnessCovers owner (arrowSource arrow) datum witness} @-}
coverageWitnessAlongArrow
  :: Atlas a s d o f -> PageElementArrow s source target -> d source
  -> AtlasCoverageWitness (AtlasObject a s d) -> ()
coverageWitnessAlongArrow owner arrow datum (AtlasCoverageWitness _ _ _ _) =
  cellTraceHasOrigin owner (arrowSource arrow) `seq`
  cellTraceHasOrigin owner (arrowTarget arrow) `seq`
  cellOriginRankMap owner arrow datum

-- | Introduce a coverage witness. LiquidHaskell checks that the region is on
-- the final page and that its datum has the same origin image as the source.
{-@
atlasCoverageWitness
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:{PageElement scope object | cellTraceValid valueAtlas source}
  -> sourceDatum:{cellData object | atlasAcceptsDatum valueAtlas source sourceDatum}
  -> region:{PageElement scope regionObject | cellTraceValid valueAtlas region}
  -> regionDatum:{cellData regionObject | atlasAcceptsDatum valueAtlas region regionDatum}
  -> conditions:{ proof:() |
       coveragePage (coverageNormalize valueAtlas region)
         == coverageFinalPage valueAtlas
       && atlasOriginImageRank
            valueAtlas
            (coverageNormalize valueAtlas source)
            sourceDatum
          == atlasOriginImageRank
               valueAtlas
               (coverageNormalize valueAtlas region)
               regionDatum }
  -> { witness:AtlasCoverageWitness
         (AtlasObject atlasScope scope cellData) |
       coverageWitnessCovers
         valueAtlas
         (coverageNormalize valueAtlas source)
         sourceDatum
         witness }
@-}
-- ALIGN: ATLAS-COVERAGE-CONSTRUCTOR.
atlasCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoverageWitness
       (AtlasObject atlasScope scope cellData)
atlasCoverageWitness valueAtlas source sourceDatum region regionDatum _ =
  normalizeAtlasElementTraceValid valueAtlas source `seq`
  atlasAcceptsDatumNormalized valueAtlas source sourceDatum `seq`
  normalizeAtlasElementTraceValid valueAtlas region `seq`
  atlasAcceptsDatumNormalized valueAtlas region regionDatum `seq`
  AtlasCoverageWitness
    (coverageNormalize valueAtlas region)
    regionDatum
    (coveragePage (coverageNormalize valueAtlas region))
    (atlasOriginImageRank
      valueAtlas
      (coverageNormalize valueAtlas region)
      regionDatum)

-- | Construct a covered page element using the checked introduction rule.
{-@
atlasCoveredPageElement
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:{PageElement scope object | cellTraceValid valueAtlas source}
  -> sourceDatum:{cellData object | atlasAcceptsDatum valueAtlas source sourceDatum}
  -> region:{PageElement scope regionObject | cellTraceValid valueAtlas region}
  -> regionDatum:{cellData regionObject | atlasAcceptsDatum valueAtlas region regionDatum}
  -> conditions:{ proof:() |
       coveragePage (coverageNormalize valueAtlas region)
         == coverageFinalPage valueAtlas
       && atlasOriginImageRank
            valueAtlas
            (coverageNormalize valueAtlas source)
            sourceDatum
          == atlasOriginImageRank
               valueAtlas
               (coverageNormalize valueAtlas region)
               regionDatum }
  -> AtlasCoveredPageElement (AtlasObject atlasScope scope cellData)
@-}
-- ALIGN: ATLAS-COVERED-CONSTRUCTOR.
atlasCoveredPageElement
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoveredPageElement
       (AtlasObject atlasScope scope cellData)
atlasCoveredPageElement
  valueAtlas source sourceDatum region regionDatum conditions =
    AtlasCoveredPageElement
      (coverageNormalize valueAtlas source)
      sourceDatum
      (atlasCoverageWitness
        valueAtlas source sourceDatum region regionDatum conditions)

-- | Eliminate a covered page element while retaining its dependent cell-data
-- type.
-- ALIGN: ATLAS-COVERED-SEMANTICS.
{-@ reflect withAtlasCoveredPageElement @-}
withAtlasCoveredPageElement
  :: AtlasCoveredPageElement atlasObject
  -> (forall object.
        PageElement (AtlasObjectPaginationScope atlasObject) object
        -> AtlasObjectCellData atlasObject object
        -> result)
  -> result
withAtlasCoveredPageElement
  (AtlasCoveredPageElement occurrence datum _)
  useCovered = useCovered occurrence datum

-- | Recover the evidence already carried by a covered datum.
-- ALIGN: ATLAS-COVERED-WITNESS.
atlasCoveredPageElementWitness
  :: AtlasCoveredPageElement atlasObject -> AtlasCoverageWitness atlasObject
atlasCoveredPageElementWitness (AtlasCoveredPageElement _ _ witness) = witness

-- | Search the countable final territory for a coverage witness. This is the
-- executable counterpart needed because Haskell's 'Dominion' carries an
-- @unrank@ operation whereas Lean's dominions only require a rank embedding.
-- The search terminates exactly on covered page elements, the only domain on
-- which Charter calls it.
-- ALIGN: ATLAS-COVERAGE-SEARCH-SPEC.
{-@ findAtlasCoverage :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> AtlasCoverageWitness (AtlasObject a s d) @-}
findAtlasCoverage
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
findAtlasCoverage valueAtlas source sourceDatum =
  searchAtlasCoverageFrom valueAtlas source sourceDatum 0

-- | The first enumeration index witnessing coverage of a datum. The search
-- is total on the abstract covered carrier used by Charter.
{-@ lazy findAtlasCoverageRank @-}
-- ALIGN: ATLAS-COVERAGE-RANK-ROUNDTRIP.
-- ALIGN: ATLAS-COVERAGE-RANK-MINIMAL.
{-@ findAtlasCoverageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> Natural @-}
findAtlasCoverageRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
findAtlasCoverageRank valueAtlas source sourceDatum = go 0
  where
    sourceDominion = atlasDataAt valueAtlas source
    sourceRank = rank sourceDominion sourceDatum

    go candidate =
      case atlasCoveredPageElementAt valueAtlas source candidate of
        Just candidateDatum
          | rank sourceDominion candidateDatum == sourceRank -> candidate
        _ -> go (candidate + 1)

-- | Decode one finite coverage candidate. A final-region datum is transported
-- to the origin and pulled back along the selected source cell. Unlike a
-- membership filter, this operation terminates for every index.
{-@ atlasCoveredPageElementAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({datum:d object | atlasAcceptsDatum owner source datum}) @-}
atlasCoveredPageElementAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe (cellData object)
atlasCoveredPageElementAt valueAtlas source candidate =
  case atlasCoverageAt valueAtlas source candidate of
    Nothing -> Nothing
    Just (datum, _) -> Just datum

-- | Decode one coverage candidate together with the evidence that made it a
-- member of the covered carrier.  Returning the witness alongside the datum
-- lets downstream dependent carriers stay total instead of reconstructing
-- evidence with an unchecked search.
-- ALIGN: ATLAS-COVERAGE-DECODE-SOUND.
-- ALIGN: ATLAS-COVERAGE-RANK-DECODER.
-- ALIGN: ATLAS-COVERAGE-DECODE-COMPLETE.
{-@ atlasCoverageAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, AtlasCoverageWitness (AtlasObject a s d)) |
           coverageResultCovers owner source result}) @-}
atlasCoverageAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe
       ( cellData object
       , AtlasCoverageWitness
           (AtlasObject atlasScope scope cellData)
       )
atlasCoverageAt valueAtlas source candidate =
  cellTraceHasOrigin valueAtlas source `seq`
  case unpairNatural candidate of
    (positionCode, datumRank) ->
      case chainIndex
        (atlasTerritoryChain valueAtlas)
        (ordinal (decodeNaturalList positionCode)) of
          Nothing -> Nothing
          Just territoryIndex ->
            withAtlasTerritory valueAtlas territoryIndex $ \region ->
              case unrank (atlasDataAt valueAtlas region) datumRank of
                Nothing -> Nothing
                Just regionDatum ->
                  let regionOriginRank = atlasOriginImageRank valueAtlas region regionDatum
                  in case preimage (atlasCellOriginRankInsertion valueAtlas source) regionOriginRank of
                    Nothing -> Nothing
                    Just sourceDatum
                      | atlasOriginImageRank valueAtlas source sourceDatum == regionOriginRank ->
                          Just (sourceDatum, AtlasCoverageWitness region regionDatum
                            (coverageFinalPage valueAtlas) regionOriginRank)
                      | otherwise -> Nothing

-- | The decoder retains coverage for the exact datum returned alongside it.
{-@ reflect coverageResultCovers @-}
coverageResultCovers
  :: Atlas a s d o f -> PageElement s object
  -> (d object, AtlasCoverageWitness (AtlasObject a s d)) -> Bool
coverageResultCovers owner source (datum, witness) =
  coverageWitnessCovers owner source datum witness

{-@ lazy searchAtlasCoverageFrom @-}
{-@ searchAtlasCoverageFrom :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural
      -> AtlasCoverageWitness (AtlasObject a s d) @-}
searchAtlasCoverageFrom
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
searchAtlasCoverageFrom valueAtlas source sourceDatum candidate =
  case coverageCandidate valueAtlas source sourceDatum candidate of
    Just witness -> witness
    Nothing ->
      searchAtlasCoverageFrom valueAtlas source sourceDatum (candidate + 1)

-- ALIGN: ATLAS-COVERAGE-CANDIDATE-SOUND.
-- ALIGN: ATLAS-COVERAGE-CANDIDATE-COMPLETE.
{-@ coverageCandidate :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural
      -> Maybe ({witness:AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum witness}) @-}
coverageCandidate
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
  -> Maybe (AtlasCoverageWitness (AtlasObject atlasScope scope cellData))
coverageCandidate valueAtlas source sourceDatum candidate =
  case unpairNatural candidate of
    (positionCode, datumRank) ->
      case chainIndex
        (atlasTerritoryChain valueAtlas)
        (ordinal (decodeNaturalList positionCode)) of
          Nothing -> Nothing
          Just territoryIndex ->
            withAtlasTerritory valueAtlas territoryIndex $ \region ->
                case unrank (atlasDataAt valueAtlas region) datumRank of
                  Nothing -> Nothing
                  Just regionDatum
                    | atlasOriginImageRank valueAtlas source sourceDatum
                        == atlasOriginImageRank
                             valueAtlas region regionDatum ->
                        Just
                          (AtlasCoverageWitness
                            region
                            regionDatum
                            (coverageFinalPage valueAtlas)
                            (atlasOriginImageRank
                              valueAtlas source sourceDatum))
                    | otherwise -> Nothing
