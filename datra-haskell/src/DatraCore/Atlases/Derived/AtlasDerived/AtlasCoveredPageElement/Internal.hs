{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--max-case-expand=8" @-}
{-@ embed Natural as int @-}

-- | Hidden implementation of coverage by final Atlas regions.
module AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness
  , AtlasCoveredPageElement (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
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
    :: CoverageRegionData atlasObject regionObject
    -> AtlasCoverageWitness atlasObject

type role CoverageRegionData nominal nominal
{-@ data CoverageRegionData atlasObject object = CoverageRegionData
      { coverageRegion :: PageElement (AtlasObjectPaginationScope atlasObject) object
      , coverageRegionDatum :: AtlasObjectCellData atlasObject object
      , coverageRegionPage :: Natural
      , coverageRegionRank :: Natural
      } @-}
data CoverageRegionData atlasObject regionObject = CoverageRegionData
  { coverageRegion :: PageElement (AtlasObjectPaginationScope atlasObject) regionObject
  , coverageRegionDatum :: AtlasObjectCellData atlasObject regionObject
  , coverageRegionPage :: Natural
  , coverageRegionRank :: Natural
  }

-- | Observe a witness without exposing its constructor or cached fields.
withAtlasCoverageWitness
  :: AtlasCoverageWitness atlasObject
  -> (forall object. PageElement (AtlasObjectPaginationScope atlasObject) object
       -> AtlasObjectCellData atlasObject object -> result)
  -> result
withAtlasCoverageWitness (AtlasCoverageWitness value) useRegion =
  useRegion (coverageRegion value) (coverageRegionDatum value)

{-@ reflect coverageWitnessOriginRank @-}
coverageWitnessOriginRank :: AtlasCoverageWitness atlasObject -> Natural
coverageWitnessOriginRank (AtlasCoverageWitness value) = coverageRegionRank value

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
-- ALIGN: ATLAS-COVERAGE-VALIDATION.
{-@ reflect coverageWitnessValid @-}
coverageWitnessValid
  :: forall a s d o f. Atlas a s d o f -> AtlasCoverageWitness (AtlasObject a s d) -> Bool
coverageWitnessValid owner
    (AtlasCoverageWitness (value :: CoverageRegionData (AtlasObject a s d) object)) =
  coverageRegionDataValid owner value

{-@ reflect coverageRegionDataValid @-}
coverageRegionDataValid :: Atlas a s d o f -> CoverageRegionData (AtlasObject a s d) object -> Bool
coverageRegionDataValid owner value
  | cellTraceValid owner (coverageRegion value)
  , atlasAcceptsDatum owner (coverageRegion value) (coverageRegionDatum value) =
      coveragePage (coverageRegion value) == coverageFinalPage owner
        && coverageRegionPage value == coveragePage (coverageRegion value)
        && coverageRegionRank value ==
             atlasOriginImageRank owner (coverageRegion value) (coverageRegionDatum value)
  | otherwise = False

-- ALIGN: ATLAS-COVERAGE-INTERPRETATION.
{-@ reflect coverageWitnessCovers @-}
-- ALIGN: ATLAS-COVERAGE-WITNESS-SOUND.
coverageWitnessCovers
  :: Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d) -> Bool
coverageWitnessCovers owner source sourceDatum witness
  | cellTraceValid owner source
  , atlasAcceptsDatum owner source sourceDatum =
      coverageWitnessAtRank owner (atlasOriginImageRank owner source sourceDatum) witness
  | otherwise = False

{-@ reflect coverageWitnessAtRank @-}
coverageWitnessAtRank
  :: forall a s d o f. Atlas a s d o f -> Natural
  -> AtlasCoverageWitness (AtlasObject a s d) -> Bool
coverageWitnessAtRank owner sourceRank
    (AtlasCoverageWitness (value :: CoverageRegionData (AtlasObject a s d) regionObject)) =
  coverageRegionDataValid owner value
    && coverageRegionPage value == coverageFinalPage owner
    && sourceRank == coverageRegionRank value

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
coverageWitnessAlongArrow owner arrow datum _witness =
  cellTraceHasOrigin owner (arrowSource arrow) `seq`
  cellTraceHasOrigin owner (arrowTarget arrow) `seq`
  cellOriginRankMap owner arrow datum

{-@ coverageRegionWitness :: owner:Atlas a s d o f
      -> region:{PageElement s object | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> datum:{d object | atlasAcceptsDatum owner region datum}
      -> {witness:AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessValid owner witness && coverageWitnessCovers owner region datum witness} @-}
coverageRegionWitness
  :: forall a s d o f object. Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d)
coverageRegionWitness owner region datum =
  let witness = AtlasCoverageWitness (CoverageRegionData region datum
        (coveragePage region) (atlasOriginImageRank owner region datum))
  in coverageWitnessCovers owner region datum witness `seq` witness

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
  coverageRegionWitness valueAtlas (coverageNormalize valueAtlas region) regionDatum

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
  case unpairNatural candidate of
    (positionCode, datumRank) ->
      case chainIndex
        (atlasTerritoryChain valueAtlas)
        (ordinal (decodeNaturalList positionCode)) of
          Nothing -> Nothing
          Just territoryIndex ->
            withAtlasTerritory valueAtlas territoryIndex
              (coverageAtRegion valueAtlas source datumRank)

{-@ coverageAtRegion :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> Natural
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, AtlasCoverageWitness (AtlasObject a s d)) |
           coverageResultCovers owner source result}) @-}
coverageAtRegion
  :: Atlas a s d o f -> PageElement s object -> Natural
  -> PageElement s regionObject
  -> Maybe (d object, AtlasCoverageWitness (AtlasObject a s d))
coverageAtRegion owner source datumRank region =
  cellTraceHasOrigin owner source `seq`
  case unrank (atlasDataAt owner region) datumRank of
    Nothing -> Nothing
    Just regionDatum ->
      let regionOriginRank = atlasOriginImageRank owner region regionDatum
      in case preimage (atlasCellOriginRankInsertion owner source) regionOriginRank of
        Nothing -> Nothing
        Just sourceDatum
          | atlasOriginImageRank owner source sourceDatum == regionOriginRank ->
              Just (coveragePair owner source sourceDatum
                (coverageRegionWitness owner region regionDatum))
          | otherwise -> Nothing

{-@ coveragePair :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum witness}
      -> {result:({value:d object | atlasAcceptsDatum owner source value}, AtlasCoverageWitness (AtlasObject a s d)) |
           coverageResultCovers owner source result} @-}
coveragePair
  :: Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d)
  -> (d object, AtlasCoverageWitness (AtlasObject a s d))
coveragePair _owner _source datum witness = (datum, witness)

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
            withAtlasTerritory valueAtlas territoryIndex
              (coverageCandidateAtRegion valueAtlas source sourceDatum datumRank)

{-@ coverageCandidateAtRegion :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> Natural
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> Maybe ({witness:AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum witness}) @-}
coverageCandidateAtRegion
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural
  -> PageElement s regionObject
  -> Maybe (AtlasCoverageWitness (AtlasObject a s d))
coverageCandidateAtRegion owner source sourceDatum datumRank region =
  case unrank (atlasDataAt owner region) datumRank of
    Nothing -> Nothing
    Just regionDatum
      | atlasOriginImageRank owner source sourceDatum
          == atlasOriginImageRank owner region regionDatum ->
          coverageMaybe owner source sourceDatum
            (coverageRegionWitness owner region regionDatum)
      | otherwise -> Nothing

{-@ coverageMaybe :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum witness}
      -> Maybe ({result:AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner source datum result}) @-}
coverageMaybe
  :: Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d)
  -> Maybe (AtlasCoverageWitness (AtlasObject a s d))
coverageMaybe _owner _source _datum witness = Just witness
