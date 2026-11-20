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
  , CoverageWitness
  , AtlasCoveredPageElement (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessCode
  , coverageWitnessAlongArrow
  , coverageFinalPage
  , coverageNormalize
  , atlasOriginImageRank
  , findAtlasCoverage
  , findAtlasCoverageRank
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , atlasCoverageRankWithin
  , atlasCoverageRankLeast
  , atlasCoveredPageElementAt
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , atlasCoveredPageElementWitness
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectAtlasScope
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
import DatraOrdinal (ordinal, ordinalCoefficients)
import Dominion (rank, unrank)
import Numeric.Natural (Natural)
import Data.Kind (Type)
import NaturalEncoding (pairNatural, unpairNatural, encodeNaturalList, decodeNaturalList)
import PageElements.Structure
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElementPage
  , pageElementPosition
  )

-- | The existential witness in Lean's @Covered X x t@ predicate: a datum in
-- a final region whose image in the origin is the image of the source datum.
-- Its constructor is hidden; 'atlasCoverageWitness' is the checked
-- introduction rule.
type AtlasCoverageWitness atlasObject =
  CoverageWitness (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoverageWitness nominal nominal nominal
{-@ data CoverageWitness a s d where
      AtlasCoverageWitness :: forall a s d object.
        payload:CoverageRegionData s d object -> CoverageWitness a s d @-}
data CoverageWitness (atlasScope :: Type) scope cellData where
  AtlasCoverageWitness
    :: forall atlasScope scope cellData regionObject.
       CoverageRegionData scope cellData regionObject
    -> CoverageWitness atlasScope scope cellData

type role CoverageRegionData nominal nominal nominal
{-@ data CoverageRegionData s d object = CoverageRegionData
      { coverageRegion :: PageElement s object
      , coverageRegionDatum :: d object
      , coverageRegionPage :: Natural
      , coverageRegionRank :: Natural
      } @-}
data CoverageRegionData scope cellData regionObject = CoverageRegionData
  { coverageRegion :: PageElement scope regionObject
  , coverageRegionDatum :: cellData regionObject
  , coverageRegionPage :: Natural
  , coverageRegionRank :: Natural
  }

-- | Observe the certified final region and its accepted datum through the
-- owning Atlas, retaining the equality with the witness's cached origin rank.
-- ALIGN: ATLAS-COVERAGE-ELIM.
{-@ withAtlasCoverageWitness :: owner:Atlas a s d o f
      -> witness:{CoverageWitness a s d | coverageWitnessValid owner witness}
      -> (forall object. region:{PageElement s object | cellTraceValid owner region
             && coveragePage region == coverageFinalPage owner}
            -> datum:{d object | atlasAcceptsDatum owner region datum
                 && atlasOriginImageRank owner region datum == coverageWitnessOriginRank witness}
            -> result)
      -> result @-}
withAtlasCoverageWitness
  :: Atlas a s d o f -> CoverageWitness a s d
  -> (forall object. PageElement s object -> d object -> result)
  -> result
withAtlasCoverageWitness _owner (AtlasCoverageWitness value) useRegion =
  useRegion (coverageRegion value) (coverageRegionDatum value)

-- ALIGN: ATLAS-COVERAGE-RANK-OBSERVE.
{-@ reflect coverageWitnessOriginRank @-}
coverageWitnessOriginRank :: CoverageWitness a s d -> Natural
coverageWitnessOriginRank (AtlasCoverageWitness value) = coverageRegionRank value

-- | Encode the actual retained final region and its datum, independently
-- of the cached origin rank used to compare coverage.
-- ALIGN: ATLAS-COVERAGE-WITNESS-CODE.
{-@ coverageWitnessCode :: owner:Atlas a s d o f
      -> witness:{CoverageWitness a s d | coverageWitnessValid owner witness} -> Natural @-}
coverageWitnessCode :: Atlas a s d o f -> CoverageWitness a s d -> Natural
coverageWitnessCode owner witness =
  withAtlasCoverageWitness owner witness $ \region datum ->
    pairNatural (encodeNaturalList (ordinalCoefficients (pageElementPosition region)))
      (rank (atlasDataAt owner region) datum)

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
  :: forall a s d o f. Atlas a s d o f -> CoverageWitness a s d -> Bool
coverageWitnessValid owner
    (AtlasCoverageWitness (value :: CoverageRegionData s d object)) =
  coverageRegionDataValid owner value

{-@ reflect coverageRegionDataValid @-}
coverageRegionDataValid :: Atlas a s d o f -> CoverageRegionData s d object -> Bool
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
  -> CoverageWitness a s d -> Bool
coverageWitnessCovers owner source sourceDatum witness
  | cellTraceValid owner source
  , atlasAcceptsDatum owner source sourceDatum =
      coverageWitnessAtRank owner (atlasOriginImageRank owner source sourceDatum) witness
  | otherwise = False

{-@ reflect coverageWitnessAtRank @-}
coverageWitnessAtRank
  :: forall a s d o f. Atlas a s d o f -> Natural
  -> CoverageWitness a s d -> Bool
coverageWitnessAtRank owner sourceRank
    (AtlasCoverageWitness (value :: CoverageRegionData s d regionObject)) =
  coverageRegionDataValid owner value
    && coverageRegionPage value == coverageFinalPage owner
    && sourceRank == coverageRegionRank value

-- | A witness for a transported datum also covers the original datum.
-- ALIGN: ATLAS-COVERAGE-TRANSPORT.
{-@ coverageWitnessAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner (arrowTarget arrow)
             (applyInsertion (mapAtlasData owner arrow) datum) witness}
      -> {coverageWitnessCovers owner (arrowSource arrow) datum witness} @-}
coverageWitnessAlongArrow
  :: Atlas a s d o f -> PageElementArrow s source target -> d source
  -> CoverageWitness a s d -> ()
coverageWitnessAlongArrow owner arrow datum _witness =
  cellTraceHasOrigin owner (arrowSource arrow) `seq`
  cellTraceHasOrigin owner (arrowTarget arrow) `seq`
  cellOriginRankMap owner arrow datum

{-@ coverageRegionWitness :: owner:Atlas a s d o f
      -> region:{PageElement s object | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> datum:{d object | atlasAcceptsDatum owner region datum}
      -> {witness:CoverageWitness a s d |
           coverageWitnessValid owner witness && coverageWitnessCovers owner region datum witness} @-}
coverageRegionWitness
  :: forall a s d o f object. Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
coverageRegionWitness owner region datum =
  AtlasCoverageWitness (CoverageRegionData region datum
    (coveragePage region) (atlasOriginImageRank owner region datum))

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
  -> { witness:CoverageWitness atlasScope scope cellData |
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
  -> CoverageWitness atlasScope scope cellData
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
      -> CoverageWitness a s d @-}
findAtlasCoverage
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> CoverageWitness atlasScope scope cellData
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
    go candidate
      | coverageRankCandidate valueAtlas source sourceDatum candidate = candidate
      | otherwise = go (candidate + 1)

-- | Test whether a finite candidate decodes the requested source datum.
{-@ opaque-reflect atlasCoveredPageElementAt @-}
{-@ reflect coverageRankCandidate @-}
{-@ coverageRankCandidate :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural -> Bool @-}
coverageRankCandidate
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Bool
coverageRankCandidate owner source datum candidate =
  case atlasCoveredPageElementAt owner source candidate of
    Nothing -> False
    Just value -> rank (atlasDataAt owner source) value == rank (atlasDataAt owner source) datum

-- | Search the inclusive interval from zero through the supplied limit.
-- ALIGN: ATLAS-COVERAGE-BOUNDED-RANK.
{-@ reflect atlasCoverageRankWithin @-}
{-@ atlasCoverageRankWithin :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> Maybe ({found:Natural | found <= limit && coverageRankCandidate owner source datum found}) @-}
atlasCoverageRankWithin
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe Natural
atlasCoverageRankWithin owner source datum limit = searchCoverageRank owner source datum 0 limit

{-@ reflect searchCoverageRank @-}
{-@ searchCoverageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> candidate:Natural -> remaining:Natural
      -> Maybe ({found:Natural | candidate <= found && found <= candidate + remaining
           && coverageRankCandidate owner source datum found}) / [remaining] @-}
searchCoverageRank
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Natural -> Maybe Natural
searchCoverageRank owner source datum candidate remaining
  | coverageRankCandidate owner source datum candidate = Just candidate
  | remaining == 0 = Nothing
  | otherwise = searchCoverageRank owner source datum (candidate + 1) (remaining - 1)

-- | A successful bounded search selects the least successful candidate.
-- ALIGN: ATLAS-COVERAGE-BOUNDED-MINIMAL.
{-@ atlasCoverageRankLeast :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> found:{Natural | atlasCoverageRankWithin owner source datum limit == Just found}
      -> earlier:{Natural | earlier < found}
      -> {not (coverageRankCandidate owner source datum earlier)} @-}
atlasCoverageRankLeast
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Natural -> Natural -> ()
atlasCoverageRankLeast owner source datum limit found earlier =
  searchCoverageRankLeast owner source datum 0 limit found earlier

{-@ searchCoverageRankLeast :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> candidate:Natural -> remaining:Natural
      -> found:{Natural | searchCoverageRank owner source datum candidate remaining == Just found}
      -> earlier:{Natural | candidate <= earlier && earlier < found}
      -> {not (coverageRankCandidate owner source datum earlier)} / [remaining] @-}
searchCoverageRankLeast
  :: Atlas a s d o f -> PageElement s object -> d object
  -> Natural -> Natural -> Natural -> Natural -> ()
searchCoverageRankLeast owner source datum candidate remaining found earlier
  | coverageRankCandidate owner source datum candidate = ()
  | remaining == 0 = ()
  | earlier == candidate = ()
  | otherwise = searchCoverageRankLeast owner source datum (candidate + 1) (remaining - 1) found earlier

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
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
atlasCoverageAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe
       ( cellData object
       , CoverageWitness atlasScope scope cellData
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
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
coverageAtRegion
  :: Atlas a s d o f -> PageElement s object -> Natural
  -> PageElement s regionObject
  -> Maybe (d object, CoverageWitness a s d)
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
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> {result:({value:d object | atlasAcceptsDatum owner source value}, CoverageWitness a s d) |
           coverageResultCovers owner source result} @-}
coveragePair
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
  -> (d object, CoverageWitness a s d)
coveragePair _owner _source datum witness = (datum, witness)

-- | The decoder retains coverage for the exact datum returned alongside it.
{-@ reflect coverageResultCovers @-}
coverageResultCovers
  :: Atlas a s d o f -> PageElement s object
  -> (d object, CoverageWitness a s d) -> Bool
coverageResultCovers owner source (datum, witness) =
  coverageWitnessCovers owner source datum witness

{-@ lazy searchAtlasCoverageFrom @-}
{-@ searchAtlasCoverageFrom :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural
      -> CoverageWitness a s d @-}
searchAtlasCoverageFrom
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
  -> CoverageWitness atlasScope scope cellData
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
      -> Maybe ({witness:CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}) @-}
coverageCandidate
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
  -> Maybe (CoverageWitness atlasScope scope cellData)
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
      -> Maybe ({witness:CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}) @-}
coverageCandidateAtRegion
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural
  -> PageElement s regionObject
  -> Maybe (CoverageWitness a s d)
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
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> Maybe ({result:CoverageWitness a s d |
           coverageWitnessCovers owner source datum result}) @-}
coverageMaybe
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
  -> Maybe (CoverageWitness a s d)
coverageMaybe _owner _source _datum witness = Just witness
