{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed Natural as int @-}

-- | Hidden implementation of coverage by final Atlas regions.
module AtlasCovered.Internal
  ( AtlasCoverageWitness (..)
  , AtlasCoveredDatum (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageFinalPage
  , coverageNormalize
  , atlasOriginImageRank
  , findAtlasCoverage
  , findAtlasCoverageRank
  , atlasCoverageAt
  , atlasCoveredDatumAt
  , atlasCoveredDatum
  , withAtlasCoveredDatum
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , atlasCardinality
  , atlasDataAt
  , atlasOriginCell
  , atlasTerritory
  , atlasTerritoryChain
  , withAtlasCellDominion
  , mapAtlasData
  , normalizeAtlasElement
  )
import DomanialInsertion (applyInsertion, preimage)
import Chain (chainIndex)
import DatraOrdinal (ordinal)
import Dominion (rank, unrank)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , pageElementArrow
  , pageElementPage
  , withPageElement
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

-- | A datum paired with evidence that it is covered by a final region.
type role AtlasCoveredDatum nominal
data AtlasCoveredDatum atlasObject where
  AtlasCoveredDatum
    :: PageElement (AtlasObjectPaginationScope atlasObject) object
    -> AtlasObjectCellData atlasObject object
    -> AtlasCoverageWitness atlasObject
    -> AtlasCoveredDatum atlasObject

-- | Rank the image of a datum in the Atlas extent. Dominion ranks are
-- injective, so equality of these ranks is equality of the origin images.
{-@ reflect atlasOriginImageRank @-}
atlasOriginImageRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
atlasOriginImageRank valueAtlas occurrence datum =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    rank
      (atlasDataAt valueAtlas origin)
      (applyInsertion
        (mapAtlasData valueAtlas (pageElementArrow occurrence origin))
        datum)

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

-- | The proposition represented by an 'AtlasCoverageWitness'. The first
-- conjunct places its witness on the final genuine page and the second is
-- Lean's equality after both data are transported to the origin.
{-@ reflect coverageWitnessCovers @-}
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
  (AtlasCoverageWitness _ _ regionPage regionOriginRank) =
    regionPage == coverageFinalPage valueAtlas
      && atlasOriginImageRank valueAtlas source sourceDatum
        == regionOriginRank

-- | Introduce a coverage witness. LiquidHaskell checks that the region is on
-- the final page and that its datum has the same origin image as the source.
{-@
atlasCoverageWitness
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:PageElement scope object
  -> sourceDatum:cellData object
  -> region:PageElement scope regionObject
  -> regionDatum:cellData regionObject
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
atlasCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoverageWitness
       (AtlasObject atlasScope scope cellData)
atlasCoverageWitness valueAtlas _ _ region regionDatum _ =
  AtlasCoverageWitness
    (coverageNormalize valueAtlas region)
    regionDatum
    (coveragePage (coverageNormalize valueAtlas region))
    (atlasOriginImageRank
      valueAtlas
      (coverageNormalize valueAtlas region)
      regionDatum)

-- | Construct a covered datum using the checked introduction rule.
{-@
atlasCoveredDatum
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:PageElement scope object
  -> sourceDatum:cellData object
  -> region:PageElement scope regionObject
  -> regionDatum:cellData regionObject
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
  -> AtlasCoveredDatum (AtlasObject atlasScope scope cellData)
@-}
atlasCoveredDatum
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoveredDatum
       (AtlasObject atlasScope scope cellData)
atlasCoveredDatum
  valueAtlas source sourceDatum region regionDatum conditions =
    AtlasCoveredDatum
      (coverageNormalize valueAtlas source)
      sourceDatum
      (atlasCoverageWitness
        valueAtlas source sourceDatum region regionDatum conditions)

-- | Eliminate a covered datum while retaining its dependent cell-data type.
withAtlasCoveredDatum
  :: AtlasCoveredDatum atlasObject
  -> (forall object.
        PageElement (AtlasObjectPaginationScope atlasObject) object
        -> AtlasObjectCellData atlasObject object
        -> result)
  -> result
withAtlasCoveredDatum
  (AtlasCoveredDatum occurrence datum _)
  useCovered = useCovered occurrence datum

-- | Search the countable final territory for a coverage witness. This is the
-- executable counterpart needed because Haskell's 'Dominion' carries an
-- @unrank@ operation whereas Lean's dominions only require a rank embedding.
-- The search terminates exactly on covered data, which is the only domain on
-- which Charting calls it.
findAtlasCoverage
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
findAtlasCoverage valueAtlas source sourceDatum =
  searchAtlasCoverageFrom valueAtlas source sourceDatum 0

-- | The first enumeration index witnessing coverage of a datum. The search
-- is total on the abstract covered carrier used by Charting.
{-@ lazy findAtlasCoverageRank @-}
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
      case atlasCoveredDatumAt valueAtlas source candidate of
        Just candidateDatum
          | rank sourceDominion candidateDatum == sourceRank -> candidate
        _ -> go (candidate + 1)

-- | Decode one finite coverage candidate. A final-region datum is transported
-- to the origin and pulled back along the selected source cell. Unlike a
-- membership filter, this operation terminates for every index.
atlasCoveredDatumAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe (cellData object)
atlasCoveredDatumAt valueAtlas source candidate =
  fst <$> atlasCoverageAt valueAtlas source candidate

-- | Decode one coverage candidate together with the evidence that made it a
-- member of the covered carrier.  Returning the witness alongside the datum
-- lets downstream dependent carriers stay total instead of reconstructing
-- evidence with an unchecked search.
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
            withAtlasCellDominion
              (atlasTerritory valueAtlas territoryIndex) $ \region regionDom ->
                case unrank regionDom datumRank of
                  Nothing -> Nothing
                  Just regionDatum ->
                    withPageElement (atlasOriginCell valueAtlas) $ \origin ->
                      let regionOriginRank =
                            atlasOriginImageRank
                              valueAtlas region regionDatum
                      in case preimage
                        (mapAtlasData
                          valueAtlas (pageElementArrow source origin))
                        (applyInsertion
                          (mapAtlasData
                            valueAtlas (pageElementArrow region origin))
                          regionDatum) of
                            Nothing -> Nothing
                            Just sourceDatum ->
                              Just
                                ( sourceDatum
                                , AtlasCoverageWitness
                                    region
                                    regionDatum
                                    (coverageFinalPage valueAtlas)
                                    regionOriginRank
                                )

{-@ lazy searchAtlasCoverageFrom @-}
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
            withAtlasCellDominion
              (atlasTerritory valueAtlas territoryIndex) $ \region regionDom ->
                case unrank regionDom datumRank of
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

-- | Cantor's diagonal decoding, used twice to enumerate pairs and then all
-- finite coefficient lists. Consequently every ordinal below omega^omega and
-- every datum rank is eventually visited.
{-@ lazy unpairNatural @-}
unpairNatural :: Natural -> (Natural, Natural)
unpairNatural = go 0
  where
    go diagonal remainder
      | remainder <= diagonal = (remainder, diagonal - remainder)
      | otherwise = go (diagonal + 1) (remainder - diagonal - 1)

{-@ lazy decodeNaturalList @-}
decodeNaturalList :: Natural -> [Natural]
decodeNaturalList 0 = []
decodeNaturalList code =
  let (value, rest) = unpairNatural (code - 1)
  in value : decodeNaturalList rest
