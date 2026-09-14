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
  ( AtlasCoverageWitness
  , AtlasCoveredDatum (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageFinalPage
  , coverageNormalize
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
  , mapAtlasData
  , normalizeAtlasElement
  )
import DomanialInsertion (applyInsertion)
import Dominion (rank)
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
