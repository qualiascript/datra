{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Coalition carriers and the forward action, independent of stable arrows.
module Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData (..)
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElement
  , coalitionElementRank
  , coalitionElementSource
  , coalitionElementCode
  , coalitionCoveredElement
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  ) where

import Atlas
  ( Atlas, AtlasObject, AtlasObjectAtlasScope, AtlasObjectCellData, AtlasObjectPaginationScope
  , atlasOriginCell, mapAtlasData )
import AtlasCoveredPageElement
  ( CoveredPageElement, CoverageWitness, atlasCoverageAt, atlasCoverageWitness
  , atlasCoveredByWitness, atlasCoveredPageElementWitness, withAtlasCoveredPageElement
  , withAtlasCoverageWitness, coverageWitnessOriginRank )
import Charter.Data
  ( ChartedDatum, chartCellData, chartedCellDataValue, chartedCellDataRank, chartedCellCoverage )
import AtlasTransversal (AtlasTransversal, mapAtlasTransversalCoveredPageElement)
import DomanialInsertion (applyInsertion)
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements (PageElement, pageElementArrow, withPageElement)
import PageElements.Structure (SomePageElement (..))

-- | A coalition stores the canonical charted origin datum and its origin rank.
-- Coverage witnesses are reconstructed from the canonical code when needed.
type CoalitionElement atlasObject =
  CoalitionData (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoalitionData nominal nominal nominal
data CoalitionData atlasScope scope cellData where
  CoalitionElement :: forall atlasScope scope cellData object.
    PageElement scope object -> ChartedDatum atlasScope scope cellData object
    -> Natural -> CoalitionData atlasScope scope cellData

-- | A public read-only view: constructing a view cannot construct a coalition.
data CoalitionView scope cellData where
  CoalitionView :: forall scope cellData object.
    PageElement scope object -> cellData object -> CoalitionView scope cellData

viewCoalitionElement :: CoalitionData a s d -> CoalitionView s d
viewCoalitionElement (CoalitionElement source datum _) =
  CoalitionView source (chartedCellDataValue datum)

coalitionElement :: PageElement s object -> ChartedDatum a s d object -> Natural -> CoalitionData a s d
coalitionElement = CoalitionElement

coalitionElementSource :: CoalitionData a s d -> SomePageElement s
coalitionElementSource (CoalitionElement source _ _) = SomePageElement source

coalitionElementCode :: CoalitionData a s d -> Natural
coalitionElementCode (CoalitionElement _ datum _) = chartedCellDataRank datum

coalitionCoveredElement :: Atlas a s d o f -> CoalitionData a s d -> CoveredPageElement a s d
coalitionCoveredElement owner (CoalitionElement source datum _) =
  atlasCoveredByWitness owner source (chartedCellDataValue datum) (chartedCellCoverage owner source datum)

instance Eq (CoalitionData a s d) where
  (==) = coalitionElementsEqual

-- ALIGN: COALITION-EQUALITY.
coalitionElementsEqual :: CoalitionData a s d -> CoalitionData a s d -> Bool
coalitionElementsEqual left right = coalitionElementRank left == coalitionElementRank right

instance Show (CoalitionData a s d) where
  showsPrec _ element =
    showString "CoalitionElement " . shows (coalitionElementRank element)

-- | The rank of the underlying datum in the uncharted origin dominion.
-- ALIGN: COALITION-CACHED-RANK.
coalitionElementRank :: CoalitionData a s d -> Natural
coalitionElementRank (CoalitionElement _ _ originRank) = originRank

-- | Eliminate a coalition element at its exact dependent origin cell.
-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
withCoalitionElement
  :: CoalitionData atlasScope scope cellData
  -> (forall object.
       PageElement scope object
       -> cellData object
       -> result)
  -> result
withCoalitionElement element useElement = case viewCoalitionElement element of
  CoalitionView source datum -> useElement source datum

-- | Read a coalition datum at another occurrence of the canonical origin
-- cell.  The Atlas data action supplies the dependent transport, so no cast
-- or partial pattern match is required.
-- ALIGN: COALITION-DATUM-TRANSPORT.
coalitionElementAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> CoalitionElement (AtlasObject atlasScope scope cellData)
  -> cellData targetObject
coalitionElementAt valueAtlas target element =
  withCoalitionElement element $ \source datum ->
    applyInsertion (mapAtlasData valueAtlas (pageElementArrow source target)) datum

-- | Transport a coalition element to an exact origin occurrence while
-- retaining a coverage witness for the transported datum.
-- ALIGN: COALITION-COVERAGE-TRANSPORT.
coalitionElementCoverageAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> CoalitionElement (AtlasObject atlasScope scope cellData)
  -> CoverageWitness atlasScope scope cellData
coalitionElementCoverageAt valueAtlas target
    element@(CoalitionElement source datum _) =
  withAtlasCoverageWitness valueAtlas (chartedCellCoverage valueAtlas source datum) $ \region regionDatum ->
      atlasCoverageWitness
        valueAtlas
        target
        (coalitionElementAt valueAtlas target element)
        region
        regionDatum
        ()

-- | The extent of the charted Atlas.  Its carrier consists precisely of the
-- covered page elements in the original Atlas's origin cell.
-- ALIGN: COALITION-CARRIER-EQUIVALENCE.
-- ALIGN: COALITION-ROUNDTRIP.
coalition
  :: Atlas atlasScope scope cellData origin final
  -> Dominion
       (CoalitionElement (AtlasObject atlasScope scope cellData))
coalition valueAtlas =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    let coalitionUnrank candidate =
          case atlasCoverageAt valueAtlas origin candidate of
            Nothing -> Nothing
            Just (datum, witness) -> Just (CoalitionElement origin
              (chartCellData valueAtlas origin datum witness ()) (coverageWitnessOriginRank witness))
    in dominion coalitionElementCode coalitionUnrank (const ())

-- | Apply the transversal and transport its covered image to the target origin.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
mapCoalitionElement
  :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> CoalitionData sourceAtlasScope sourceScope sourceCellData
  -> CoalitionData targetAtlasScope targetScope targetCellData
mapCoalitionElement sourceAtlas targetAtlas transversal element =
  let covered = coalitionCoveredElement sourceAtlas element
      mapped = mapAtlasTransversalCoveredPageElement transversal covered
  in withAtlasCoveredPageElement mapped $ \mappedOrigin mappedDatum ->
    withPageElement (atlasOriginCell targetAtlas) $ \targetOrigin ->
      let toCanonicalOrigin =
            mapAtlasData targetAtlas (pageElementArrow mappedOrigin targetOrigin)
          targetDatum = applyInsertion toCanonicalOrigin mappedDatum
      in withAtlasCoverageWitness targetAtlas (atlasCoveredPageElementWitness mapped) $
          \targetRegion targetRegionDatum ->
            let targetWitness = atlasCoverageWitness targetAtlas targetOrigin targetDatum
                  targetRegion targetRegionDatum ()
            in CoalitionElement targetOrigin
              (chartCellData targetAtlas targetOrigin targetDatum targetWitness ())
              (coverageWitnessOriginRank targetWitness)
