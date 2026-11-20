{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Coalition carriers and the forward action, independent of stable arrows.
module Coalition.Element.Internal
  ( CoalitionElement
  , coalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  ) where

import Atlas
  ( Atlas, AtlasObject, AtlasObjectCellData, AtlasObjectPaginationScope
  , atlasOriginCell, mapAtlasData )
import AtlasCoveredPageElement.Internal (findAtlasCoverageRank)
import AtlasCoveredPageElement
  ( AtlasCoveredPageElement, CoverageWitness, atlasCoveredAt, atlasCoverageWitness
  , atlasCoveredByWitness, atlasCoveredPageElementWitness, withAtlasCoveredPageElement
  , withAtlasCoverageWitness, coverageWitnessOriginRank )
import AtlasTransversal (AtlasTransversal, mapAtlasTransversalCoveredPageElement)
import DomanialInsertion (applyInsertion)
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements (PageElement, pageElementArrow, withPageElement)

-- | A coalition element retains a covered origin datum through the shared
-- covered-element carrier. Its public constructor checks the origin condition.
type role CoalitionElement nominal
data CoalitionElement atlasObject = CoalitionElement
  (AtlasCoveredPageElement atlasObject)

coalitionElement :: AtlasCoveredPageElement atlasObject -> CoalitionElement atlasObject
coalitionElement = CoalitionElement

instance Eq (CoalitionElement atlasObject) where
  (==) = coalitionElementsEqual

-- ALIGN: COALITION-EQUALITY.
coalitionElementsEqual :: CoalitionElement atlasObject -> CoalitionElement atlasObject -> Bool
coalitionElementsEqual left right = coalitionElementRank left == coalitionElementRank right

instance Show (CoalitionElement atlasObject) where
  showsPrec _ element =
    showString "CoalitionElement " . shows (coalitionElementRank element)

-- | The rank of the underlying datum in the uncharted origin dominion.
-- ALIGN: COALITION-CACHED-RANK.
coalitionElementRank :: CoalitionElement atlasObject -> Natural
coalitionElementRank (CoalitionElement covered) =
  coverageWitnessOriginRank (atlasCoveredPageElementWitness covered)

-- | Eliminate a coalition element at its exact dependent origin cell.
-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
withCoalitionElement
  :: CoalitionElement atlasObject
  -> (forall object.
       PageElement (AtlasObjectPaginationScope atlasObject) object
       -> AtlasObjectCellData atlasObject object
       -> result)
  -> result
withCoalitionElement (CoalitionElement covered) = withAtlasCoveredPageElement covered

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
    element@(CoalitionElement covered) =
  withAtlasCoverageWitness valueAtlas (atlasCoveredPageElementWitness covered) $ \region regionDatum ->
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
    let coalitionRank element =
          withCoalitionElement element $ \occurrence datum ->
            findAtlasCoverageRank valueAtlas occurrence datum

        coalitionUnrank candidate =
          CoalitionElement <$> atlasCoveredAt valueAtlas origin candidate
    in dominion coalitionRank coalitionUnrank (const ())

-- | Apply the transversal and transport its covered image to the target origin.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
mapCoalitionElement
  :: Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal source (AtlasObject targetAtlasScope targetScope targetCellData)
  -> CoalitionElement source
  -> CoalitionElement (AtlasObject targetAtlasScope targetScope targetCellData)
mapCoalitionElement targetAtlas transversal (CoalitionElement covered) =
  let mapped = mapAtlasTransversalCoveredPageElement transversal covered
  in withAtlasCoveredPageElement mapped $ \mappedOrigin mappedDatum ->
    withPageElement (atlasOriginCell targetAtlas) $ \targetOrigin ->
      let toCanonicalOrigin =
            mapAtlasData targetAtlas (pageElementArrow mappedOrigin targetOrigin)
          targetDatum = applyInsertion toCanonicalOrigin mappedDatum
      in withAtlasCoverageWitness targetAtlas (atlasCoveredPageElementWitness mapped) $
          \targetRegion targetRegionDatum ->
            CoalitionElement (atlasCoveredByWitness targetAtlas targetOrigin targetDatum
              (atlasCoverageWitness targetAtlas targetOrigin targetDatum
                targetRegion targetRegionDatum ()))
