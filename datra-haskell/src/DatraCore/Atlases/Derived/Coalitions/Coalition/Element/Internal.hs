{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Coalition carriers and the forward action, independent of stable arrows.
module Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData (..)
  , coalitionElement
  , coalitionElementRank
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
  ( CoveredPageElement, CoverageWitness, atlasCoveredAt, atlasCoverageWitness
  , atlasCoveredByWitness, atlasCoveredPageElementWitness, withAtlasCoveredPageElement
  , withAtlasCoverageWitness, coverageWitnessOriginRank, atlasCoverageRank )
import AtlasTransversal (AtlasTransversal, mapAtlasTransversalCoveredPageElement)
import DomanialInsertion (applyInsertion)
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements (PageElement, pageElementArrow, withPageElement)

-- | A coalition element retains a covered origin datum through the shared
-- covered-element carrier. Its public constructor checks the origin condition.
type CoalitionElement atlasObject =
  CoalitionData (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoalitionData nominal nominal nominal
data CoalitionData atlasScope scope cellData = CoalitionElement
  (CoveredPageElement atlasScope scope cellData)

coalitionElement :: CoveredPageElement a s d -> CoalitionData a s d
coalitionElement = CoalitionElement

coalitionCoveredElement :: CoalitionData a s d -> CoveredPageElement a s d
coalitionCoveredElement (CoalitionElement covered) = covered

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
coalitionElementRank element =
  coverageWitnessOriginRank (atlasCoveredPageElementWitness (coalitionCoveredElement element))

-- | Eliminate a coalition element at its exact dependent origin cell.
-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
withCoalitionElement
  :: CoalitionData atlasScope scope cellData
  -> (forall object.
       PageElement scope object
       -> cellData object
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
    let coalitionRank element@(CoalitionElement covered) =
          withCoalitionElement element $ \occurrence datum ->
            atlasCoverageRank valueAtlas occurrence datum (atlasCoveredPageElementWitness covered)

        coalitionUnrank candidate =
          CoalitionElement <$> atlasCoveredAt valueAtlas origin candidate
    in dominion coalitionRank coalitionUnrank (const ())

-- | Apply the transversal and transport its covered image to the target origin.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
mapCoalitionElement
  :: Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> CoalitionData sourceAtlasScope sourceScope sourceCellData
  -> CoalitionData targetAtlasScope targetScope targetCellData
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
