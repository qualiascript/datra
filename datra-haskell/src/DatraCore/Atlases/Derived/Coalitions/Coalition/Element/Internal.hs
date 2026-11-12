{-# LANGUAGE GADTs #-}
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
import AtlasCoveredPageElement.Internal
  ( AtlasCoveredPageElement (..), AtlasCoverageWitness (..)
  , atlasCoverageAt, atlasCoverageWitness, findAtlasCoverageRank )
import AtlasTransversal (AtlasTransversal, mapAtlasTransversalCoveredPageElement)
import DomanialInsertion (applyInsertion)
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements (PageElement, pageElementArrow, withPageElement)

-- | An element of an Atlas coalition.
--
-- Like 'AtlasCoveredPageElement', this is a dependent page element paired with
-- its datum and the witness that it is retained by Charter. Carrying the value
-- makes elimination total: no unchecked rank ever has to be decoded.
type role CoalitionElement nominal
data CoalitionElement atlasObject where
  CoalitionElement
    :: PageElement
         (AtlasObjectPaginationScope atlasObject)
         object
    -> AtlasObjectCellData atlasObject object
    -> AtlasCoverageWitness atlasObject
    -> CoalitionElement atlasObject

-- | Internal introduction rule. Public clients obtain coalition
-- elements through 'coalition'; derived constructions may already possess the
-- exact coverage witness and therefore need not search for it again.
coalitionElement
  :: PageElement (AtlasObjectPaginationScope atlasObject) object
  -> AtlasObjectCellData atlasObject object
  -> AtlasCoverageWitness atlasObject
  -> CoalitionElement atlasObject
coalitionElement = CoalitionElement

coalitionCoverageRank :: AtlasCoverageWitness atlasObject -> Natural
coalitionCoverageRank (AtlasCoverageWitness _ _ _ originRank) = originRank

instance Eq (CoalitionElement atlasObject) where
  (==) = coalitionElementsEqual

-- ALIGN: COALITION-EQUALITY.
coalitionElementsEqual :: CoalitionElement atlasObject -> CoalitionElement atlasObject -> Bool
coalitionElementsEqual left right = coalitionElementRank left == coalitionElementRank right

instance Show (CoalitionElement atlasObject) where
  showsPrec _ (CoalitionElement _ _ coverage) =
    showString "CoalitionElement "
      . shows (coalitionCoverageRank coverage)

-- | The rank of the underlying datum in the uncharted origin dominion.
-- ALIGN: COALITION-CACHED-RANK.
coalitionElementRank :: CoalitionElement atlasObject -> Natural
coalitionElementRank (CoalitionElement _ _ coverage) =
  coalitionCoverageRank coverage

-- | Eliminate a coalition element at its exact dependent origin cell.
-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
withCoalitionElement
  :: CoalitionElement atlasObject
  -> (forall object.
       PageElement (AtlasObjectPaginationScope atlasObject) object
       -> AtlasObjectCellData atlasObject object
       -> result)
  -> result
withCoalitionElement (CoalitionElement origin datum _) useElement =
  useElement origin datum

-- | Read a coalition datum at another occurrence of the canonical origin
-- cell.  The Atlas data action supplies the dependent transport, so no cast
-- or partial pattern match is required.
-- ALIGN: COALITION-DATUM-TRANSPORT.
coalitionElementAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> CoalitionElement (AtlasObject atlasScope scope cellData)
  -> cellData targetObject
coalitionElementAt valueAtlas target
    (CoalitionElement source datum _) =
  applyInsertion
    (mapAtlasData valueAtlas (pageElementArrow source target))
    datum

-- | Transport a coalition element to an exact origin occurrence while
-- retaining a coverage witness for the transported datum.
-- ALIGN: COALITION-COVERAGE-TRANSPORT.
coalitionElementCoverageAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> CoalitionElement (AtlasObject atlasScope scope cellData)
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
coalitionElementCoverageAt valueAtlas target
    element@(CoalitionElement _ _ coverage) =
  case coverage of
    AtlasCoverageWitness region regionDatum _ _ ->
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
    let coalitionRank (CoalitionElement occurrence datum _) =
          findAtlasCoverageRank valueAtlas occurrence datum

        coalitionUnrank candidate = do
          (datum, coverage) <-
            atlasCoverageAt valueAtlas origin candidate
          pure
            (CoalitionElement
              origin
              datum
              coverage)
    in dominion coalitionRank coalitionUnrank (const ())

-- | Apply the transversal and transport its covered image to the target origin.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
mapCoalitionElement
  :: Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasTransversal source (AtlasObject targetAtlasScope targetScope targetCellData)
  -> CoalitionElement source
  -> CoalitionElement (AtlasObject targetAtlasScope targetScope targetCellData)
mapCoalitionElement targetAtlas transversal
  (CoalitionElement sourceOrigin sourceDatum sourceCoverage) =
    case mapAtlasTransversalCoveredPageElement transversal
      (AtlasCoveredPageElement
        sourceOrigin sourceDatum sourceCoverage) of
      AtlasCoveredPageElement mappedOrigin mappedDatum targetCoverage ->
        withPageElement
          (atlasOriginCell targetAtlas) $ \targetOrigin ->
            let toCanonicalOrigin =
                  mapAtlasData targetAtlas
                    (pageElementArrow mappedOrigin targetOrigin)
                targetDatum =
                  applyInsertion toCanonicalOrigin mappedDatum
            in case targetCoverage of
                AtlasCoverageWitness
                  targetRegion targetRegionDatum _ _ ->
                    CoalitionElement
                      targetOrigin
                      targetDatum
                      (atlasCoverageWitness
                        targetAtlas
                        targetOrigin
                        targetDatum
                        targetRegion
                        targetRegionDatum
                        ())
