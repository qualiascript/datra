{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hidden implementation of coalitions and the Coalizing functor.
module Coalition.Internal
  ( CoalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalition
  , stableCoalitionMap
  , coalizingFunctorObject
  , coalizingFunctorHom
  , coalizingFunctorIdentity
  , coalizingFunctorComposition
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasOriginCell
  , mapAtlasData
  , withAtlasMorphismImage
  )
import Atlas.Morphism.Internal (AtlasWitness (..))
import AtlasCovered.Internal
  ( AtlasCoveredDatum (..)
  , AtlasCoverageWitness (..)
  , atlasCoverageAt
  , atlasCoverageWitness
  , findAtlasCoverageRank
  )
import AtlasTransposal
  ( atlasTransposalElement
  , withAtlasTransposalElement
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , composeInsertions
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , pageElementArrow
  , withPageElement
  )
import StableAtlasTransversal
  ( StableAtlasTransversal
  , composeStableAtlasTransversals
  , identityStableAtlasTransversal
  , mapStableAtlasTransversalCoveredDatum
  , mapStableAtlasTransversalData
  , stableAtlasTransversalPreimage
  )

-- | An element of an Atlas coalition.
--
-- Like 'AtlasCoveredDatum', this is a dependent datum paired with the witness
-- that it is retained by charting.  Carrying the value and witness together
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

coalitionCoverageRank :: AtlasCoverageWitness atlasObject -> Natural
coalitionCoverageRank (AtlasCoverageWitness _ _ _ originRank) = originRank

instance Eq (CoalitionElement atlasObject) where
  CoalitionElement _ _ left == CoalitionElement _ _ right =
    coalitionCoverageRank left == coalitionCoverageRank right

instance Show (CoalitionElement atlasObject) where
  showsPrec _ (CoalitionElement _ _ coverage) =
    showString "CoalitionElement "
      . shows (coalitionCoverageRank coverage)

-- | The rank of the underlying datum in the uncharted origin dominion.
coalitionElementRank :: CoalitionElement atlasObject -> Natural
coalitionElementRank (CoalitionElement _ _ coverage) =
  coalitionCoverageRank coverage

-- | Eliminate a coalition element at its exact dependent origin cell.
withCoalitionElement
  :: CoalitionElement atlasObject
  -> (forall object.
       PageElement (AtlasObjectPaginationScope atlasObject) object
       -> AtlasObjectCellData atlasObject object
       -> result)
  -> result
withCoalitionElement (CoalitionElement origin datum _) useElement =
  useElement origin datum

-- | The extent of the charted Atlas.  Its carrier consists precisely of the
-- covered data in the original Atlas's origin cell.
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

-- | The object action of the Coalizing functor.
coalizingFunctorObject
  :: Atlas atlasScope scope cellData origin final
  -> Dominion
       (CoalitionElement (AtlasObject atlasScope scope cellData))
coalizingFunctorObject = coalition

-- | The component at the source origin, followed by transport from its
-- stable image to the target's canonical origin.  This is the executable
-- Haskell form of Lean's @stableCoalitionMap@.
stableCoalitionMap
  :: AtlasWitness source
  -> AtlasWitness target
  -> StableAtlasTransversal source target
  -> DomanialInsertion
       (CoalitionElement source)
       (CoalitionElement target)
stableCoalitionMap
  sourceWitness@(AtlasWitness sourceAtlas)
  targetWitness@(AtlasWitness targetAtlas)
  stable =
    domanialInsertion mapElement elementPreimage elementLeftInverse
  where
    mapElement
      (CoalitionElement sourceOrigin sourceDatum sourceCoverage) =
        case mapStableAtlasTransversalCoveredDatum stable
          (AtlasCoveredDatum
            sourceOrigin sourceDatum sourceCoverage) of
          AtlasCoveredDatum mappedOrigin mappedDatum targetCoverage ->
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

    elementPreimage
      (CoalitionElement targetOrigin targetDatum targetCoverage) =
      withPageElement (atlasOriginCell sourceAtlas) $ \sourceOrigin ->
        withAtlasMorphismImage
          (mapStableAtlasTransversalData
            sourceWitness stable sourceOrigin) $ \mappedOrigin component ->
              let toCanonicalOrigin =
                    mapAtlasData targetAtlas
                      (pageElementArrow mappedOrigin targetOrigin)
                  originComponent =
                    composeInsertions toCanonicalOrigin component
              in case preimage originComponent targetDatum of
                  Nothing -> Nothing
                  Just sourceDatum ->
                    case targetCoverage of
                      AtlasCoverageWitness
                        targetRegion targetRegionDatum _ _ ->
                          case stableAtlasTransversalPreimage stable
                            (atlasTransposalElement
                              targetWitness targetRegion) of
                              Nothing -> Nothing
                              Just sourceRegionElement ->
                                withAtlasTransposalElement
                                  sourceRegionElement $ \sourceRegion ->
                                    withAtlasMorphismImage
                                      (mapStableAtlasTransversalData
                                        sourceWitness stable sourceRegion) $
                                          \mappedRegion regionComponent ->
                                            let toCoverageRegion =
                                                  mapAtlasData targetAtlas
                                                    (pageElementArrow
                                                      mappedRegion
                                                      targetRegion)
                                                coverageComponent =
                                                  composeInsertions
                                                    toCoverageRegion
                                                    regionComponent
                                            in case preimage
                                              coverageComponent
                                              targetRegionDatum of
                                                Nothing -> Nothing
                                                Just sourceRegionDatum ->
                                                  Just
                                                    (CoalitionElement
                                                      sourceOrigin
                                                      sourceDatum
                                                      (atlasCoverageWitness
                                                        sourceAtlas
                                                        sourceOrigin
                                                        sourceDatum
                                                        sourceRegion
                                                        sourceRegionDatum
                                                        ()))

    elementLeftInverse
      (CoalitionElement sourceOrigin sourceDatum _) =
        withAtlasMorphismImage
          (mapStableAtlasTransversalData
            sourceWitness stable sourceOrigin) $ \mappedOrigin component ->
              withPageElement
                (atlasOriginCell targetAtlas) $ \targetOrigin ->
                  insertionLeftInverse component sourceDatum `seq`
                  insertionLeftInverse
                    (mapAtlasData targetAtlas
                      (pageElementArrow mappedOrigin targetOrigin))
                    (applyInsertion component sourceDatum)

-- | The arrow action of the Coalizing functor.
coalizingFunctorHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> StableAtlasTransversal source target
  -> DomanialInsertion
       (CoalitionElement source)
       (CoalitionElement target)
coalizingFunctorHom = stableCoalitionMap

-- | Pointwise identity law for the Coalizing functor.
coalizingFunctorIdentity
  :: AtlasWitness object
  -> CoalitionElement object
  -> ()
coalizingFunctorIdentity witness = insertionLeftInverse
      (stableCoalitionMap
        witness witness identityStableAtlasTransversal)

-- | Pointwise composition law for the Coalizing functor.
coalizingFunctorComposition
  :: AtlasWitness source
  -> AtlasWitness middle
  -> AtlasWitness target
  -> StableAtlasTransversal source middle
  -> StableAtlasTransversal middle target
  -> CoalitionElement source
  -> ()
coalizingFunctorComposition
  sourceWitness middleWitness targetWitness first second element =
    insertionLeftInverse firstMap element `seq`
      insertionLeftInverse secondMap
        (applyInsertion firstMap element) `seq`
          insertionLeftInverse directMap element
  where
    firstMap =
      stableCoalitionMap sourceWitness middleWitness first

    secondMap =
      stableCoalitionMap middleWitness targetWitness second

    directMap =
      stableCoalitionMap
        sourceWitness
        targetWitness
        (composeStableAtlasTransversals second first)
