{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | The specification operator from a total Atlas map into one selected
-- member of an Atlas-map federation.
module SpecificationOperator
  ( IdentityPaginationTransversal
  , paginationActsAsIdentityAt
  , identityPaginationTransversal
  , identityPaginationUnderlying
  , Specification
  , specificationOperator
  , specificationSource
  , specificationTarget
  , specificationTargetIndex
  , specificationMorphism
  , AtlasMapFederationDecision (..)
  ) where

import AtlasConfederation
  ( atlasConfederationComponent
  , atlasConfederationComponentHom
  , atlasConfederationHom
  , composeAtlasConfederationHoms
  , singletonAtlasConfederation
  , withAtlasConfederationComponent
  )
import Atlas qualified
import AtlasFederation (atlasFederationConfederation)
import AtlasMap (atlasMapAtlas)
import AtlasMapFederation
  ( AtlasMapFederation
  , atlasMapFederationAtlasFederation
  )
import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..) )
import PageElements
  ( PageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
import StableAtlasTransversal
  ( StableAtlasTransversal
  , mapStableAtlasTransversalElement
  )
import StableConfederalData
  ( EmbeddedAtlasFederation
  , EmbeddedAtlasMap
  , StableConfederalDataHom
  , embedAtlasFederation
  , embedAtlasMap
  , embeddedAtlasFederationValue
  , stableConfederalDataHom
  )
import TotalAtlasMap
  ( TotalAtlasMap
  , totalAtlasMapUnderlying
  )
import Atlas.Morphism.Internal (AtlasWitness (AtlasWitness))

-- | A stable Atlas transversal whose pagination action is certified to be
-- the identity after identifying the structurally equal source and target
-- paginations.  The proof is erased at runtime and remains independent of
-- the data injections carried by the transversal.
type role IdentityPaginationTransversal nominal nominal
data IdentityPaginationTransversal source target =
  IdentityPaginationTransversal
    (AtlasWitness source)
    (StableAtlasTransversal source target)
    (forall object.
       PageElement
         (Atlas.AtlasObjectPaginationScope source)
         object
       -> ())

-- | Executable statement witnessed by an
-- 'IdentityPaginationTransversal': every source page element is sent to the
-- same page and ordinal position.
paginationActsAsIdentityAt
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> PageElement
       (Atlas.AtlasObjectPaginationScope source)
       object
  -> Bool
paginationActsAsIdentityAt sourceWitness transversal sourceElement =
  withPageElement
    (mapStableAtlasTransversalElement
      sourceWitness transversal sourceElement) $ \targetElement ->
        pageElementPage targetElement == pageElementPage sourceElement
          && pageElementPosition targetElement
            == pageElementPosition sourceElement

identityPaginationTransversal
  :: AtlasWitness source
  -> StableAtlasTransversal source target
  -> (forall object.
       PageElement
         (Atlas.AtlasObjectPaginationScope source)
         object
       -> ())
  -> IdentityPaginationTransversal source target
identityPaginationTransversal = IdentityPaginationTransversal

identityPaginationUnderlying
  :: IdentityPaginationTransversal source target
  -> StableAtlasTransversal source target
identityPaginationUnderlying
    (IdentityPaginationTransversal _ transversal _) = transversal

-- | A successful specification.  The existential target of the component
-- arrow is the Atlas selected by 'specificationTargetIndex'.
type role Specification nominal nominal nominal
data Specification federationScope index source = Specification
  (TotalAtlasMap source)
  (AtlasMapFederation federationScope index)
  index
  (StableConfederalDataHom
    (EmbeddedAtlasMap source)
    (EmbeddedAtlasFederation federationScope index))

-- | Select a federation member and construct the corresponding
-- @StaConfDa@ morphism.  Search and decidability belong to the target-specific
-- decision procedure; this constructor handles the generic categorical part.
specificationOperator
  :: TotalAtlasMap source
  -> AtlasMapFederation federationScope index
  -> index
  -> (forall target.
       AtlasWitness target
       -> Maybe (IdentityPaginationTransversal source target))
  -> Maybe (Specification federationScope index source)
specificationOperator source target targetIndex buildTransversal =
  withAtlasConfederationComponent targetComponent $ \targetWitness -> do
    identityTransversal <- buildTransversal targetWitness
    let componentArrow =
          atlasConfederationComponentHom
            sourceWitness
            targetWitness
            (identityPaginationUnderlying identityTransversal)
        selectedArrow =
          atlasConfederationHom
            sourceConfederation
            targetConfederation
            (const targetIndex)
            (const componentArrow)
        morphism =
          stableConfederalDataHom
            (embedAtlasMap sourceMap)
            (embedAtlasFederation targetFederation)
            (embeddedAtlasFederationValue
              . composeAtlasConfederationHoms selectedArrow)
            (\_ _ -> ())
    pure (Specification source target targetIndex morphism)
  where
    sourceMap = totalAtlasMapUnderlying source
    sourceWitness = atlasMapAtlas sourceMap
    targetFederation = atlasMapFederationAtlasFederation target
    targetConfederation =
      atlasFederationConfederation targetFederation
    targetComponent =
      atlasConfederationComponent targetConfederation targetIndex
    sourceConfederation =
      case sourceWitness of
        AtlasWitness sourceAtlas -> singletonAtlasConfederation sourceAtlas

specificationSource
  :: Specification federationScope index source
  -> TotalAtlasMap source
specificationSource (Specification source _ _ _) = source

specificationTarget
  :: Specification federationScope index source
  -> AtlasMapFederation federationScope index
specificationTarget (Specification _ target _ _) = target

specificationTargetIndex
  :: Specification federationScope index source
  -> index
specificationTargetIndex (Specification _ _ targetIndex _) = targetIndex

specificationMorphism
  :: Specification federationScope index source
  -> StableConfederalDataHom
       (EmbeddedAtlasMap source)
       (EmbeddedAtlasFederation federationScope index)
specificationMorphism (Specification _ _ _ morphism) = morphism
