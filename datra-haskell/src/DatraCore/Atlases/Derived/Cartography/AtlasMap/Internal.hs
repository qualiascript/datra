{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden implementation of Atlas maps, their full subcategory, and the
-- canonical inclusion into the category of atlases.
module AtlasMap.Internal
  ( AtlasMap
  , atlasMap
  , atlasMapAtlas
  , withAtlasMapExtent
  , atlasMapCoversDatum
  , AtlasMapHom
  , atlasMapHom
  , identityAtlasMapHom
  , composeAtlasMapHoms
  , materializeAtlasMapHom
  , atlasMapHomPagination
  , mapAtlasMapHomElement
  , mapAtlasMapHomArrow
  , mapAtlasMapHomData
  , AtlasMapInclusionFunctor
  , atlasMapInclusionFunctor
  , atlasMapInclusionObject
  , atlasMapInclusionHom
  ) where

import Atlas
  ( Atlas
  , AtlasHom
  , AtlasMorphism
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectAtlasScope
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasDataAt
  , atlasHomPagination
  , atlasOriginCell
  , atlasWitness
  , composeAtlasHoms
  , identityAtlasHom
  , mapAtlasHomArrow
  , mapAtlasHomData
  , mapAtlasHomElement
  , mapAtlasData
  , materializeAtlasHom
  )
import AtlasCoveredPageElement.Internal
  ( AtlasCoveredPageElement (..)
  , AtlasCoverageWitness
  , coverageNormalize
  , coverageWitnessCovers
  )
import Control.Category (Category (..))
import DomanialInsertion (applyInsertion)
import Dominion (Dominion)
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  , pageElementArrow
  , withPageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | An object of the category of Atlas maps. It is an Atlas together with the
-- extra object restriction from Lean's @IsAtlasMap@: every datum in its extent
-- is covered by a datum in a final region.
--
-- The origin cell is stored existentially with the coverage function. This
-- keeps the dependent @cellData extentObject@ type aligned with that exact
-- cell while leaving the Atlas's ordinary type-level object name unchanged.
type role AtlasMap nominal
data AtlasMap atlasObject where
  AtlasMap
    :: Atlas atlasScope scope cellData origin final
    -> PageElement scope extentObject
    -> (cellData extentObject
        -> AtlasCoverageWitness
             (AtlasObject atlasScope scope cellData))
    -> AtlasMap (AtlasObject atlasScope scope cellData)

-- | Restrict an Atlas to an Atlas map by supplying coverage for every datum
-- in its extent. The callback is invoked only at the Atlas's canonical origin
-- cell; its rank-2 type preserves the origin cell's dependent identity.
{-@
atlasMap
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> coversExtent:(forall extentObject.
       extent:PageElement scope extentObject
       -> datum:cellData extentObject
       -> { witness:AtlasCoverageWitness
              (AtlasObject atlasScope scope cellData) |
            coverageWitnessCovers
              valueAtlas
              (coverageNormalize valueAtlas extent)
              datum
              witness })
  -> AtlasMap (AtlasObject atlasScope scope cellData)
@-}
atlasMap
  :: Atlas atlasScope scope cellData origin final
  -> (forall extentObject.
       PageElement scope extentObject
       -> cellData extentObject
       -> AtlasCoverageWitness
            (AtlasObject atlasScope scope cellData))
  -> AtlasMap (AtlasObject atlasScope scope cellData)
atlasMap valueAtlas coversExtent =
  withPageElement (atlasOriginCell valueAtlas) $ \extent ->
    AtlasMap valueAtlas extent (coversExtent extent)

-- | Forget the Atlas-map object restriction. This is the object action of
-- the canonical inclusion functor.
atlasMapAtlas :: AtlasMap atlasObject -> AtlasWitness atlasObject
atlasMapAtlas (AtlasMap valueAtlas _ _) = atlasWitness valueAtlas

-- | Consume the extent of an Atlas map. Besides the dependent dominion, the
-- callback receives the total operation witnessing that each of its data is
-- covered by a final region.
withAtlasMapExtent
  :: AtlasMap atlasObject
  -> (forall extentObject.
       PageElement
         (AtlasObjectPaginationScope atlasObject)
         extentObject
       -> Dominion (AtlasObjectCellData atlasObject extentObject)
       -> (AtlasObjectCellData atlasObject extentObject
           -> AtlasCoveredPageElement atlasObject)
       -> result)
  -> result
withAtlasMapExtent
  (AtlasMap valueAtlas extent coversExtent)
  useExtent =
    useExtent
      extent
      (atlasDataAt valueAtlas extent)
      (\datum -> AtlasCoveredPageElement extent datum (coversExtent datum))

-- | Extend the defining extent-coverage witness to any Atlas cell. The datum
-- is first transported to the origin, exactly as in Lean's
-- @atlasMap_all_covered@ proof.
atlasMapCoversDatum
  :: AtlasMap atlasObject
  -> PageElement
       (AtlasObjectPaginationScope atlasObject)
       object
  -> AtlasObjectCellData atlasObject object
  -> AtlasCoverageWitness atlasObject
atlasMapCoversDatum
  (AtlasMap valueAtlas extent coversExtent)
  occurrence
  datum =
    coversExtent
      (applyInsertion
        (mapAtlasData valueAtlas (pageElementArrow occurrence extent))
        datum)

-- | A morphism in the full subcategory of Atlas maps. There are no extra
-- arrow restrictions: between two Atlas-map objects the hom-set is exactly
-- the corresponding 'AtlasHom' hom-set.
type role AtlasMapHom nominal nominal
newtype AtlasMapHom source target = AtlasMapHom
  { getAtlasMapHom :: AtlasHom source target
  }

-- | Regard an Atlas morphism between Atlas-map objects as a morphism in the
-- full subcategory.
atlasMapHom :: AtlasHom source target -> AtlasMapHom source target
atlasMapHom = AtlasMapHom

-- | Identity in the category of Atlas maps.
identityAtlasMapHom :: AtlasMapHom object object
identityAtlasMapHom = AtlasMapHom identityAtlasHom

-- | Compose Atlas-map morphisms in categorical order.
composeAtlasMapHoms
  :: AtlasMapHom middle target
  -> AtlasMapHom source middle
  -> AtlasMapHom source target
composeAtlasMapHoms (AtlasMapHom second) (AtlasMapHom first) =
  AtlasMapHom (composeAtlasHoms second first)

instance Category AtlasMapHom where
  id = identityAtlasMapHom
  (.) = composeAtlasMapHoms

-- | Interpret a symbolic Atlas-map arrow using its restricted source object.
materializeAtlasMapHom
  :: AtlasMap source
  -> AtlasMapHom source target
  -> AtlasMorphism
       (AtlasObjectAtlasScope source)
       (AtlasObjectAtlasScope target)
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
materializeAtlasMapHom sourceMap (AtlasMapHom hom) =
  materializeAtlasHom (atlasMapAtlas sourceMap) hom

-- | Recover the included pagination morphism.
atlasMapHomPagination
  :: AtlasMap source
  -> AtlasMapHom source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasMapHomPagination sourceMap (AtlasMapHom hom) =
  atlasHomPagination (atlasMapAtlas sourceMap) hom

-- | Apply an Atlas-map arrow to a padded page element through the inclusion.
mapAtlasMapHomElement
  :: AtlasMap source
  -> AtlasMapHom source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasMapHomElement sourceMap (AtlasMapHom hom) =
  mapAtlasHomElement (atlasMapAtlas sourceMap) hom

-- | Apply an Atlas-map arrow to a page-element arrow through the inclusion.
mapAtlasMapHomArrow
  :: AtlasMap source
  -> AtlasMapHom source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasMapHomArrow sourceMap (AtlasMapHom hom) =
  mapAtlasHomArrow (atlasMapAtlas sourceMap) hom

-- | Apply an Atlas-map arrow to a cell and its dependent datum through the
-- inclusion.
mapAtlasMapHomData
  :: AtlasMap source
  -> AtlasMapHom source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasMapHomData sourceMap (AtlasMapHom hom) =
  mapAtlasHomData (atlasMapAtlas sourceMap) hom

-- | The canonical inclusion @AtlMap -> Atl@. Its two rank-polymorphic fields
-- are the object and arrow actions of the functor. Both merely forget proof
-- data, so identity and composition are preserved definitionally.
data AtlasMapInclusionFunctor = AtlasMapInclusionFunctor
  { atlasMapInclusionObject
      :: forall object. AtlasMap object -> AtlasWitness object
  , atlasMapInclusionHom
      :: forall source target.
         AtlasMapHom source target -> AtlasHom source target
  }

-- | The Atlas Map Inclusion Functor from the Lean definition.
atlasMapInclusionFunctor :: AtlasMapInclusionFunctor
atlasMapInclusionFunctor =
  AtlasMapInclusionFunctor
    { atlasMapInclusionObject = atlasMapAtlas
    , atlasMapInclusionHom = getAtlasMapHom
    }
