{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  , atlasMapAcceptsDatum
  , atlasMapCellValid
  , atlasMapWitnessCovers
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
  , atlasAcceptsDatum
  , atlasPageElements
  , atlasHomPagination
  , atlasWitness
  , composeAtlasHoms
  , identityAtlasHom
  , mapAtlasHomArrow
  , mapAtlasHomData
  , mapAtlasHomElement
  , mapAtlasData
  , materializeAtlasHom
  )
import AtlasCoveredPageElement
  ( CoverageWitness
  , AtlasCoveredPageElement
  , atlasCoveredByWitness
  , coverageWitnessCovers
  , coverageWitnessAlongArrow
  )
import AtlasExtent (cellTraceValid, cellTraceHasOrigin)
import PageElements.Structure (SomePageElement (..))
import Control.Category (Category (..))
import DomanialInsertion (applyInsertion)
import Dominion (Dominion)
import PageElements
  ( PageElement
  , PageElementArrow
  , originPageElement
  , pageElementArrow
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
  AtlasMap :: AtlasMapData a s d o f extent -> AtlasMap (AtlasObject a s d)

-- | Store the origin, its owning trace, and the coverage law together.
type role AtlasMapData nominal nominal nominal nominal nominal nominal
{-@ data AtlasMapData a s d o f extent = AtlasMapData
      { mapOwner :: Atlas a s d o f
      , mapExtent :: {source:PageElement s extent | cellTraceValid mapOwner source
           && SomePageElement source == originPageElement (atlasPageElements mapOwner)}
      , mapExtentCoverage :: datum:{d extent | atlasAcceptsDatum mapOwner mapExtent datum}
          -> {witness:CoverageWitness a s d |
               coverageWitnessCovers mapOwner mapExtent datum witness}
      } @-}
data AtlasMapData a s d o f extent = AtlasMapData
  { mapOwner :: Atlas a s d o f
  , mapExtent :: PageElement s extent
  , mapExtentCoverage :: d extent -> CoverageWitness a s d
  }

{-@ reflect atlasMapCellValid @-}
atlasMapCellValid
  :: forall a s d cell. AtlasMap (AtlasObject a s d) -> PageElement s cell -> Bool
atlasMapCellValid (AtlasMap (value :: AtlasMapData a s d o f extent)) source =
  cellTraceValid (mapOwner value) source

{-@ reflect atlasMapAcceptsDatum @-}
atlasMapAcceptsDatum
  :: forall a s d cell. AtlasMap (AtlasObject a s d) -> PageElement s cell -> d cell -> Bool
atlasMapAcceptsDatum (AtlasMap (value :: AtlasMapData a s d o f extent)) source datum =
  atlasAcceptsDatum (mapOwner value) source datum

{-@ reflect atlasMapWitnessCovers @-}
atlasMapWitnessCovers
  :: forall a s d cell. AtlasMap (AtlasObject a s d) -> PageElement s cell -> d cell
  -> CoverageWitness a s d -> Bool
atlasMapWitnessCovers (AtlasMap (value :: AtlasMapData a s d o f extent)) source datum witness =
  coverageWitnessCovers (mapOwner value) source datum witness

-- | Restrict an Atlas to an Atlas map by supplying coverage for every datum
-- in its extent. The callback is invoked only at the Atlas's canonical origin
-- cell; its rank-2 type preserves the origin cell's dependent identity.
{-@
atlasMap
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> coversExtent:(forall extentObject.
       extent:{PageElement scope extentObject | cellTraceValid valueAtlas extent
            && SomePageElement extent == originPageElement (atlasPageElements valueAtlas)}
       -> datum:{cellData extentObject | atlasAcceptsDatum valueAtlas extent datum}
       -> { witness:CoverageWitness atlasScope scope cellData |
            coverageWitnessCovers
              valueAtlas
              extent
              datum
              witness })
  -> AtlasMap (AtlasObject atlasScope scope cellData)
@-}
-- ALIGN: ATLAS-MAP-OBJECT-INTERPRETATION.
atlasMap
  :: Atlas atlasScope scope cellData origin final
  -> (forall extentObject.
       PageElement scope extentObject
       -> cellData extentObject
       -> CoverageWitness atlasScope scope cellData)
  -> AtlasMap (AtlasObject atlasScope scope cellData)
atlasMap valueAtlas coversExtent =
  case originPageElement (atlasPageElements valueAtlas) of
    SomePageElement extent -> AtlasMap (AtlasMapData valueAtlas extent (coversExtent extent))

-- | Forget the Atlas-map object restriction. This is the object action of
-- the canonical inclusion functor.
atlasMapAtlas :: AtlasMap atlasObject -> AtlasWitness atlasObject
atlasMapAtlas (AtlasMap value) = atlasWitness (mapOwner value)

-- | Consume the extent together with its owning Atlas and dependent dominion.
-- The callback receives coverage for each datum accepted by that exact owner
-- and origin cell.
{-@ withAtlasMapExtent :: value:AtlasMap (AtlasObject a s d)
      -> (forall o f extent.
           owner:Atlas a s d o f
           -> source:{PageElement s extent | cellTraceValid owner source
                && SomePageElement source == originPageElement (atlasPageElements owner)}
           -> Dominion ({datum:d extent | atlasAcceptsDatum owner source datum})
           -> ({datum:d extent | atlasAcceptsDatum owner source datum}
                 -> AtlasCoveredPageElement (AtlasObject a s d))
           -> result)
      -> result @-}
withAtlasMapExtent
  :: forall a s d result. AtlasMap (AtlasObject a s d)
  -> (forall o f extent.
       Atlas a s d o f
       -> PageElement s extent
       -> Dominion (d extent)
       -> (d extent -> AtlasCoveredPageElement (AtlasObject a s d))
       -> result)
  -> result
withAtlasMapExtent (AtlasMap (value :: AtlasMapData a s d o f extent)) useExtent =
  useExtent (mapOwner value) (mapExtent value)
    (atlasDataAt (mapOwner value) (mapExtent value))
    (mapExtentCovered value)

{-@ mapExtentCovered :: value:AtlasMapData a s d o f extent
      -> datum:{d extent | atlasAcceptsDatum (mapOwner value) (mapExtent value) datum}
      -> AtlasCoveredPageElement (AtlasObject a s d) @-}
mapExtentCovered
  :: AtlasMapData a s d o f extent -> d extent -> AtlasCoveredPageElement (AtlasObject a s d)
mapExtentCovered value datum =
  atlasCoveredByWitness (mapOwner value) (mapExtent value) datum (mapExtentCoverage value datum)

-- | Extend the defining extent-coverage witness to any Atlas cell. The datum
-- is first transported to the origin, exactly as in Lean's
-- @atlasMap_all_covered@ proof.
-- ALIGN: ATLAS-MAP-COVERAGE.
{-@ atlasMapCoversDatum :: value:AtlasMap (AtlasObject a s d)
      -> source:{PageElement s cell | atlasMapCellValid value source}
      -> datum:{d cell | atlasMapAcceptsDatum value source datum}
      -> {witness:CoverageWitness a s d |
           atlasMapWitnessCovers value source datum witness} @-}
atlasMapCoversDatum
  :: forall a s d object. AtlasMap (AtlasObject a s d)
  -> PageElement s object
  -> d object
  -> CoverageWitness a s d
atlasMapCoversDatum (AtlasMap (value :: AtlasMapData a s d o f extent)) occurrence datum =
  mapCoveredDatum value occurrence datum

{-@ mapCoveredDatum :: value:AtlasMapData a s d o f extent
      -> source:{PageElement s cell | cellTraceValid (mapOwner value) source}
      -> datum:{d cell | atlasAcceptsDatum (mapOwner value) source datum}
      -> {witness:CoverageWitness a s d |
           coverageWitnessCovers (mapOwner value) source datum witness} @-}
mapCoveredDatum
  :: AtlasMapData a s d o f extent
  -> PageElement s cell
  -> d cell
  -> CoverageWitness a s d
mapCoveredDatum value occurrence datum =
  cellTraceHasOrigin (mapOwner value) occurrence `seq`
    let arrow = pageElementArrow occurrence (mapExtent value)
        witness = mapExtentCoverage value
          (applyInsertion (mapAtlasData (mapOwner value) arrow) datum)
    in coverageWitnessAlongArrow (mapOwner value) arrow datum witness `seq` witness

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
-- ALIGN: ATLAS-MAP-HOM-IDENTITY.
identityAtlasMapHom :: AtlasMapHom object object
identityAtlasMapHom = AtlasMapHom identityAtlasHom

-- | Compose Atlas-map morphisms in categorical order.
-- ALIGN: ATLAS-MAP-HOM-COMPOSITION.
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
-- ALIGN: ATLAS-MAP-HOM-DATA.
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
-- ALIGN: ATLAS-MAP-INCLUSION.
atlasMapInclusionFunctor :: AtlasMapInclusionFunctor
atlasMapInclusionFunctor =
  AtlasMapInclusionFunctor
    { atlasMapInclusionObject = atlasMapAtlas
    , atlasMapInclusionHom = getAtlasMapHom
    }
