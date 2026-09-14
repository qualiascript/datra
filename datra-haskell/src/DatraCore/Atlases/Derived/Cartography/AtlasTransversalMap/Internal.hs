{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hidden implementation of the full subcategory of Atlas transversals
-- whose objects are Atlas maps.
module AtlasTransversalMap.Internal
  ( AtlasTransversalMap
  , atlasTransversalMap
  , atlasTransversalMapTransversal
  , atlasTransversalMapAtlasMapHom
  , identityAtlasTransversalMap
  , composeAtlasTransversalMaps
  , atlasTransversalMapOrderedTransposal
  , atlasTransversalMapTransposal
  , atlasTransversalMapHom
  , atlasTransversalMapPreservesCoverage
  , mapAtlasTransversalMapCoveredDatum
  , mapAtlasTransversalMapObject
  , atlasTransversalMapPreimage
  , atlasTransversalMapLeftInverse
  , atlasTransversalMapPreservesOrder
  , atlasTransversalMapPagination
  , mapAtlasTransversalMapElement
  , mapAtlasTransversalMapArrow
  , mapAtlasTransversalMapData
  , AtlasTransversalMapInclusionFunctor
  , atlasTransversalMapInclusionFunctor
  , atlasTransversalMapInclusionObject
  , atlasTransversalMapInclusionHom
  ) where

import Atlas
  ( AtlasHom
  , AtlasMorphismImage
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  )
import AtlasCovered (AtlasCoveredDatum)
import AtlasMap
  ( AtlasMap
  , AtlasMapHom
  , atlasMapAtlas
  , atlasMapHom
  )
import AtlasTransposal (AtlasTransposal, AtlasTransposalElement)
import AtlasTransversal
  ( AtlasTransversal
  , atlasTransversalHom
  , atlasTransversalLeftInverse
  , atlasTransversalOrderedTransposal
  , atlasTransversalPagination
  , atlasTransversalPreimage
  , atlasTransversalPreservesCoverage
  , atlasTransversalPreservesOrder
  , atlasTransversalTransposal
  , composeAtlasTransversals
  , identityAtlasTransversal
  , mapAtlasTransversalArrow
  , mapAtlasTransversalCoveredDatum
  , mapAtlasTransversalData
  , mapAtlasTransversalElement
  , mapAtlasTransversalObject
  )
import Control.Category (Category (..))
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | An arrow in the full subcategory of Atlas transversals whose objects are
-- Atlas maps. There is no additional arrow condition: the wrapper records
-- that the source and target are being viewed as objects of that subcategory.
type role AtlasTransversalMap nominal nominal
newtype AtlasTransversalMap source target = AtlasTransversalMap
  { getAtlasTransversalMap :: AtlasTransversal source target
  }

-- | Regard an Atlas transversal between Atlas-map objects as an arrow in the
-- full subcategory.
atlasTransversalMap
  :: AtlasTransversal source target
  -> AtlasTransversalMap source target
atlasTransversalMap = AtlasTransversalMap

-- | Forget the Atlas-map object restriction while retaining every transversal
-- arrow restriction. This is the arrow action of the canonical inclusion.
atlasTransversalMapTransversal
  :: AtlasTransversalMap source target
  -> AtlasTransversal source target
atlasTransversalMapTransversal = getAtlasTransversalMap

-- | Forget the transversal arrow restrictions while retaining the Atlas-map
-- object restriction.
atlasTransversalMapAtlasMapHom
  :: AtlasTransversalMap source target
  -> AtlasMapHom source target
atlasTransversalMapAtlasMapHom =
  atlasMapHom . atlasTransversalHom . atlasTransversalMapTransversal

-- | Identity in the category of Atlas transversal maps.
identityAtlasTransversalMap :: AtlasTransversalMap object object
identityAtlasTransversalMap =
  AtlasTransversalMap identityAtlasTransversal

-- | Compose Atlas transversal maps in categorical order.
composeAtlasTransversalMaps
  :: AtlasTransversalMap middle target
  -> AtlasTransversalMap source middle
  -> AtlasTransversalMap source target
composeAtlasTransversalMaps
  (AtlasTransversalMap second)
  (AtlasTransversalMap first) =
    AtlasTransversalMap (composeAtlasTransversals second first)

-- | Atlas transversal maps form the full subcategory from Lean's
-- @AtlTravMap@ definition.
instance Category AtlasTransversalMap where
  id = identityAtlasTransversalMap
  (.) = composeAtlasTransversalMaps

-- | Recover the inherited ordered Atlas transposal.
atlasTransversalMapOrderedTransposal
  :: AtlasTransversalMap source target
  -> OrderedAtlasTransposal source target
atlasTransversalMapOrderedTransposal =
  atlasTransversalOrderedTransposal . atlasTransversalMapTransversal

-- | Recover the inherited Atlas transposal.
atlasTransversalMapTransposal
  :: AtlasTransversalMap source target
  -> AtlasTransposal source target
atlasTransversalMapTransposal =
  atlasTransversalTransposal . atlasTransversalMapTransversal

-- | Include an Atlas transversal map all the way into the Atlas category.
atlasTransversalMapHom
  :: AtlasTransversalMap source target
  -> AtlasHom source target
atlasTransversalMapHom =
  atlasTransversalHom . atlasTransversalMapTransversal

-- | Map a covered datum using the inherited coverage-preserving action.
mapAtlasTransversalMapCoveredDatum
  :: AtlasTransversalMap source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
mapAtlasTransversalMapCoveredDatum =
  mapAtlasTransversalCoveredDatum . atlasTransversalMapTransversal

-- | The inherited covered-data preservation condition.
atlasTransversalMapPreservesCoverage
  :: AtlasTransversalMap source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
atlasTransversalMapPreservesCoverage =
  atlasTransversalPreservesCoverage . atlasTransversalMapTransversal

-- | Apply the inherited injective, order-preserving object action.
mapAtlasTransversalMapObject
  :: AtlasTransversalMap source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransversalMapObject =
  mapAtlasTransversalObject . atlasTransversalMapTransversal

-- | Try to recover an element under the inherited injective object action.
atlasTransversalMapPreimage
  :: AtlasTransversalMap source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransversalMapPreimage =
  atlasTransversalPreimage . atlasTransversalMapTransversal

-- | Invoke the inherited injectivity certificate.
atlasTransversalMapLeftInverse
  :: AtlasTransversalMap source target
  -> AtlasTransposalElement source
  -> ()
atlasTransversalMapLeftInverse =
  atlasTransversalLeftInverse . atlasTransversalMapTransversal

-- | Invoke the inherited strict-order preservation certificate.
atlasTransversalMapPreservesOrder
  :: AtlasTransversalMap source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
atlasTransversalMapPreservesOrder =
  atlasTransversalPreservesOrder . atlasTransversalMapTransversal

-- | Recover the inherited pagination morphism using the source Atlas map.
atlasTransversalMapPagination
  :: AtlasMap source
  -> AtlasTransversalMap source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasTransversalMapPagination sourceMap transversalMap =
  atlasTransversalPagination
    (atlasMapAtlas sourceMap)
    (atlasTransversalMapTransversal transversalMap)

-- | Apply an Atlas transversal map to a padded page element.
mapAtlasTransversalMapElement
  :: AtlasMap source
  -> AtlasTransversalMap source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasTransversalMapElement sourceMap transversalMap =
  mapAtlasTransversalElement
    (atlasMapAtlas sourceMap)
    (atlasTransversalMapTransversal transversalMap)

-- | Apply an Atlas transversal map to a page-element arrow.
mapAtlasTransversalMapArrow
  :: AtlasMap source
  -> AtlasTransversalMap source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasTransversalMapArrow sourceMap transversalMap =
  mapAtlasTransversalArrow
    (atlasMapAtlas sourceMap)
    (atlasTransversalMapTransversal transversalMap)

-- | Apply an Atlas transversal map to a cell and its dependent datum.
mapAtlasTransversalMapData
  :: AtlasMap source
  -> AtlasTransversalMap source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasTransversalMapData sourceMap transversalMap =
  mapAtlasTransversalData
    (atlasMapAtlas sourceMap)
    (atlasTransversalMapTransversal transversalMap)

-- | The canonical inclusion @AtlTravMap -> AtlTrav@. Its object action
-- forgets the Atlas-map proof, and its arrow action unwraps the full
-- subcategory arrow. Identity and composition are therefore preserved
-- definitionally.
data AtlasTransversalMapInclusionFunctor =
  AtlasTransversalMapInclusionFunctor
    { atlasTransversalMapInclusionObject
        :: forall object. AtlasMap object -> AtlasWitness object
    , atlasTransversalMapInclusionHom
        :: forall source target.
           AtlasTransversalMap source target
           -> AtlasTransversal source target
    }

-- | The Atlas Transversal Map Inclusion Functor from the Lean definition.
atlasTransversalMapInclusionFunctor
  :: AtlasTransversalMapInclusionFunctor
atlasTransversalMapInclusionFunctor =
  AtlasTransversalMapInclusionFunctor
    { atlasTransversalMapInclusionObject = atlasMapAtlas
    , atlasTransversalMapInclusionHom = atlasTransversalMapTransversal
    }
