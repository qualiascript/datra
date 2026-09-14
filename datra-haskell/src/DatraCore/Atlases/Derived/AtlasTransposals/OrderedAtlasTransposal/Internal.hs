{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Hidden implementation of order-preserving Atlas transposals.
module OrderedAtlasTransposal.Internal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  , orderedAtlasTransposalTransposal
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalPreservesOrder
  , identityOrderedAtlasTransposal
  , composeOrderedAtlasTransposals
  , mapOrderedAtlasTransposalObject
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , mapOrderedAtlasTransposalElement
  , mapOrderedAtlasTransposalArrow
  , mapOrderedAtlasTransposalData
  ) where

import Atlas
  ( AtlasHom
  , AtlasMorphismImage
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  )
import AtlasTransposal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElementLT
  , atlasTransposalHom
  , atlasTransposalLeftInverse
  , atlasTransposalPagination
  , atlasTransposalPreimage
  , composeAtlasTransposals
  , identityAtlasTransposal
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  , mapAtlasTransposalElement
  , mapAtlasTransposalObject
  )
import Control.Category (Category (..))
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | An Atlas transposal together with preservation of Lean's strict
-- @elementLT@ relation. Primitive restrictions retain their supplied proof;
-- identity and composition are syntax constructors whose proofs are derived.
type role OrderedAtlasTransposal nominal nominal
data OrderedAtlasTransposal source target where
  PrimitiveOrderedAtlasTransposal
    :: AtlasTransposal source target
    -> (AtlasTransposalElement source
        -> AtlasTransposalElement source
        -> ())
    -> OrderedAtlasTransposal source target
  IdentityOrderedAtlasTransposal
    :: OrderedAtlasTransposal object object
  CompositeOrderedAtlasTransposal
    :: OrderedAtlasTransposal middle target
    -> OrderedAtlasTransposal source middle
    -> OrderedAtlasTransposal source target

{-@ reflect orderedElementLT @-}
orderedElementLT
  :: AtlasTransposalElement atlasObject
  -> AtlasTransposalElement atlasObject
  -> Bool
orderedElementLT = atlasTransposalElementLT

{-@ reflect orderedMapObject @-}
orderedMapObject
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
orderedMapObject = mapAtlasTransposalObject

-- | Restrict a transposal to the arrows preserving strict Atlas order.
--
-- The proof callback is required precisely when @left < right@ in the source
-- Atlas and must establish that their mapped elements retain that relation in
-- the target. No coverage condition is imposed here.
{-@
orderedAtlasTransposal
  :: transposal:AtlasTransposal source target
  -> (left:AtlasTransposalElement source
       -> right:{AtlasTransposalElement source |
            orderedElementLT left right}
       -> { proof:() |
            orderedElementLT
              (orderedMapObject transposal left)
              (orderedMapObject transposal right) })
  -> OrderedAtlasTransposal source target
@-}
orderedAtlasTransposal
  :: AtlasTransposal source target
  -> (AtlasTransposalElement source
      -> AtlasTransposalElement source
      -> ())
  -> OrderedAtlasTransposal source target
orderedAtlasTransposal transposal preservesOrder =
  PrimitiveOrderedAtlasTransposal transposal checkedPreservesOrder
  where
    checkedPreservesOrder left right
      | orderedElementLT left right = preservesOrder left right
      | otherwise = ()

-- | Forget only the ordering restriction, retaining the injectivity evidence.
orderedAtlasTransposalTransposal
  :: OrderedAtlasTransposal source target
  -> AtlasTransposal source target
orderedAtlasTransposalTransposal
  (PrimitiveOrderedAtlasTransposal transposal _) = transposal
orderedAtlasTransposalTransposal IdentityOrderedAtlasTransposal =
  identityAtlasTransposal
orderedAtlasTransposalTransposal
  (CompositeOrderedAtlasTransposal second first) =
    composeAtlasTransposals
      (orderedAtlasTransposalTransposal second)
      (orderedAtlasTransposalTransposal first)

-- | Include an ordered transposal all the way into the Atlas category.
orderedAtlasTransposalHom
  :: OrderedAtlasTransposal source target
  -> AtlasHom source target
orderedAtlasTransposalHom =
  atlasTransposalHom . orderedAtlasTransposalTransposal

-- | Invoke the primitive or derived strict-order preservation proof.
orderedAtlasTransposalPreservesOrder
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
orderedAtlasTransposalPreservesOrder
  (PrimitiveOrderedAtlasTransposal _ preservesOrder)
  left
  right = preservesOrder left right
orderedAtlasTransposalPreservesOrder IdentityOrderedAtlasTransposal _ _ = ()
orderedAtlasTransposalPreservesOrder
  (CompositeOrderedAtlasTransposal second first)
  left
  right =
    orderedAtlasTransposalPreservesOrder first left right `seq`
      orderedAtlasTransposalPreservesOrder
        second
        (mapOrderedAtlasTransposalObject first left)
        (mapOrderedAtlasTransposalObject first right)

-- | The identity transposal preserves strict order unchanged.
identityOrderedAtlasTransposal
  :: OrderedAtlasTransposal object object
identityOrderedAtlasTransposal = IdentityOrderedAtlasTransposal

-- | Compose ordered transposals in categorical order.
composeOrderedAtlasTransposals
  :: OrderedAtlasTransposal middle target
  -> OrderedAtlasTransposal source middle
  -> OrderedAtlasTransposal source target
composeOrderedAtlasTransposals IdentityOrderedAtlasTransposal first = first
composeOrderedAtlasTransposals second IdentityOrderedAtlasTransposal = second
composeOrderedAtlasTransposals
  second
  (CompositeOrderedAtlasTransposal middle first) =
    CompositeOrderedAtlasTransposal
      (composeOrderedAtlasTransposals second middle)
      first
composeOrderedAtlasTransposals second first =
  CompositeOrderedAtlasTransposal second first

-- | Ordered Atlas transposals form the next wide subcategory in the
-- restriction chain.
instance Category OrderedAtlasTransposal where
  id = identityOrderedAtlasTransposal
  (.) = composeOrderedAtlasTransposals

-- | Apply the order-preserving injective object map.
mapOrderedAtlasTransposalObject
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapOrderedAtlasTransposalObject ordered =
  orderedMapObject
    (orderedAtlasTransposalTransposal ordered)

-- | Try to recover an element under the underlying injective object map.
orderedAtlasTransposalPreimage
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
orderedAtlasTransposalPreimage ordered =
  atlasTransposalPreimage
    (orderedAtlasTransposalTransposal ordered)

-- | Invoke the inherited left-inverse certificate.
orderedAtlasTransposalLeftInverse
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> ()
orderedAtlasTransposalLeftInverse ordered =
  atlasTransposalLeftInverse
    (orderedAtlasTransposalTransposal ordered)

-- | Recover the underlying pagination morphism.
orderedAtlasTransposalPagination
  :: AtlasWitness source
  -> OrderedAtlasTransposal source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
orderedAtlasTransposalPagination sourceWitness ordered =
  atlasTransposalPagination
    sourceWitness
    (orderedAtlasTransposalTransposal ordered)

-- | Apply the included arrow to a padded page element.
mapOrderedAtlasTransposalElement
  :: AtlasWitness source
  -> OrderedAtlasTransposal source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapOrderedAtlasTransposalElement sourceWitness ordered =
  mapAtlasTransposalElement
    sourceWitness
    (orderedAtlasTransposalTransposal ordered)

-- | Apply the included arrow to a page-element arrow.
mapOrderedAtlasTransposalArrow
  :: AtlasWitness source
  -> OrderedAtlasTransposal source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapOrderedAtlasTransposalArrow sourceWitness ordered =
  mapAtlasTransposalArrow
    sourceWitness
    (orderedAtlasTransposalTransposal ordered)

-- | Apply the included arrow to a cell and its dependent datum.
mapOrderedAtlasTransposalData
  :: AtlasWitness source
  -> OrderedAtlasTransposal source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapOrderedAtlasTransposalData sourceWitness ordered =
  mapAtlasTransposalData
    sourceWitness
    (orderedAtlasTransposalTransposal ordered)
