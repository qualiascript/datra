{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of order-preserving Atlas transposals.
module OrderedAtlasTransposal.Internal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  , orderedAtlasTransposalTransposal
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalPreservesOrder
  , orderedAtlasTransposalOwnedOrder
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
import AtlasTransposal.Element (TransposalElementData)
import AtlasTransposal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElementLT
  , atlasTransposalHom
  , atlasTransposalSourceValid
  , atlasTransposalPathValid, atlasTransposalPathSource
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasTransposalCompositionOwners, atlasTransposalOwnersAssociativity
  , atlasTransposalOwnedPath, atlasTransposalElementValid
  , identityAtlasTransposalRetains, composeAtlasTransposalsRetains
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
import Data.Type.Equality ((:~:) (Refl))
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
{-@ data OrderedAtlasTransposal source target where
      PrimitiveOrderedAtlasTransposal :: forall source target.
        OrderedTransposalAction source target -> OrderedAtlasTransposal source target
      IdentityOrderedAtlasTransposal :: forall source target.
        OrderedIdentityEquality source target
        -> action:{OrderedTransposalAction source target |
             atlasTransposalSourceOwner (storedOrderedTransposal action) == Nothing
             && atlasTransposalTargetOwner (storedOrderedTransposal action) == Nothing
             && TransposalCompatible (storedOrderedTransposal action)}
        -> OrderedAtlasTransposal source target
      CompositeOrderedAtlasTransposal :: forall source target middle.
        OrderedAtlasTransposal middle target -> OrderedAtlasTransposal source middle
        -> OrderedAtlasTransposal source target @-}
data OrderedAtlasTransposal source target where
  PrimitiveOrderedAtlasTransposal
    :: OrderedTransposalAction source target
    -> OrderedAtlasTransposal source target
  IdentityOrderedAtlasTransposal
    :: OrderedIdentityEquality source target
    -> OrderedTransposalAction source target
    -> OrderedAtlasTransposal source target
  CompositeOrderedAtlasTransposal
    :: OrderedAtlasTransposal middle target
    -> OrderedAtlasTransposal source middle
    -> OrderedAtlasTransposal source target

-- | Preserve the type equality for identity simplification without casting
-- the raw carriers when the order certificate is eliminated.
type role OrderedIdentityEquality nominal nominal
data OrderedIdentityEquality source target = OrderedIdentityEquality (source :~: target)

-- | Retain the primitive's checked law when hiding it in the syntax tree.
type role OrderedTransposalAction nominal nominal
{-@ data OrderedTransposalAction source target = OrderedTransposalAction
      { storedOrderedTransposal :: AtlasTransposal source target
      , storedOrderProof :: left:AtlasTransposalElement source -> right:AtlasTransposalElement source
          -> {orderedSourceValid storedOrderedTransposal left && orderedSourceValid storedOrderedTransposal right
               && orderedElementLT left right
               => orderedElementLT (orderedMapObject storedOrderedTransposal left) (orderedMapObject storedOrderedTransposal right)}
      } @-}
data OrderedTransposalAction source target = OrderedTransposalAction
  { storedOrderedTransposal :: AtlasTransposal source target
  , storedOrderProof :: AtlasTransposalElement source -> AtlasTransposalElement source -> ()
  }

{-@ reflect orderedElementLT @-}
orderedElementLT
  :: TransposalElementData a s d
  -> TransposalElementData a s d
  -> Bool
orderedElementLT = atlasTransposalElementLT

{-@ reflect orderedSourceValid @-}
orderedSourceValid :: AtlasTransposal source target
  -> AtlasTransposalElement source -> Bool
orderedSourceValid transposal element = atlasTransposalSourceValid transposal element

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
  -> (left:{AtlasTransposalElement source | orderedSourceValid transposal left}
       -> right:{AtlasTransposalElement source |
            orderedSourceValid transposal right && orderedElementLT left right}
       -> { proof:() |
            orderedElementLT
              (orderedMapObject transposal left)
              (orderedMapObject transposal right) })
  -> {result:OrderedAtlasTransposal source target | orderedAtlasTransposalTransposal result == transposal}
@-}
-- ALIGN: ATLAS-ORDERED-INTERPRETATION.
orderedAtlasTransposal
  :: AtlasTransposal source target
  -> (AtlasTransposalElement source
      -> AtlasTransposalElement source
      -> ())
  -> OrderedAtlasTransposal source target
orderedAtlasTransposal transposal preservesOrder =
  PrimitiveOrderedAtlasTransposal (OrderedTransposalAction transposal checkedPreservesOrder)
  where
    checkedPreservesOrder left right
      | orderedSourceValid transposal left
          && orderedSourceValid transposal right
          && orderedElementLT left right = preservesOrder left right
      | otherwise = ()

-- | Forget only the ordering restriction, retaining the injectivity evidence.
-- ALIGN: ATLAS-ORDERED-NATIVE-PROJECTION.
{-@ reflect orderedAtlasTransposalTransposal @-}
orderedAtlasTransposalTransposal
  :: OrderedAtlasTransposal source target
  -> AtlasTransposal source target
orderedAtlasTransposalTransposal
  (PrimitiveOrderedAtlasTransposal action) = storedOrderedTransposal action
orderedAtlasTransposalTransposal (IdentityOrderedAtlasTransposal _ action) =
  storedOrderedTransposal action
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
-- ALIGN: ATLAS-ORDERED-PRESERVATION.
-- ALIGN: ATLAS-ORDERED-PATH-PRESERVATION.
{-@ orderedAtlasTransposalPreservesOrder :: ordered:OrderedAtlasTransposal source target
      -> left:AtlasTransposalElement source -> right:AtlasTransposalElement source
      -> {atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) left
           && atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) right && orderedElementLT left right
           => orderedElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}

orderedAtlasTransposalPreservesOrder
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
orderedAtlasTransposalPreservesOrder (PrimitiveOrderedAtlasTransposal action) left right =
  orderedActionPreservesOrder action left right
orderedAtlasTransposalPreservesOrder (IdentityOrderedAtlasTransposal _ action) left right =
  orderedActionPreservesOrder action left right
orderedAtlasTransposalPreservesOrder
  (CompositeOrderedAtlasTransposal second first)
  left
  right =
    composeAtlasTransposalsRetains (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal first)
      left (mapOrderedAtlasTransposalObject second (mapOrderedAtlasTransposalObject first left)) `seq`
    composeAtlasTransposalsRetains (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal first)
      right (mapOrderedAtlasTransposalObject second (mapOrderedAtlasTransposalObject first right)) `seq`
    orderedAtlasTransposalPreservesOrder first left right `seq`
      orderedAtlasTransposalPreservesOrder
        second
        (mapOrderedAtlasTransposalObject first left)
        (mapOrderedAtlasTransposalObject first right)

{-@ orderedActionPreservesOrder :: action:OrderedTransposalAction source target
      -> left:AtlasTransposalElement source -> right:AtlasTransposalElement source
      -> {atlasTransposalPathValid (storedOrderedTransposal action) left
           && atlasTransposalPathValid (storedOrderedTransposal action) right && orderedElementLT left right
           => orderedElementLT (orderedMapObject (storedOrderedTransposal action) left)
                (orderedMapObject (storedOrderedTransposal action) right)} @-}
orderedActionPreservesOrder :: OrderedTransposalAction source target
  -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
orderedActionPreservesOrder action left right =
  atlasTransposalPathSource (storedOrderedTransposal action) left `seq`
  atlasTransposalPathSource (storedOrderedTransposal action) right `seq` storedOrderProof action left right

-- | Owner evidence discharges every intermediate domain in the order proof.
-- ALIGN: ATLAS-ORDERED-OWNED-PRESERVATION.
{-@ orderedAtlasTransposalOwnedOrder :: witness:AtlasWitness source
      -> ordered:{OrderedAtlasTransposal source target | TransposalOwnedBy witness (orderedAtlasTransposalTransposal ordered)}
      -> left:{AtlasTransposalElement source | atlasTransposalElementValid witness left}
      -> right:{AtlasTransposalElement source | atlasTransposalElementValid witness right && orderedElementLT left right}
      -> {orderedElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}
orderedAtlasTransposalOwnedOrder :: AtlasWitness source -> OrderedAtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
orderedAtlasTransposalOwnedOrder witness ordered left right =
  atlasTransposalOwnedPath witness (orderedAtlasTransposalTransposal ordered) left `seq`
  atlasTransposalOwnedPath witness (orderedAtlasTransposalTransposal ordered) right `seq`
    orderedAtlasTransposalPreservesOrder ordered left right

-- | The identity transposal preserves strict order unchanged.
-- ALIGN: ATLAS-ORDERED-IDENTITY.
{-@ identityOrderedAtlasTransposal :: {result:OrderedAtlasTransposal object object |
      orderedAtlasTransposalTransposal result == identityAtlasTransposal} @-}
identityOrderedAtlasTransposal
  :: OrderedAtlasTransposal object object
identityOrderedAtlasTransposal = identityOrderedFrom identityAtlasTransposal

{-@ identityOrderedFrom :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> {result:OrderedAtlasTransposal object object | orderedAtlasTransposalTransposal result == identity} @-}
identityOrderedFrom :: AtlasTransposal object object -> OrderedAtlasTransposal object object
identityOrderedFrom identity = IdentityOrderedAtlasTransposal (OrderedIdentityEquality Refl)
  (OrderedTransposalAction identity (identityOrderProof identity))

{-@ identityOrderProof :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> left:AtlasTransposalElement object -> right:AtlasTransposalElement object
      -> {orderedElementLT left right => orderedElementLT (orderedMapObject identity left) (orderedMapObject identity right)} @-}
identityOrderProof :: AtlasTransposal object object -> AtlasTransposalElement object -> AtlasTransposalElement object -> ()
identityOrderProof identity left right =
  identityAtlasTransposalRetains identity left `seq` identityAtlasTransposalRetains identity right

-- | Compose ordered transposals in categorical order.
-- ALIGN: ATLAS-ORDERED-COMPOSITION.
-- ALIGN: ATLAS-ORDERED-NORMALIZED-OWNERS.
{-@ composeOrderedAtlasTransposals :: second:OrderedAtlasTransposal middle target
      -> first:OrderedAtlasTransposal source middle
      -> {result:OrderedAtlasTransposal source target |
           atlasTransposalSourceOwner (orderedAtlasTransposalTransposal result)
             == atlasTransposalSourceOwner (composeAtlasTransposals (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal first))
           && atlasTransposalTargetOwner (orderedAtlasTransposalTransposal result)
             == atlasTransposalTargetOwner (composeAtlasTransposals (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal first))
           && (TransposalCompatible (orderedAtlasTransposalTransposal result)
             <=> TransposalCompatible (composeAtlasTransposals (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal first)))} @-}
composeOrderedAtlasTransposals
  :: OrderedAtlasTransposal middle target
  -> OrderedAtlasTransposal source middle
  -> OrderedAtlasTransposal source target
composeOrderedAtlasTransposals second first =
  atlasTransposalCompositionOwners (orderedAtlasTransposalTransposal second)
    (orderedAtlasTransposalTransposal first) `seq`
  case (second, first) of
    (IdentityOrderedAtlasTransposal (OrderedIdentityEquality Refl) _, _) -> first
    (_, IdentityOrderedAtlasTransposal (OrderedIdentityEquality Refl) _) -> second
    (_, CompositeOrderedAtlasTransposal middle initial) ->
      atlasTransposalOwnersAssociativity (orderedAtlasTransposalTransposal second)
        (orderedAtlasTransposalTransposal middle) (orderedAtlasTransposalTransposal initial) `seq`
      let reduced = composeOrderedAtlasTransposals second middle
      in atlasTransposalCompositionOwners
           (composeAtlasTransposals (orderedAtlasTransposalTransposal second) (orderedAtlasTransposalTransposal middle))
           (orderedAtlasTransposalTransposal initial) `seq`
         atlasTransposalCompositionOwners (orderedAtlasTransposalTransposal reduced)
           (orderedAtlasTransposalTransposal initial) `seq`
         CompositeOrderedAtlasTransposal reduced initial
    _ -> CompositeOrderedAtlasTransposal second first

-- | Ordered Atlas transposals form the next wide subcategory in the
-- restriction chain.
instance Category OrderedAtlasTransposal where
  id = identityOrderedAtlasTransposal
  (.) = composeOrderedAtlasTransposals

-- | Apply the order-preserving injective object map.
{-@ reflect mapOrderedAtlasTransposalObject @-}
mapOrderedAtlasTransposalObject
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapOrderedAtlasTransposalObject ordered source =
  orderedMapObject (orderedAtlasTransposalTransposal ordered) source

-- | Try to recover an element under the underlying injective object map.
{-@ reflect orderedAtlasTransposalPreimage @-}
orderedAtlasTransposalPreimage
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
orderedAtlasTransposalPreimage ordered target =
  atlasTransposalPreimage (orderedAtlasTransposalTransposal ordered) target

-- | Invoke the inherited left-inverse certificate.
{-@ orderedAtlasTransposalLeftInverse :: ordered:OrderedAtlasTransposal source target
      -> source:AtlasTransposalElement source
      -> {atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) source
           => orderedAtlasTransposalPreimage ordered (mapOrderedAtlasTransposalObject ordered source) == Just source} @-}
orderedAtlasTransposalLeftInverse
  :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source
  -> ()
orderedAtlasTransposalLeftInverse ordered source =
  atlasTransposalLeftInverse (orderedAtlasTransposalTransposal ordered) source

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
