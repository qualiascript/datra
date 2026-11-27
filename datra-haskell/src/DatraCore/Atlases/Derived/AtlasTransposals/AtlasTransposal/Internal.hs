{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of the category of Atlas transposals.
--
-- This is the Haskell presentation of Lean's @AtlTrap@: objects are unchanged
-- from 'Atlas', while arrows are restricted by an executable left inverse for
-- their action on Atlas elements.
module AtlasTransposal.Internal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElement
  , atlasTransposalElementValid
  , withAtlasTransposalElement
  , atlasTransposalElementLT
  , atlasTransposal
  , atlasTransposalHom
  , atlasTransposalSourceValid
  , atlasTransposalPathValid
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasHomSourceOwner, atlasHomTargetOwner
  , atlasHomSourceAgrees
  , atlasHomSourceValid, atlasHomTargetValid, mapAtlasHomObject
  , mapAtlasTransposalObject
  , atlasTransposalPreimage
  , atlasTransposalLeftInverse
  , identityAtlasTransposal
  , identityAtlasTransposalRetains
  , composeAtlasTransposals
  , composeAtlasTransposalsRetains
  , atlasTransposalPagination
  , mapAtlasTransposalElement
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  ) where

import Atlas
  ( AtlasHom
  , AtlasMorphismImage
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasHomPagination
  , mapAtlasHomArrow
  , mapAtlasHomData
  , mapAtlasHomElement
  )
import AtlasTransposal.Primitive.Internal (primitiveAtlasTransposal)
import AtlasTransposal.Syntax.Internal
  ( AtlasTransposal (..)
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasTransposalSourceValid, atlasTransposalPathValid
  , mapAtlasTransposalObject, atlasTransposalPreimage
  , atlasTransposalLeftInverse, identityAtlasTransposal, identityAtlasTransposalRetains
  , composeAtlasTransposals, composeAtlasTransposalsRetains )
import AtlasTransposal.Element.Internal
  (AtlasTransposalElement, TransposalElementData (..))
import AtlasTransposal.Element (transposalElementSource, transposalWitnessElementValid)
import Atlas.Witness (atlasWitnessOwner,
  atlasWitnessElementValid, normalizeAtlasWitnessElement, atlasWitnessNormalizeValid)
import AtlasTransposal.Action (transposalAction)
import AtlasTransposal.Objects
  ( transposalObjectsMap, transposalObjectsWitnessAgrees, withTransposalObjects
  , homTransposalObjects, homTransposalObjectsRetains
  , atlasHomSourceOwner, atlasHomTargetOwner, atlasHomSourceValid, atlasHomTargetValid, mapAtlasHomObject )
import Control.Category (Category (..))
import DatraOrdinal (ordinalLT)
import PageElements
  ( PageElement
  , PageElementArrow
  , pageElementPage
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import PageElements.Structure (positionAtPage, SomePageElement (..))
import Prelude hiding ((.), id)

-- | Normalize a raw occurrence against the actual witnessed Atlas. The raw
-- result is retained even when the source lies outside that owner's domain.
-- ALIGN: ATLAS-TRANSPOSE-ELEMENT-EQUIVALENCE.
-- ALIGN: ATLAS-TRANSPOSAL-WITNESSED-ELEMENT.
{-@ atlasTransposalElement :: witness:AtlasWitness atlasObject
      -> source:PageElement (AtlasObjectPaginationScope atlasObject) object
      -> {result:AtlasTransposalElement atlasObject |
           transposalElementSource result == SomePageElement (normalizeAtlasWitnessElement witness source)
           && (atlasWitnessElementValid witness source => atlasTransposalElementValid witness result)} @-}
atlasTransposalElement
  :: AtlasWitness atlasObject
  -> PageElement (AtlasObjectPaginationScope atlasObject) object
  -> AtlasTransposalElement atlasObject
atlasTransposalElement witness source =
  atlasWitnessNormalizeValid witness source `seq`
    AtlasTransposalElement (normalizeAtlasWitnessElement witness source)

{-@ reflect atlasTransposalElementValid @-}
atlasTransposalElementValid :: AtlasWitness atlasObject -> AtlasTransposalElement atlasObject -> Bool
atlasTransposalElementValid witness element = transposalWitnessElementValid witness element

-- | Eliminate the existential cell identity of an Atlas element.
withAtlasTransposalElement
  :: TransposalElementData a s d
  -> (forall object.
        PageElement s object
        -> result)
  -> result
withAtlasTransposalElement (AtlasTransposalElement element) useElement =
  useElement element

-- | The strict Atlas order on genuine elements. The elements have already
-- been normalized, so this is Lean's @elementLT@: transport both cells to
-- their common earliest page and compare their positions there.
{-@ reflect atlasTransposalElementLT @-}
-- ALIGN: ATLAS-ORDER-INTERPRETATION.
atlasTransposalElementLT
  :: TransposalElementData a s d
  -> TransposalElementData a s d
  -> Bool
atlasTransposalElementLT
    (AtlasTransposalElement left)
    (AtlasTransposalElement right) =
  let commonPage = min (pageElementPage left) (pageElementPage right)
  in case
      ( positionAtPage commonPage left
      , positionAtPage commonPage right
      ) of
        (Just leftPosition, Just rightPosition) ->
          ordinalLT leftPosition rightPosition
        _ -> False

-- | Transfer owning membership only after identifying the complete owners.
-- ALIGN: ATLAS-TRANSPOSAL-WITNESSED-SOURCE.
{-@ atlasHomSourceAgrees :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> element:AtlasTransposalElement source
      -> {atlasTransposalElementValid witness element <=> atlasHomSourceValid witness hom element} @-}
atlasHomSourceAgrees :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> ()
atlasHomSourceAgrees witness hom element =
  transposalObjectsWitnessAgrees witness (homTransposalObjects witness hom) element

-- | Restrict an Atlas arrow to a transposal.
--
-- The final argument certifies, for every accepted @sourceElement@, that
--
-- @
-- preimage (mapAtlasTransposalObject result sourceElement)
--   == Just sourceElement
-- @
--
-- This is the same proof boundary used by 'DomanialInsertion': the executable
-- preimage makes the injectivity condition compositional and testable.
{-@
atlasTransposal
  :: sourceWitness:AtlasWitness source
  -> hom:{AtlasHom source target | atlasHomSourceOwner sourceWitness hom == atlasWitnessOwner sourceWitness}
  -> objectPreimage:(targetElement:AtlasTransposalElement target
       -> Maybe ({sourceElement:AtlasTransposalElement source |
            atlasHomTargetValid sourceWitness hom targetElement => atlasHomSourceValid sourceWitness hom sourceElement}))
  -> (sourceElement:{AtlasTransposalElement source | atlasHomSourceValid sourceWitness hom sourceElement}
       -> {objectPreimage (mapAtlasHomObject sourceWitness hom sourceElement) == Just sourceElement})
  -> {result:AtlasTransposal source target |
       atlasTransposalSourceOwner result == Just (atlasWitnessOwner sourceWitness)
       && atlasTransposalTargetOwner result == Just (atlasHomTargetOwner sourceWitness hom)
       && atlasTransposalSourceValid result == atlasHomSourceValid sourceWitness hom
       && mapAtlasTransposalObject result == mapAtlasHomObject sourceWitness hom
       && atlasTransposalPreimage result == objectPreimage}
@-}
-- ALIGN: ATLAS-TRANSPOSAL-INJECTIVITY.
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-OWNERS.
atlasTransposal
  :: AtlasWitness source
  -> AtlasHom source target
  -> (AtlasTransposalElement target -> Maybe (AtlasTransposalElement source))
  -> (AtlasTransposalElement source -> ())
  -> AtlasTransposal source target
atlasTransposal sourceWitness hom objectPreimage leftInverse =
  let objects = homTransposalObjects sourceWitness hom
  in homTransposalObjectsRetains sourceWitness hom `seq` withTransposalObjects objects $ \sourceOwner targetOwner _ ->
    primitiveAtlasTransposal hom
      (transposalAction sourceOwner targetOwner
        (transposalObjectsMap objects) objectPreimage leftInverse)

-- | Forget the injectivity evidence. This is the inclusion
-- @AtlTrap ⟶ Atl@ from the Lean definition.
atlasTransposalHom
  :: AtlasTransposal source target
  -> AtlasHom source target
atlasTransposalHom (PrimitiveAtlasTransposal hom _) = hom
atlasTransposalHom (IdentityAtlasTransposal hom _) = hom
atlasTransposalHom (CompositeAtlasTransposal second first) =
  atlasTransposalHom second . atlasTransposalHom first

-- | Recover the underlying pagination morphism through the inclusion.
atlasTransposalPagination
  :: AtlasWitness source
  -> AtlasTransposal source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasTransposalPagination sourceWitness transposal =
  atlasHomPagination sourceWitness (atlasTransposalHom transposal)

-- | Apply the included Atlas arrow to a padded page element.
mapAtlasTransposalElement
  :: AtlasWitness source
  -> AtlasTransposal source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasTransposalElement sourceWitness transposal =
  mapAtlasHomElement sourceWitness (atlasTransposalHom transposal)

-- | Apply the included Atlas arrow to a page-element arrow.
mapAtlasTransposalArrow
  :: AtlasWitness source
  -> AtlasTransposal source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasTransposalArrow sourceWitness transposal =
  mapAtlasHomArrow sourceWitness (atlasTransposalHom transposal)

-- | Apply the included Atlas arrow to a cell and its dependent datum.
mapAtlasTransposalData
  :: AtlasWitness source
  -> AtlasTransposal source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasTransposalData sourceWitness transposal =
  mapAtlasHomData sourceWitness (atlasTransposalHom transposal)
