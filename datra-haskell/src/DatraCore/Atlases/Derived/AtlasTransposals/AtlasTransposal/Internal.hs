{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Hidden implementation of the category of Atlas transposals.
--
-- This is the Haskell presentation of Lean's @AtlTrap@: objects are unchanged
-- from 'Atlas', while arrows are restricted by an executable left inverse for
-- their action on Atlas elements.
module AtlasTransposal.Internal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElement
  , withAtlasTransposalElement
  , atlasTransposal
  , atlasTransposalHom
  , mapAtlasTransposalObject
  , atlasTransposalPreimage
  , atlasTransposalLeftInverse
  , identityAtlasTransposal
  , composeAtlasTransposals
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
  , identityAtlasHom
  , mapAtlasHomArrow
  , mapAtlasHomData
  , mapAtlasHomElement
  )
import Control.Category (Category (..))
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , composeInsertions
  , domanialInsertion
  , identityInsertion
  , insertionLeftInverse
  , preimage
  )
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | One object of the finite page-element category belonging to an Atlas.
--
-- The constructor is hidden. 'atlasTransposalElement' first applies the
-- Atlas's coherence map, so padded occurrences denote their genuine stored
-- representative. This is the carrier on which Lean's @F.Pa.obj@ is required
-- to be injective; it deliberately does not use the non-injective action on
-- the auxiliary padded spine.
type role AtlasTransposalElement nominal
data AtlasTransposalElement atlasObject where
  AtlasTransposalElement
    :: PageElement (AtlasObjectPaginationScope atlasObject) object
    -> AtlasTransposalElement atlasObject

instance Eq (AtlasTransposalElement atlasObject) where
  AtlasTransposalElement left == AtlasTransposalElement right =
    pageElementPage left == pageElementPage right
      && pageElementPosition left == pageElementPosition right

instance Show (AtlasTransposalElement atlasObject) where
  showsPrec _ (AtlasTransposalElement element) =
    showString "AtlasTransposalElement "
      . shows (pageElementPage element, pageElementPosition element)

-- | Turn an occurrence on the padded spine into the corresponding genuine
-- Atlas element.
atlasTransposalElement
  :: AtlasWitness atlasObject
  -> PageElement (AtlasObjectPaginationScope atlasObject) object
  -> AtlasTransposalElement atlasObject
atlasTransposalElement witness element =
  withPageElement
    (mapAtlasHomElement witness identityAtlasHom element)
    AtlasTransposalElement

-- | Eliminate the existential cell identity of an Atlas element.
withAtlasTransposalElement
  :: AtlasTransposalElement atlasObject
  -> (forall object.
        PageElement (AtlasObjectPaginationScope atlasObject) object
        -> result)
  -> result
withAtlasTransposalElement (AtlasTransposalElement element) useElement =
  useElement element

-- | An arrow in the wide subcategory of Atlas transposals.
--
-- Besides the included Atlas arrow, an arrow stores a partial inverse to its
-- object action and a certificate that this inverse succeeds on every image.
-- The certificate is the constructive form of @Function.Injective F.Pa.obj@.
-- Keeping the constructor private ensures identities and composites cannot
-- enter the subcategory without their derived certificates.
type role AtlasTransposal nominal nominal
data AtlasTransposal source target = AtlasTransposal
  (AtlasHom source target)
  (DomanialInsertion
    (AtlasTransposalElement source)
    (AtlasTransposalElement target))

{-@ reflect mapAtlasHomObject @-}
mapAtlasHomObject
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasHomObject sourceWitness hom
    (AtlasTransposalElement sourceElement) =
  withPageElement
    (mapAtlasHomElement sourceWitness hom sourceElement)
    AtlasTransposalElement

-- | Restrict an Atlas arrow to a transposal.
--
-- The final argument must certify, for every @sourceElement@, that
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
  -> hom:AtlasHom source target
  -> objectPreimage:(AtlasTransposalElement target
       -> Maybe (AtlasTransposalElement source))
  -> (sourceElement:AtlasTransposalElement source
       -> { proof:() |
            objectPreimage
              (mapAtlasHomObject sourceWitness hom sourceElement)
              == Just sourceElement })
  -> AtlasTransposal source target
@-}
atlasTransposal
  :: AtlasWitness source
  -> AtlasHom source target
  -> (AtlasTransposalElement target
       -> Maybe (AtlasTransposalElement source))
  -> (AtlasTransposalElement source -> ())
  -> AtlasTransposal source target
atlasTransposal sourceWitness hom objectPreimage leftInverse =
  AtlasTransposal hom
    (domanialInsertion
      (mapAtlasHomObject sourceWitness hom)
      objectPreimage
      leftInverse)

-- | Forget the injectivity evidence. This is the inclusion
-- @AtlTrap ⟶ Atl@ from the Lean definition.
atlasTransposalHom
  :: AtlasTransposal source target
  -> AtlasHom source target
atlasTransposalHom (AtlasTransposal hom _) = hom

-- | Apply the injective object map on genuine Atlas elements.
mapAtlasTransposalObject
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransposalObject (AtlasTransposal _ objectInsertion) =
  applyInsertion objectInsertion

-- | Try to recover the source of an element under a transposal's object map.
atlasTransposalPreimage
  :: AtlasTransposal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransposalPreimage (AtlasTransposal _ objectInsertion) =
  preimage objectInsertion

-- | Invoke the stored or mechanically derived left-inverse certificate.
atlasTransposalLeftInverse
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> ()
atlasTransposalLeftInverse (AtlasTransposal _ objectInsertion) =
  insertionLeftInverse objectInsertion

-- | The identity Atlas arrow with its identity object preimage.
identityAtlasTransposal :: AtlasTransposal object object
identityAtlasTransposal =
  AtlasTransposal identityAtlasHom identityInsertion

-- | Compose transposals in categorical order. Their partial preimages compose
-- in the reverse order, and the two left-inverse certificates establish the
-- certificate of the composite.
composeAtlasTransposals
  :: AtlasTransposal middle target
  -> AtlasTransposal source middle
  -> AtlasTransposal source target
composeAtlasTransposals second first =
  AtlasTransposal
    (atlasTransposalHom second . atlasTransposalHom first)
    (composeInsertions secondInsertion firstInsertion)
  where
    AtlasTransposal _ secondInsertion = second
    AtlasTransposal _ firstInsertion = first

-- | Atlas transposals form a category with all Atlas objects and only the
-- point-injective Atlas arrows.
instance Category AtlasTransposal where
  id = identityAtlasTransposal
  (.) = composeAtlasTransposals

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
