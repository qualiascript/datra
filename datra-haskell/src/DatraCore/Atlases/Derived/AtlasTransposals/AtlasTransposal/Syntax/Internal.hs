{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Raw transposal syntax and observations of its stored actions.
module AtlasTransposal.Syntax.Internal
  ( AtlasTransposal (..)
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasTransposalSourceValid, atlasTransposalPathValid
  , mapAtlasTransposalObject, atlasTransposalPreimage
  , atlasTransposalLeftInverse, identityAtlasTransposal, identityAtlasTransposalRetains
  , composeAtlasTransposals, composeAtlasTransposalsRetains
  ) where

import Atlas (identityAtlasHom, AtlasHom, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import Atlas.Witness (AtlasOwner, atlasOwner)
import AtlasTransposal.Element (AtlasTransposalElement, transposalElementValid)
import AtlasTransposal.Action
  (TransposalAction, transposalActionSource, transposalActionTarget,
   mapTransposalAction, transposalActionPreimage, transposalActionLeftInverse)
import DomanialInsertion (DomanialInsertion, applyInsertion, preimage, insertionLeftInverse, identityInsertion)
import DomanialInsertion.Core (identityInsertionApply, composePartialInverses)
import Control.Category (Category (..))
import Prelude hiding ((.), id)

-- | An arrow in the wide subcategory of Atlas transposals.
--
-- Besides the included Atlas arrow, an arrow stores a partial inverse to its
-- object action and a certificate that it succeeds on every accepted source image.
-- The certificate is the constructive form of @Function.Injective F.Pa.obj@.
-- Keeping the constructor private ensures identities and composites cannot
-- enter the subcategory without their derived certificates.
type role AtlasTransposal nominal nominal
data AtlasTransposal source target where
  PrimitiveAtlasTransposal
    :: AtlasHom source target
    -> TransposalAction
         (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
         (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
    -> AtlasTransposal source target
  IdentityAtlasTransposal
    :: AtlasHom source target
    -> DomanialInsertion (AtlasTransposalElement source) (AtlasTransposalElement target)
    -> AtlasTransposal source target
  CompositeAtlasTransposal :: AtlasTransposal middle target -> AtlasTransposal source middle
    -> AtlasTransposal source target

-- | Symbolic identities carry no fixed owner. A composite retains its first
-- and last materialized owners, skipping identity-only subtrees.
{-@ reflect atlasTransposalSourceOwner @-}
atlasTransposalSourceOwner :: AtlasTransposal source target -> Maybe AtlasOwner
atlasTransposalSourceOwner (PrimitiveAtlasTransposal _ action) =
  Just (atlasOwner (transposalActionSource action))
atlasTransposalSourceOwner (IdentityAtlasTransposal _ _) = Nothing
atlasTransposalSourceOwner (CompositeAtlasTransposal second first) =
  case atlasTransposalSourceOwner first of
    Nothing -> atlasTransposalSourceOwner second
    owner -> owner

{-@ reflect atlasTransposalTargetOwner @-}
atlasTransposalTargetOwner :: AtlasTransposal source target -> Maybe AtlasOwner
atlasTransposalTargetOwner (PrimitiveAtlasTransposal _ action) =
  Just (atlasOwner (transposalActionTarget action))
atlasTransposalTargetOwner (IdentityAtlasTransposal _ _) = Nothing
atlasTransposalTargetOwner (CompositeAtlasTransposal second first) =
  case atlasTransposalTargetOwner second of
    Nothing -> atlasTransposalTargetOwner first
    owner -> owner


-- | The source domain retained by a primitive, or inherited from the first
-- arrow of a composite. Symbolic identity has a total raw identity action.
{-@ reflect atlasTransposalSourceValid @-}
atlasTransposalSourceValid :: AtlasTransposal source target -> AtlasTransposalElement source -> Bool
atlasTransposalSourceValid (PrimitiveAtlasTransposal _ action) element =
  transposalElementValid (transposalActionSource action) element
atlasTransposalSourceValid (IdentityAtlasTransposal _ _) _ = True
atlasTransposalSourceValid (CompositeAtlasTransposal _ first) element = atlasTransposalSourceValid first element

-- | Check the owning domain at every primitive traversed by this raw input.
-- This is an execution premise, distinct from the first arrow's source domain.
-- Connecting those predicates requires the middle-owner compatibility proof.
{-@ reflect atlasTransposalPathValid @-}
atlasTransposalPathValid :: AtlasTransposal source target -> AtlasTransposalElement source -> Bool
atlasTransposalPathValid (PrimitiveAtlasTransposal _ action) element =
  transposalElementValid (transposalActionSource action) element
atlasTransposalPathValid (IdentityAtlasTransposal _ _) _ = True
atlasTransposalPathValid (CompositeAtlasTransposal second first) element =
  atlasTransposalPathValid first element
    && atlasTransposalPathValid second (mapAtlasTransposalObject first element)


-- | Apply the injective object map on genuine Atlas elements.
{-@ reflect mapAtlasTransposalObject @-}
mapAtlasTransposalObject
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransposalObject (PrimitiveAtlasTransposal _ action) source = mapTransposalAction action source
mapAtlasTransposalObject (IdentityAtlasTransposal _ insertion) source = applyInsertion insertion source
mapAtlasTransposalObject (CompositeAtlasTransposal second first) source =
  mapAtlasTransposalObject second (mapAtlasTransposalObject first source)

-- | Try to recover the source of an element under a transposal's object map.
{-@ reflect atlasTransposalPreimage @-}
atlasTransposalPreimage
  :: AtlasTransposal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransposalPreimage (PrimitiveAtlasTransposal _ action) target = transposalActionPreimage action target
atlasTransposalPreimage (IdentityAtlasTransposal _ insertion) target = preimage insertion target
atlasTransposalPreimage (CompositeAtlasTransposal second first) target =
  case atlasTransposalPreimage second target of
    Nothing -> Nothing
    Just middle -> atlasTransposalPreimage first middle


-- | Invoke the stored or mechanically derived left-inverse certificate.
-- ALIGN: ATLAS-TRANSPOSAL-LEFT-INVERSE.
-- ALIGN: ATLAS-TRANSPOSAL-PATH-LEFT-INVERSE.
{-@ atlasTransposalLeftInverse :: transposal:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source
      -> {atlasTransposalPathValid transposal sourceElement =>
           atlasTransposalPreimage transposal (mapAtlasTransposalObject transposal sourceElement)
             == Just sourceElement} @-}
atlasTransposalLeftInverse
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> ()
atlasTransposalLeftInverse (PrimitiveAtlasTransposal _ action) source
  | transposalElementValid (transposalActionSource action) source = transposalActionLeftInverse action source
  | otherwise = ()
atlasTransposalLeftInverse (IdentityAtlasTransposal _ insertion) source =
  insertionLeftInverse insertion source
atlasTransposalLeftInverse (CompositeAtlasTransposal second first) source =
  atlasTransposalLeftInverse second (mapAtlasTransposalObject first source) `seq`
    atlasTransposalLeftInverse first source

-- | The identity Atlas arrow with its identity object preimage.
-- ALIGN: ATLAS-TRANSPOSAL-IDENTITY.
{-@ opaque-reflect identityAtlasHom @-}
{-@ reflect identityAtlasTransposal @-}
identityAtlasTransposal :: AtlasTransposal object object
identityAtlasTransposal = IdentityAtlasTransposal identityAtlasHom identityInsertion

-- | Observe identity on every raw input, without an owning-domain premise.
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-IDENTITY-CALLBACKS.
{-@ identityAtlasTransposalRetains
      :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> source:AtlasTransposalElement object
      -> {mapAtlasTransposalObject identity source == source
           && atlasTransposalPreimage identity source == Just source
           && atlasTransposalPathValid identity source} @-}
identityAtlasTransposalRetains :: AtlasTransposal object object -> AtlasTransposalElement object -> ()
identityAtlasTransposalRetains identity source =
  identityInsertionApply source `seq` atlasTransposalLeftInverse identity source

-- | Compose transposals in categorical order. Their partial preimages compose
-- in the reverse order, and the two left-inverse certificates establish the
-- certificate of the composite.
-- ALIGN: ATLAS-TRANSPOSAL-COMPOSITION.
{-@ reflect composeAtlasTransposals @-}
composeAtlasTransposals
  :: AtlasTransposal middle target
  -> AtlasTransposal source middle
  -> AtlasTransposal source target
composeAtlasTransposals = CompositeAtlasTransposal

-- | Preserve both raw callbacks and the exact stage-acceptance condition.
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-COMPOSITION-CALLBACKS.
{-@ composeAtlasTransposalsRetains
      :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals second first) sourceElement
             == mapAtlasTransposalObject second (mapAtlasTransposalObject first sourceElement)
           && atlasTransposalPreimage (composeAtlasTransposals second first) targetElement
             == composePartialInverses (atlasTransposalPreimage first) (atlasTransposalPreimage second) targetElement
           && (atlasTransposalPathValid (composeAtlasTransposals second first) sourceElement
             <=> (atlasTransposalPathValid first sourceElement
               && atlasTransposalPathValid second (mapAtlasTransposalObject first sourceElement)))} @-}
composeAtlasTransposalsRetains :: AtlasTransposal middle target -> AtlasTransposal source middle
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
composeAtlasTransposalsRetains second first source target =
  composeAtlasTransposals second first `seq`
    case atlasTransposalPreimage second target of
      Nothing -> ()
      Just _ -> ()

-- | Atlas transposals form a category with all Atlas objects and only the
-- point-injective Atlas arrows.
instance Category AtlasTransposal where
  id = identityAtlasTransposal
  (.) = composeAtlasTransposals

