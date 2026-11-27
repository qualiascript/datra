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
  , atlasTransposalTargetWitness, atlasTransposalMapValid
  , atlasTransposalOwnedPath, atlasTransposalComposeOwned
  , atlasTransposalSourceValid, atlasTransposalPathValid, atlasTransposalPathSource
  , mapAtlasTransposalObject, atlasTransposalPreimage
  , atlasTransposalLeftInverse, identityAtlasTransposal, identityAtlasTransposalRetains
  , composeAtlasTransposals, composeAtlasTransposalsRetains
  , atlasTransposalLeftIdentity, atlasTransposalRightIdentity, atlasTransposalAssociativity
  ) where

import Atlas (atlasHomTargetObjectEquality, identityAtlasHom, AtlasHom, AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import Atlas.Witness (AtlasWitness, AtlasOwner, atlasOwner, atlasWitnessOwner, atlasWitnessFor)
import AtlasTransposal.Element (AtlasTransposalElement, transposalElementValid,
  transposalWitnessElementValid, transposalWitnessOwnerAgrees)
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
    -> TransposalIdentity source target
    -> AtlasTransposal source target
  CompositeAtlasTransposal :: AtlasTransposal middle target -> AtlasTransposal source middle
    -> AtlasTransposal source target

-- | A symbolic identity transports a supplied owner along with its raw action.
-- Keeping the transport law here avoids specializing object-indexed carriers
-- when the recursive interpreter eliminates the syntax node.
{-@ data TransposalIdentity source target = TransposalIdentity
      { storedIdentityInsertion :: DomanialInsertion (AtlasTransposalElement source) (AtlasTransposalElement target)
      , identityTargetWitness :: witness:AtlasWitness source
          -> {result:AtlasWitness target | atlasWitnessOwner result == atlasWitnessOwner witness}
      , identityMapValid :: witness:AtlasWitness source
          -> element:{AtlasTransposalElement source | transposalWitnessElementValid witness element}
          -> {transposalWitnessElementValid (identityTargetWitness witness)
                (applyInsertion storedIdentityInsertion element)}
      } @-}
data TransposalIdentity source target = TransposalIdentity
  { storedIdentityInsertion :: DomanialInsertion (AtlasTransposalElement source) (AtlasTransposalElement target)
  , identityTargetWitness :: AtlasWitness source -> AtlasWitness target
  , identityMapValid :: AtlasWitness source -> AtlasTransposalElement source -> ()
  }

-- | Recover the last stored target, or preserve the supplied owner through an
-- identity-only tree. No runtime equality test on Atlas owners is needed.
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-TARGET-WITNESS.
{-@ opaque-reflect atlasHomTargetObjectEquality @-}
{-@ reflect atlasTransposalTargetWitness @-}
{-@ atlasTransposalTargetWitness :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> {result:AtlasWitness target |
           atlasTransposalTargetOwner arrow == Just (atlasWitnessOwner result)
           || (atlasTransposalTargetOwner arrow == Nothing
                && atlasWitnessOwner result == atlasWitnessOwner witness)} @-}
atlasTransposalTargetWitness :: AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
atlasTransposalTargetWitness witness (PrimitiveAtlasTransposal hom action) =
  atlasWitnessFor (atlasHomTargetObjectEquality witness hom) (transposalActionTarget action)
atlasTransposalTargetWitness witness (IdentityAtlasTransposal _ identity) = identityTargetWitness identity witness
atlasTransposalTargetWitness witness (CompositeAtlasTransposal second first) =
  atlasTransposalTargetWitness (atlasTransposalTargetWitness witness first) second

-- | An accepted execution ends in its recovered target's owning domain.
-- The path premise is needed independently of witnessed source membership.
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-TARGET-VALID.
{-@ atlasTransposalMapValid :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source |
           transposalWitnessElementValid witness element && atlasTransposalPathValid arrow element}
      -> {transposalWitnessElementValid (atlasTransposalTargetWitness witness arrow)
           (mapAtlasTransposalObject arrow element)} @-}
atlasTransposalMapValid :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalMapValid witness arrow@(PrimitiveAtlasTransposal _ action) source =
  let target = mapTransposalAction action source
  in transposalWitnessOwnerAgrees (atlasTransposalTargetWitness witness arrow) (transposalActionTarget action) target
atlasTransposalMapValid witness (IdentityAtlasTransposal _ identity) source = identityMapValid identity witness source
atlasTransposalMapValid witness (CompositeAtlasTransposal second first) source =
  atlasTransposalMapValid witness first source `seq`
    atlasTransposalMapValid (atlasTransposalTargetWitness witness first) second (mapAtlasTransposalObject first source)

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


-- | A logical compatibility condition, not an executable owner comparison.
-- Identity-only subtrees have no fixed endpoints; materialized joins must
-- equate the complete owners, independently of their nominal object indices.
{-@ measure atlasTransposalOwnersCompatible :: AtlasTransposal source target -> Bool
      atlasTransposalOwnersCompatible (PrimitiveAtlasTransposal hom action) = true
      atlasTransposalOwnersCompatible (IdentityAtlasTransposal hom identity) = true
      atlasTransposalOwnersCompatible (CompositeAtlasTransposal second first) =
        atlasTransposalOwnersCompatible first && atlasTransposalOwnersCompatible second
        && (atlasTransposalTargetOwner first == Nothing
             || atlasTransposalSourceOwner second == Nothing
             || atlasTransposalTargetOwner first == atlasTransposalSourceOwner second)
  @-}

-- | A subtree has no stored source precisely when it has no stored target.
{-@ atlasTransposalOwnersEmpty :: arrow:AtlasTransposal source target
      -> {(atlasTransposalSourceOwner arrow == Nothing) <=> (atlasTransposalTargetOwner arrow == Nothing)} @-}
atlasTransposalOwnersEmpty :: AtlasTransposal source target -> ()
atlasTransposalOwnersEmpty (PrimitiveAtlasTransposal _ _) = ()
atlasTransposalOwnersEmpty (IdentityAtlasTransposal _ _) = ()
atlasTransposalOwnersEmpty (CompositeAtlasTransposal second first) =
  atlasTransposalOwnersEmpty first `seq` atlasTransposalOwnersEmpty second `seq`
    case atlasTransposalSourceOwner first of
      Nothing -> case atlasTransposalTargetOwner second of
        Nothing -> ()
        Just _ -> ()
      Just _ -> case atlasTransposalTargetOwner second of
        Nothing -> ()
        Just _ -> ()

-- | Compatible complete owners propagate witnessed membership through every
-- stage, even when the first subtree is a symbolic identity.
-- ALIGN: ATLAS-TRANSPOSAL-OWNER-COMPATIBLE-PATH.
{-@ atlasTransposalOwnedPath :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | atlasTransposalOwnersCompatible arrow
           && (atlasTransposalSourceOwner arrow == Nothing
                || atlasTransposalSourceOwner arrow == Just (atlasWitnessOwner witness))}
      -> source:{AtlasTransposalElement source | transposalWitnessElementValid witness source}
      -> {atlasTransposalPathValid arrow source} @-}
atlasTransposalOwnedPath :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalOwnedPath witness (PrimitiveAtlasTransposal _ action) source =
  transposalWitnessOwnerAgrees witness (transposalActionSource action) source
atlasTransposalOwnedPath _ (IdentityAtlasTransposal _ _) _ = ()
atlasTransposalOwnedPath witness (CompositeAtlasTransposal second first) source =
  atlasTransposalOwnersEmpty first `seq`
  atlasTransposalOwnedPath witness first source `seq`
  atlasTransposalMapValid witness first source `seq`
  atlasTransposalOwnedPath (atlasTransposalTargetWitness witness first) second (mapAtlasTransposalObject first source)

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


-- | Complete path acceptance includes the declared first source domain.
-- ALIGN: ATLAS-TRANSPOSAL-PATH-SOURCE.
{-@ atlasTransposalPathSource :: arrow:AtlasTransposal source target
      -> source:AtlasTransposalElement source
      -> {atlasTransposalPathValid arrow source => atlasTransposalSourceValid arrow source} @-}
atlasTransposalPathSource :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalPathSource (PrimitiveAtlasTransposal _ _) _ = ()
atlasTransposalPathSource (IdentityAtlasTransposal _ _) _ = ()
atlasTransposalPathSource (CompositeAtlasTransposal _ first) source = atlasTransposalPathSource first source

-- | Apply the injective object map on genuine Atlas elements.
{-@ reflect mapAtlasTransposalObject @-}
mapAtlasTransposalObject
  :: AtlasTransposal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransposalObject (PrimitiveAtlasTransposal _ action) source = mapTransposalAction action source
mapAtlasTransposalObject (IdentityAtlasTransposal _ identity) source = applyInsertion (storedIdentityInsertion identity) source
mapAtlasTransposalObject (CompositeAtlasTransposal second first) source =
  mapAtlasTransposalObject second (mapAtlasTransposalObject first source)

-- | Try to recover the source of an element under a transposal's object map.
{-@ reflect atlasTransposalPreimage @-}
atlasTransposalPreimage
  :: AtlasTransposal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransposalPreimage (PrimitiveAtlasTransposal _ action) target = transposalActionPreimage action target
atlasTransposalPreimage (IdentityAtlasTransposal _ identity) target = preimage (storedIdentityInsertion identity) target
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
atlasTransposalLeftInverse (IdentityAtlasTransposal _ identity) source =
  insertionLeftInverse (storedIdentityInsertion identity) source
atlasTransposalLeftInverse (CompositeAtlasTransposal second first) source =
  atlasTransposalLeftInverse second (mapAtlasTransposalObject first source) `seq`
    atlasTransposalLeftInverse first source

-- | The identity Atlas arrow with its identity object preimage.
-- ALIGN: ATLAS-TRANSPOSAL-IDENTITY.
{-@ opaque-reflect identityAtlasHom @-}
{-@ reflect identityAtlasTransposal @-}
{-@ identityAtlasTransposal :: {result:AtlasTransposal object object |
      atlasTransposalOwnersCompatible result && atlasTransposalSourceOwner result == Nothing
        && atlasTransposalTargetOwner result == Nothing} @-}
identityAtlasTransposal :: AtlasTransposal object object
identityAtlasTransposal = IdentityAtlasTransposal identityAtlasHom
  (TransposalIdentity identityInsertion preserveIdentityWitness preserveIdentityMembership)

{-@ reflect preserveIdentityWitness @-}
preserveIdentityWitness :: AtlasWitness object -> AtlasWitness object
preserveIdentityWitness witness = witness

{-@ preserveIdentityMembership :: witness:AtlasWitness object
      -> source:{AtlasTransposalElement object | transposalWitnessElementValid witness source}
      -> {transposalWitnessElementValid (preserveIdentityWitness witness)
           (applyInsertion identityInsertion source)} @-}
preserveIdentityMembership :: AtlasWitness object -> AtlasTransposalElement object -> ()
preserveIdentityMembership _ source = identityInsertionApply source

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

-- | Compose owner evidence for the existing syntax operation. The second
-- subtree starts at the actual target witness recovered from the first.
-- ALIGN: ATLAS-TRANSPOSAL-OWNER-COMPATIBLE-COMPOSITION.
{-@ atlasTransposalComposeOwned :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | atlasTransposalOwnersCompatible first
           && (atlasTransposalSourceOwner first == Nothing
                || atlasTransposalSourceOwner first == Just (atlasWitnessOwner witness))}
      -> second:{AtlasTransposal middle target | atlasTransposalOwnersCompatible second
           && (atlasTransposalSourceOwner second == Nothing
                || atlasTransposalSourceOwner second == Just (atlasWitnessOwner (atlasTransposalTargetWitness witness first)))}
      -> {atlasTransposalOwnersCompatible (composeAtlasTransposals second first)
           && (atlasTransposalSourceOwner (composeAtlasTransposals second first) == Nothing
                || atlasTransposalSourceOwner (composeAtlasTransposals second first) == Just (atlasWitnessOwner witness))} @-}
atlasTransposalComposeOwned :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target -> ()
atlasTransposalComposeOwned witness first _ =
  atlasTransposalOwnersEmpty first `seq` atlasTransposalTargetWitness witness first `seq` ()

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

-- | Symbolic identity preserves raw execution and retained endpoint owners.
-- ALIGN: ATLAS-TRANSPOSAL-LEFT-IDENTITY.
{-@ atlasTransposalLeftIdentity :: identity:{AtlasTransposal target target | identity == identityAtlasTransposal}
      -> arrow:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals identity arrow) sourceElement == mapAtlasTransposalObject arrow sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals identity arrow) targetElement == atlasTransposalPreimage arrow targetElement
           && (atlasTransposalPathValid (composeAtlasTransposals identity arrow) sourceElement <=> atlasTransposalPathValid arrow sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals identity arrow) == atlasTransposalSourceOwner arrow
           && atlasTransposalTargetOwner (composeAtlasTransposals identity arrow) == atlasTransposalTargetOwner arrow} @-}
atlasTransposalLeftIdentity :: AtlasTransposal target target -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
atlasTransposalLeftIdentity identity arrow source target =
  identityAtlasTransposalRetains identity (mapAtlasTransposalObject arrow source) `seq`
  identityAtlasTransposalRetains identity target `seq`
  case atlasTransposalSourceOwner arrow of
    Nothing -> ()
    Just _ -> ()

-- | Symbolic identity preserves raw execution and retained endpoint owners.
-- ALIGN: ATLAS-TRANSPOSAL-RIGHT-IDENTITY.
{-@ atlasTransposalRightIdentity :: identity:{AtlasTransposal source source | identity == identityAtlasTransposal}
      -> arrow:AtlasTransposal source target
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals arrow identity) sourceElement == mapAtlasTransposalObject arrow sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals arrow identity) targetElement == atlasTransposalPreimage arrow targetElement
           && (atlasTransposalPathValid (composeAtlasTransposals arrow identity) sourceElement <=> atlasTransposalPathValid arrow sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals arrow identity) == atlasTransposalSourceOwner arrow
           && atlasTransposalTargetOwner (composeAtlasTransposals arrow identity) == atlasTransposalTargetOwner arrow} @-}
atlasTransposalRightIdentity :: AtlasTransposal source source -> AtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
atlasTransposalRightIdentity identity arrow source target =
  identityAtlasTransposalRetains identity source `seq`
  case atlasTransposalTargetOwner arrow of
    Nothing -> inverseIdentity
    Just _ -> inverseIdentity
  where
    inverseIdentity = case atlasTransposalPreimage arrow target of
      Nothing -> ()
      Just value -> identityAtlasTransposalRetains identity value

-- | Regrouping syntax preserves both raw callbacks, domains, and endpoint owners.
-- ALIGN: ATLAS-TRANSPOSAL-ASSOCIATIVITY.
{-@ atlasTransposalAssociativity :: third:AtlasTransposal next target
      -> second:AtlasTransposal middle next -> first:AtlasTransposal source middle
      -> sourceElement:AtlasTransposalElement source -> targetElement:AtlasTransposalElement target
      -> {mapAtlasTransposalObject (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement == mapAtlasTransposalObject (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement
           && atlasTransposalPreimage (composeAtlasTransposals third (composeAtlasTransposals second first)) targetElement == atlasTransposalPreimage (composeAtlasTransposals (composeAtlasTransposals third second) first) targetElement
           && (atlasTransposalSourceValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalSourceValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)
           && (atlasTransposalPathValid (composeAtlasTransposals third (composeAtlasTransposals second first)) sourceElement <=> atlasTransposalPathValid (composeAtlasTransposals (composeAtlasTransposals third second) first) sourceElement)
           && atlasTransposalSourceOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) == atlasTransposalSourceOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)
           && atlasTransposalTargetOwner (composeAtlasTransposals third (composeAtlasTransposals second first)) == atlasTransposalTargetOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)} @-}
atlasTransposalAssociativity :: AtlasTransposal next target -> AtlasTransposal middle next
  -> AtlasTransposal source middle -> AtlasTransposalElement source -> AtlasTransposalElement target -> ()
atlasTransposalAssociativity third second first _ target =
  atlasTransposalPreimageAssociativity third second first target `seq`
  case (atlasTransposalSourceOwner first, atlasTransposalTargetOwner third) of
    (Nothing, Nothing) -> ()
    (Nothing, Just _) -> ()
    (Just _, Nothing) -> ()
    (Just _, Just _) -> ()

{-@ atlasTransposalPreimageAssociativity :: third:AtlasTransposal next target
      -> second:AtlasTransposal middle next -> first:AtlasTransposal source middle
      -> targetElement:AtlasTransposalElement target
      -> {atlasTransposalPreimage (composeAtlasTransposals third (composeAtlasTransposals second first)) targetElement
           == atlasTransposalPreimage (composeAtlasTransposals (composeAtlasTransposals third second) first) targetElement} @-}
atlasTransposalPreimageAssociativity :: AtlasTransposal next target -> AtlasTransposal middle next
  -> AtlasTransposal source middle -> AtlasTransposalElement target -> ()
atlasTransposalPreimageAssociativity third second _ target =
  case atlasTransposalPreimage third target of
    Nothing -> ()
    Just middle -> case atlasTransposalPreimage second middle of
      Nothing -> ()
      Just _ -> ()
