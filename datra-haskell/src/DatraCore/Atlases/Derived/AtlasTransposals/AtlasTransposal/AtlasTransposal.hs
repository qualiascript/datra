{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ opaque-reflect identityAtlasTransposal @-}
{-@ opaque-reflect composeAtlasTransposals @-}
{-@ opaque-reflect atlasHomSourceOwner @-}
{-@ opaque-reflect atlasHomTargetOwner @-}
{-@ opaque-reflect atlasTransposalSourceOwner @-}
{-@ opaque-reflect atlasTransposalTargetOwner @-}

-- | The wide subcategory of Atlases whose page-element maps are injective.
--
-- This is the Haskell presentation of Lean's @AtlTrap@: objects are unchanged
-- from 'Atlas', while arrows are restricted by an executable left inverse for
-- their action on Atlas elements.
module AtlasTransposal
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
  , atlasHomSourceValid
  , atlasHomTargetValid
  , mapAtlasHomObject
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

import AtlasTransposal.Internal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElementValid
  , atlasTransposalElementLT
  , atlasTransposalHom
  , atlasTransposalSourceValid
  , atlasTransposalPathValid
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasHomSourceOwner, atlasHomTargetOwner
  , atlasHomSourceValid
  , atlasHomTargetValid
  , mapAtlasHomObject
  , atlasTransposalLeftInverse
  , atlasTransposalPagination
  , atlasTransposalPreimage
  , composeAtlasTransposals
  , identityAtlasTransposal
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  , mapAtlasTransposalElement
  , mapAtlasTransposalObject
  , withAtlasTransposalElement
  )

import qualified AtlasTransposal.Internal as Internal
  (atlasTransposalElement, identityAtlasTransposalRetains, composeAtlasTransposalsRetains, atlasHomSourceAgrees)
import DomanialInsertion.Core (composePartialInverses)

import Atlas (AtlasHom)
import Atlas.Witness (AtlasWitness, AtlasObjectPaginationScope, atlasWitnessOwner, atlasWitnessElementValid, normalizeAtlasWitnessElement)
import AtlasTransposal.Element (transposalElementSource)
import PageElements.Structure (PageElement, SomePageElement (..))

{-@ identityAtlasTransposalRetains
      :: identity:{AtlasTransposal object object | identity == identityAtlasTransposal}
      -> source:AtlasTransposalElement object
      -> {mapAtlasTransposalObject identity source == source
           && atlasTransposalPreimage identity source == Just source
           && atlasTransposalPathValid identity source} @-}
identityAtlasTransposalRetains :: AtlasTransposal object object -> AtlasTransposalElement object -> ()
identityAtlasTransposalRetains identity source = Internal.identityAtlasTransposalRetains identity source

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
composeAtlasTransposalsRetains second first source target = Internal.composeAtlasTransposalsRetains second first source target

{-@ atlasTransposalElement :: witness:AtlasWitness atlasObject
      -> source:PageElement (AtlasObjectPaginationScope atlasObject) object
      -> {result:AtlasTransposalElement atlasObject |
           transposalElementSource result == SomePageElement (normalizeAtlasWitnessElement witness source)
           && (atlasWitnessElementValid witness source => atlasTransposalElementValid witness result)} @-}
atlasTransposalElement
  :: AtlasWitness atlasObject
  -> PageElement (AtlasObjectPaginationScope atlasObject) object
  -> AtlasTransposalElement atlasObject
atlasTransposalElement witness source = Internal.atlasTransposalElement witness source

{-@ atlasHomSourceAgrees :: witness:AtlasWitness source
      -> hom:{AtlasHom source target | atlasHomSourceOwner witness hom == atlasWitnessOwner witness}
      -> element:AtlasTransposalElement source
      -> {atlasTransposalElementValid witness element <=> atlasHomSourceValid witness hom element} @-}
atlasHomSourceAgrees :: AtlasWitness source -> AtlasHom source target -> AtlasTransposalElement source -> ()
atlasHomSourceAgrees witness hom element = Internal.atlasHomSourceAgrees witness hom element
