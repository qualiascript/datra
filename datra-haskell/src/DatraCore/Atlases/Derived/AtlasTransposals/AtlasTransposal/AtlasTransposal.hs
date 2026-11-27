{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ opaque-reflect identityAtlasTransposal @-}
{-@ opaque-reflect composeAtlasTransposals @-}
{-@ opaque-reflect atlasHomSourceOwner @-}
{-@ opaque-reflect atlasHomTargetOwner @-}
{-@ opaque-reflect atlasHomTargetWitness @-}
{-@ opaque-reflect Objects.atlasHomTargetWitness @-}
{-@ opaque-reflect atlasTransposalSourceOwner @-}
{-@ opaque-reflect atlasTransposalTargetOwner @-}
{-@ opaque-reflect atlasTransposalTargetWitness @-}
{-@ opaque-reflect Internal.atlasTransposalTargetWitness @-}

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
  , atlasTransposalPathValid, atlasTransposalPathSource
  , atlasTransposalSourceOwner, atlasTransposalTargetOwner
  , atlasHomSourceOwner, atlasHomTargetOwner
  , atlasHomSourceAgrees, atlasHomTargetAgrees, atlasHomMiddleValid, atlasHomNextSourceValid
  , atlasHomTargetWitness
  , atlasTransposalTargetWitness, atlasTransposalMapValid
  , atlasTransposalOwnedPath, atlasTransposalComposeOwned
  , atlasTransposalCompositionOwners, atlasTransposalOwnersAssociativity
  , atlasHomSourceValid
  , atlasHomTargetValid
  , mapAtlasHomObject
  , mapAtlasTransposalObject
  , atlasTransposalPreimage
  , atlasTransposalLeftInverse
  , identityAtlasTransposal
  , identityAtlasTransposalRetains
  , composeAtlasTransposals
  , atlasTransposalLeftIdentity, atlasTransposalRightIdentity, atlasTransposalAssociativity
  , composeAtlasTransposalsRetains
  , atlasTransposalPagination
  , mapAtlasTransposalElement
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  ) where

import AtlasTransposal.Internal
  ( AtlasTransposal
  , AtlasTransposalElement
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
  (atlasTransposalOwnedPath, atlasTransposalComposeOwned, atlasTransposalTargetWitness, atlasTransposalMapValid, atlasTransposalLeftIdentity, atlasTransposalRightIdentity, atlasTransposalAssociativity, atlasTransposal, atlasTransposalElement, identityAtlasTransposalRetains, composeAtlasTransposalsRetains, atlasHomSourceAgrees, atlasHomTargetAgrees, atlasHomMiddleValid, atlasHomNextSourceValid)
import qualified AtlasTransposal.Syntax.Internal as Syntax (atlasTransposalPathSource, atlasTransposalCompositionOwners, atlasTransposalOwnersAssociativity)
import qualified AtlasTransposal.Objects as Objects (atlasHomTargetWitness)
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

{-@ atlasHomTargetAgrees :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> targetWitness:{AtlasWitness target | atlasWitnessOwner targetWitness == atlasHomTargetOwner sourceWitness hom}
      -> element:AtlasTransposalElement target
      -> {atlasTransposalElementValid targetWitness element <=> atlasHomTargetValid sourceWitness hom element} @-}
atlasHomTargetAgrees :: AtlasWitness source -> AtlasHom source target -> AtlasWitness target
  -> AtlasTransposalElement target -> ()
atlasHomTargetAgrees sourceWitness hom targetWitness element = Internal.atlasHomTargetAgrees sourceWitness hom targetWitness element

{-@ atlasHomMiddleValid :: sourceWitness:AtlasWitness source
      -> first:{AtlasHom source middle | atlasHomSourceOwner sourceWitness first == atlasWitnessOwner sourceWitness}
      -> middleWitness:{AtlasWitness middle | atlasWitnessOwner middleWitness == atlasHomTargetOwner sourceWitness first}
      -> second:{AtlasHom middle target | atlasHomSourceOwner middleWitness second == atlasWitnessOwner middleWitness}
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid sourceWitness sourceElement}
      -> {atlasHomSourceValid middleWitness second (mapAtlasHomObject sourceWitness first sourceElement)} @-}
atlasHomMiddleValid :: AtlasWitness source -> AtlasHom source middle -> AtlasWitness middle -> AtlasHom middle target
  -> AtlasTransposalElement source -> ()
atlasHomMiddleValid sourceWitness first middleWitness second source = Internal.atlasHomMiddleValid sourceWitness first middleWitness second source

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
       atlasTransposalOwnersCompatible result
       && atlasTransposalSourceOwner result == Just (atlasWitnessOwner sourceWitness)
       && atlasTransposalTargetOwner result == Just (atlasHomTargetOwner sourceWitness hom)
       && atlasTransposalSourceValid result == atlasHomSourceValid sourceWitness hom
       && atlasTransposalPathValid result == atlasHomSourceValid sourceWitness hom
       && mapAtlasTransposalObject result == mapAtlasHomObject sourceWitness hom
       && atlasTransposalPreimage result == objectPreimage}
@-}
atlasTransposal
  :: AtlasWitness source
  -> AtlasHom source target
  -> (AtlasTransposalElement target -> Maybe (AtlasTransposalElement source))
  -> (AtlasTransposalElement source -> ())
  -> AtlasTransposal source target
atlasTransposal witness hom backward leftInverse = Internal.atlasTransposal witness hom backward leftInverse

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
atlasTransposalLeftIdentity identity arrow source target = Internal.atlasTransposalLeftIdentity identity arrow source target

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
atlasTransposalRightIdentity identity arrow source target = Internal.atlasTransposalRightIdentity identity arrow source target

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
atlasTransposalAssociativity third second first source target =
  Internal.atlasTransposalAssociativity third second first source target

{-@ atlasHomNextSourceValid :: sourceWitness:AtlasWitness source
      -> first:{AtlasHom source middle | atlasHomSourceOwner sourceWitness first == atlasWitnessOwner sourceWitness}
      -> second:{AtlasHom middle target |
           atlasHomSourceOwner (atlasHomTargetWitness sourceWitness first) second == atlasHomTargetOwner sourceWitness first}
      -> sourceElement:{AtlasTransposalElement source | atlasTransposalElementValid sourceWitness sourceElement}
      -> {atlasHomSourceValid (atlasHomTargetWitness sourceWitness first) second
           (mapAtlasHomObject sourceWitness first sourceElement)} @-}
atlasHomNextSourceValid :: AtlasWitness source -> AtlasHom source middle -> AtlasHom middle target
  -> AtlasTransposalElement source -> ()
atlasHomNextSourceValid sourceWitness first second source =
  atlasHomTargetWitness sourceWitness first `seq`
    Internal.atlasHomNextSourceValid sourceWitness first second source

{-@ atlasHomTargetWitness :: sourceWitness:AtlasWitness source -> hom:AtlasHom source target
      -> {witness:AtlasWitness target |
           atlasWitnessOwner witness == atlasHomTargetOwner sourceWitness hom
           && witness == Objects.atlasHomTargetWitness sourceWitness hom} @-}
atlasHomTargetWitness :: AtlasWitness source -> AtlasHom source target -> AtlasWitness target
atlasHomTargetWitness sourceWitness hom = Objects.atlasHomTargetWitness sourceWitness hom

-- | Recover the target of the stored syntax, including identity-only subtrees.
{-@ atlasTransposalTargetWitness :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> {result:AtlasWitness target |
           result == Internal.atlasTransposalTargetWitness witness arrow
           && (atlasTransposalTargetOwner arrow == Just (atlasWitnessOwner result)
             || (atlasTransposalTargetOwner arrow == Nothing
                  && atlasWitnessOwner result == atlasWitnessOwner witness))} @-}
atlasTransposalTargetWitness :: AtlasWitness source -> AtlasTransposal source target -> AtlasWitness target
atlasTransposalTargetWitness witness arrow = Internal.atlasTransposalTargetWitness witness arrow

{-@ atlasTransposalMapValid :: witness:AtlasWitness source -> arrow:AtlasTransposal source target
      -> element:{AtlasTransposalElement source |
           atlasTransposalElementValid witness element && atlasTransposalPathValid arrow element}
      -> {atlasTransposalElementValid (atlasTransposalTargetWitness witness arrow)
           (mapAtlasTransposalObject arrow element)} @-}
atlasTransposalMapValid :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalMapValid witness arrow source =
  atlasTransposalTargetWitness witness arrow `seq` Internal.atlasTransposalMapValid witness arrow source

-- | Public proof vocabulary for complete-owner compatibility. This is a
-- logical predicate; Atlas owners contain functions and are not compared at runtime.
{-@ predicate TransposalCompatible A = atlasTransposalOwnersCompatible A @-}
{-@ predicate TransposalOwnedBy W A = TransposalCompatible A
      && (atlasTransposalSourceOwner A == Nothing
           || atlasTransposalSourceOwner A == Just (atlasWitnessOwner W)) @-}

{-@ atlasTransposalOwnedPath :: witness:AtlasWitness source
      -> arrow:{AtlasTransposal source target | TransposalOwnedBy witness arrow}
      -> source:{AtlasTransposalElement source | atlasTransposalElementValid witness source}
      -> {atlasTransposalPathValid arrow source} @-}
atlasTransposalOwnedPath :: AtlasWitness source -> AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalOwnedPath witness arrow source = Internal.atlasTransposalOwnedPath witness arrow source

{-@ atlasTransposalComposeOwned :: witness:AtlasWitness source
      -> first:{AtlasTransposal source middle | TransposalOwnedBy witness first}
      -> second:{AtlasTransposal middle target | TransposalOwnedBy (atlasTransposalTargetWitness witness first) second}
      -> {TransposalOwnedBy witness (composeAtlasTransposals second first)} @-}
atlasTransposalComposeOwned :: AtlasWitness source -> AtlasTransposal source middle -> AtlasTransposal middle target -> ()
atlasTransposalComposeOwned witness first second =
  atlasTransposalTargetWitness witness first `seq` Internal.atlasTransposalComposeOwned witness first second

{-@ atlasTransposalPathSource :: arrow:AtlasTransposal source target -> source:AtlasTransposalElement source
      -> {atlasTransposalPathValid arrow source => atlasTransposalSourceValid arrow source} @-}
atlasTransposalPathSource :: AtlasTransposal source target -> AtlasTransposalElement source -> ()
atlasTransposalPathSource arrow source = Syntax.atlasTransposalPathSource arrow source

{-@ atlasTransposalCompositionOwners :: second:AtlasTransposal middle target -> first:AtlasTransposal source middle
      -> {atlasTransposalSourceOwner (composeAtlasTransposals second first)
             == (if atlasTransposalSourceOwner first == Nothing then atlasTransposalSourceOwner second else atlasTransposalSourceOwner first)
           && atlasTransposalTargetOwner (composeAtlasTransposals second first)
             == (if atlasTransposalTargetOwner second == Nothing then atlasTransposalTargetOwner first else atlasTransposalTargetOwner second)
           && (TransposalCompatible (composeAtlasTransposals second first)
             <=> (TransposalCompatible first && TransposalCompatible second
               && (atlasTransposalTargetOwner first == Nothing || atlasTransposalSourceOwner second == Nothing
                 || atlasTransposalTargetOwner first == atlasTransposalSourceOwner second)))} @-}
atlasTransposalCompositionOwners second first = Syntax.atlasTransposalCompositionOwners second first

{-@ atlasTransposalOwnersAssociativity :: third:AtlasTransposal next target
      -> second:AtlasTransposal middle next -> first:AtlasTransposal source middle
      -> {atlasTransposalSourceOwner (composeAtlasTransposals third (composeAtlasTransposals second first))
             == atlasTransposalSourceOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)
           && atlasTransposalTargetOwner (composeAtlasTransposals third (composeAtlasTransposals second first))
             == atlasTransposalTargetOwner (composeAtlasTransposals (composeAtlasTransposals third second) first)
           && (TransposalCompatible (composeAtlasTransposals third (composeAtlasTransposals second first))
             <=> TransposalCompatible (composeAtlasTransposals (composeAtlasTransposals third second) first))} @-}
atlasTransposalOwnersAssociativity third second first = Syntax.atlasTransposalOwnersAssociativity third second first
