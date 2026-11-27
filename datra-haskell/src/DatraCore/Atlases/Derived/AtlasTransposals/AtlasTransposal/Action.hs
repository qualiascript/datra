{-# LANGUAGE CPP #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Object insertions retain the actual owners of both accepted carriers.
module AtlasTransposal.Action
  ( TransposalAction, transposalAction
  , transposalActionSource, transposalActionTarget, transposalActionInsertion
  , mapTransposalAction, transposalActionPreimage, transposalActionLeftInverse
  , identityTransposalAction, composeTransposalActions
  , identityTransposalActionRetains, composeTransposalActionsMap, composeTransposalActionsPreimage
  , mapTransposalMorphismElement
  ) where

import Atlas (Atlas, AtlasMorphismAction, atlasMorphismSource, atlasMorphismTarget,
  mapAtlasMorphismActionObject, normalizeAtlasElement, normalizeAtlasElementTraceValid, atlasCoherenceIdempotent)
import AtlasTransposal.Element
  (transposalElementValid, transposalOwnersAgree)
import Atlas.Witness (atlasOwner)
import AtlasTransposal.Element.Internal (TransposalElementData (..))
import DomanialInsertion.Core
  ( DomanialInsertion (..), insertionOn, composePartialInverses )

type role TransposalAction nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data TransposalAction sa ss sd so sf ta ts td to tf = TransposalAction
      { transposalActionSource :: Atlas sa ss sd so sf
      , transposalActionTarget :: Atlas ta ts td to tf
      , mapTransposalAction :: source:TransposalElementData sa ss sd
          -> {target:TransposalElementData ta ts td | transposalElementValid transposalActionSource source
               => transposalElementValid transposalActionTarget target}
      , transposalActionPreimage :: target:TransposalElementData ta ts td
          -> Maybe ({source:TransposalElementData sa ss sd | transposalElementValid transposalActionTarget target
               => transposalElementValid transposalActionSource source})
      , storedTransposalLeftInverse :: source:{TransposalElementData sa ss sd |
           transposalElementValid transposalActionSource source}
          -> {transposalActionPreimage (mapTransposalAction source) == Just source}
      } @-}
data TransposalAction sa ss sd so sf ta ts td to tf = TransposalAction
  { transposalActionSource :: Atlas sa ss sd so sf
  , transposalActionTarget :: Atlas ta ts td to tf
  , mapTransposalAction :: TransposalElementData sa ss sd -> TransposalElementData ta ts td
  , transposalActionPreimage :: TransposalElementData ta ts td -> Maybe (TransposalElementData sa ss sd)
  , storedTransposalLeftInverse :: TransposalElementData sa ss sd -> ()
  }

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-INSERTION.
{-@ reflect transposalActionInsertion @-}
{-@ transposalActionInsertion :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> {insertion:DomanialInsertion
           ({source:TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source})
           ({target:TransposalElementData ta ts td | transposalElementValid (transposalActionTarget action) target}) |
           applyInsertion insertion == mapTransposalAction action
           && preimage insertion == transposalActionPreimage action} @-}
transposalActionInsertion :: TransposalAction sa ss sd so sf ta ts td to tf
  -> DomanialInsertion (TransposalElementData sa ss sd) (TransposalElementData ta ts td)
transposalActionInsertion action = insertionOn
  (transposalElementValid (transposalActionSource action))
  (transposalElementValid (transposalActionTarget action))
  (mapTransposalAction action) (transposalActionPreimage action) (storedTransposalLeftInverse action)

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ACTION.
{-@ transposalAction :: sourceOwner:Atlas sa ss sd so sf -> targetOwner:Atlas ta ts td to tf
      -> forward:(source:TransposalElementData sa ss sd
           -> {target:TransposalElementData ta ts td | transposalElementValid sourceOwner source => transposalElementValid targetOwner target})
      -> backward:(target:TransposalElementData ta ts td
           -> Maybe ({source:TransposalElementData sa ss sd | transposalElementValid targetOwner target => transposalElementValid sourceOwner source}))
      -> (source:{TransposalElementData sa ss sd | transposalElementValid sourceOwner source}
           -> {backward (forward source) == Just source})
      -> {action:TransposalAction sa ss sd so sf ta ts td to tf |
           transposalActionSource action == sourceOwner && transposalActionTarget action == targetOwner
           && mapTransposalAction action == forward
           && transposalActionPreimage action == backward} @-}
transposalAction :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> (TransposalElementData sa ss sd -> TransposalElementData ta ts td)
  -> (TransposalElementData ta ts td -> Maybe (TransposalElementData sa ss sd))
  -> (TransposalElementData sa ss sd -> ())
  -> TransposalAction sa ss sd so sf ta ts td to tf
transposalAction sourceOwner targetOwner forward backward leftInverse =
  TransposalAction sourceOwner targetOwner forward backward leftInverse

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-LEFT-INVERSE.
{-@ transposalActionLeftInverse :: action:TransposalAction sa ss sd so sf ta ts td to tf
      -> source:{TransposalElementData sa ss sd | transposalElementValid (transposalActionSource action) source}
      -> {transposalActionPreimage action (mapTransposalAction action source) == Just source} @-}
transposalActionLeftInverse :: TransposalAction sa ss sd so sf ta ts td to tf
  -> TransposalElementData sa ss sd -> ()
transposalActionLeftInverse action = storedTransposalLeftInverse action

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-IDENTITY.
{-@ opaque-reflect identityTransposalAction @-}
{-@ identityTransposalAction :: owner:Atlas a s d o f
      -> {action:TransposalAction a s d o f a s d o f |
           transposalActionSource action == owner && transposalActionTarget action == owner
           && mapTransposalAction action == identityMap owner && transposalActionPreimage action == identityPreimage owner} @-}
identityTransposalAction :: Atlas a s d o f -> TransposalAction a s d o f a s d o f
identityTransposalAction owner = TransposalAction owner owner (identityMap owner) (identityPreimage owner) (identityRoundTrip owner)

{-@ reflect identityMap @-}
{-@ identityMap :: owner:Atlas a s d o f -> value:TransposalElementData a s d
      -> {result:TransposalElementData a s d | result == value
           && (transposalElementValid owner value => transposalElementValid owner result)} @-}
identityMap :: Atlas a s d o f -> TransposalElementData a s d -> TransposalElementData a s d
identityMap _ value = value

{-@ reflect identityPreimage @-}
{-@ identityPreimage :: owner:Atlas a s d o f -> value:TransposalElementData a s d
      -> {result:Maybe ({source:TransposalElementData a s d |
           transposalElementValid owner value => transposalElementValid owner source}) | result == Just value} @-}
identityPreimage :: Atlas a s d o f -> TransposalElementData a s d -> Maybe (TransposalElementData a s d)
identityPreimage _ value = Just value

{-@ identityRoundTrip :: owner:Atlas a s d o f -> value:TransposalElementData a s d
      -> {identityPreimage owner (identityMap owner value) == Just value} @-}
identityRoundTrip :: Atlas a s d o f -> TransposalElementData a s d -> ()
identityRoundTrip _ _ = ()

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-IDENTITY-CALLBACKS.
{-@ identityTransposalActionRetains :: owner:Atlas a s d o f -> source:TransposalElementData a s d
      -> {mapTransposalAction (identityTransposalAction owner) source == source
           && transposalActionPreimage (identityTransposalAction owner) source == Just source} @-}
identityTransposalActionRetains :: Atlas a s d o f -> TransposalElementData a s d -> ()
identityTransposalActionRetains owner source =
  identityTransposalAction owner `seq` identityMap owner source `seq` identityPreimage owner source `seq` ()

-- | Matching nominal scopes alone cannot substitute for this owner equation.
-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION.
{-@ opaque-reflect composeTransposalActions @-}
{-@ composeTransposalActions :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> {action:TransposalAction sa ss sd so sf ta ts td to tf |
           transposalActionSource action == transposalActionSource first
           && transposalActionTarget action == transposalActionTarget second
           && mapTransposalAction action == composedMap second first
           && transposalActionPreimage action == composedPreimage second first} @-}
composeTransposalActions :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1
  -> TransposalAction sa ss sd so sf ta ts td to tf
composeTransposalActions second first =
  TransposalAction (transposalActionSource first) (transposalActionTarget second)
    (composedMap second first)
    (composedPreimage second first) (composedRoundTrip second first)

{-@ reflect composedMap @-}
{-@ composedMap :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           transposalElementValid (transposalActionSource first) source => transposalElementValid (transposalActionTarget second) target} @-}
composedMap :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
composedMap second first source =
  let middle = mapTransposalAction first source
  in transposalOwnersAgree (transposalActionTarget first) (transposalActionSource second) middle `seq`
    mapTransposalAction second middle

{-@ reflect composedPreimage @-}
{-@ composedPreimage :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> target:TransposalElementData ta ts td
      -> {result:Maybe ({source:TransposalElementData sa ss sd |
           transposalElementValid (transposalActionTarget second) target => transposalElementValid (transposalActionSource first) source}) |
           result == composePartialInverses (transposalActionPreimage first) (transposalActionPreimage second) target} @-}
composedPreimage :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1
  -> TransposalElementData ta ts td -> Maybe (TransposalElementData sa ss sd)
composedPreimage second first target = case transposalActionPreimage second target of
  Nothing -> Nothing
  Just middle ->
    transposalOwnersAgree (transposalActionSource second) (transposalActionTarget first) middle `seq`
      transposalActionPreimage first middle

{-@ composedRoundTrip :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> source:{TransposalElementData sa ss sd | transposalElementValid (transposalActionSource first) source}
      -> {composedPreimage second first (composedMap second first source) == Just source} @-}
composedRoundTrip :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData sa ss sd -> ()
composedRoundTrip second first source =
  transposalOwnersAgree (transposalActionTarget first) (transposalActionSource second)
    (mapTransposalAction first source) `seq`
  storedTransposalLeftInverse second (mapTransposalAction first source) `seq`
    storedTransposalLeftInverse first source

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-MAP.
{-@ composeTransposalActionsMap :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> source:TransposalElementData sa ss sd
      -> {mapTransposalAction (composeTransposalActions second first) source
           == mapTransposalAction second (mapTransposalAction first source)} @-}
composeTransposalActionsMap :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData sa ss sd -> ()
composeTransposalActionsMap second first source =
  composeTransposalActions second first `seq` composedMap second first source `seq` ()

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-PREIMAGE.
{-@ composeTransposalActionsPreimage :: second:TransposalAction ma ms md mo mf ta ts td to tf
      -> first:{TransposalAction sa ss sd so sf ma ms md mo1 mf1 |
           atlasOwner (transposalActionTarget first) == atlasOwner (transposalActionSource second)}
      -> target:TransposalElementData ta ts td
      -> {transposalActionPreimage (composeTransposalActions second first) target
           == composePartialInverses (transposalActionPreimage first) (transposalActionPreimage second) target} @-}
composeTransposalActionsPreimage :: TransposalAction ma ms md mo mf ta ts td to tf
  -> TransposalAction sa ss sd so sf ma ms md mo1 mf1 -> TransposalElementData ta ts td -> ()
composeTransposalActionsPreimage second first target =
  composeTransposalActions second first `seq` composedPreimage second first target `seq` ()

-- | The primitive morphism's object map preserves owning trace validity;
-- transposal construction then takes its genuine normalized representative.
-- ALIGN: ATLAS-TRANSPOSAL-MORPHISM-ELEMENT.
{-@ reflect mapTransposalMorphismElement @-}
{-@ mapTransposalMorphismElement :: morphism:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:TransposalElementData sa ss sd
      -> {target:TransposalElementData ta ts td |
           transposalElementValid (atlasMorphismSource morphism) source => transposalElementValid (atlasMorphismTarget morphism) target} @-}
mapTransposalMorphismElement :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> TransposalElementData sa ss sd -> TransposalElementData ta ts td
mapTransposalMorphismElement morphism source@(AtlasTransposalElement occurrence) =
  let sourceOwner = atlasMorphismSource morphism
      normalizedSource = normalizeAtlasElement sourceOwner occurrence
      target = mapAtlasMorphismActionObject morphism normalizedSource
      targetOwner = atlasMorphismTarget morphism
      validity = if transposalElementValid sourceOwner source
        then normalizeAtlasElementTraceValid sourceOwner occurrence `seq`
          normalizeAtlasElementTraceValid targetOwner target else ()
  in validity `seq` atlasCoherenceIdempotent targetOwner target `seq`
     AtlasTransposalElement (normalizeAtlasElement targetOwner target)
