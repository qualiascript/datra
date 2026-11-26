{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE RankNTypes #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition actions retain the mapped image's certifying owner.
module Coalition.Action (mapCoalitionElement, withMappedCoalitionAction, withMappedCoalitionElement) where

import Atlas (Atlas, AtlasObject, atlasPageElements)
import AtlasCoveredPageElement (CoveredPageElement, coveredPageElementValid)
import AtlasTransversal (AtlasTransversal, withAtlasTransversalCoveredAction)
import Coalition.Element.Data
  ( CoalitionData, coalitionCoveredElement, coalitionFromCovered
  , coalitionElementValid, coalitionElementSource )
import PageElements (originPageElement)

{-@ predicate MappedCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}

{-@ mapCanonicalCoalition :: sourceOwner:Atlas sa ss sd so sf -> targetOwner:Atlas ta ts td to tf
      -> ({source:CoveredPageElement sa ss sd | coveredPageElementValid sourceOwner source}
           -> {image:CoveredPageElement ta ts td | coveredPageElementValid targetOwner image})
      -> source:{CoalitionData sa ss sd | MappedCoalitionValid sourceOwner source}
      -> {target:CoalitionData ta ts td | MappedCoalitionValid targetOwner target} @-}
mapCanonicalCoalition :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> (CoveredPageElement sa ss sd -> CoveredPageElement ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
mapCanonicalCoalition sourceOwner targetOwner forward source =
  coalitionFromCovered targetOwner (forward (coalitionCoveredElement sourceOwner source))

-- | Store both owners with the canonical mapping function.
type role CoalitionActionData nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data CoalitionActionData sa ss sd so sf ta ts td to tf = CoalitionActionData
      { coalitionStoredSource :: Atlas sa ss sd so sf
      , coalitionStoredTarget :: Atlas ta ts td to tf
      , coalitionStoredMap :: {source:CoalitionData sa ss sd | MappedCoalitionValid coalitionStoredSource source}
          -> {target:CoalitionData ta ts td | MappedCoalitionValid coalitionStoredTarget target}
      } @-}
data CoalitionActionData sa ss sd so sf ta ts td to tf = CoalitionActionData
  { coalitionStoredSource :: Atlas sa ss sd so sf
  , coalitionStoredTarget :: Atlas ta ts td to tf
  , coalitionStoredMap :: CoalitionData sa ss sd -> CoalitionData ta ts td
  }

type role CoalitionAction nominal nominal nominal nominal nominal nominal nominal nominal
data CoalitionAction sa ss sd so sf ta ts td where
  CoalitionAction :: CoalitionActionData sa ss sd so sf ta ts td to tf
    -> CoalitionAction sa ss sd so sf ta ts td

{-@ measure coalitionActionSource @-}
coalitionActionSource :: CoalitionAction sa ss sd so sf ta ts td -> Atlas sa ss sd so sf
coalitionActionSource (CoalitionAction action) = coalitionStoredSource action

{-@ reflect coalitionActionMap @-}
{-@ coalitionActionMap :: action:CoalitionAction sa ss sd so sf ta ts td
      -> ({source:CoalitionData sa ss sd | MappedCoalitionValid (coalitionActionSource action) source}
           -> CoalitionData ta ts td) @-}
coalitionActionMap :: CoalitionAction sa ss sd so sf ta ts td
  -> (CoalitionData sa ss sd -> CoalitionData ta ts td)
coalitionActionMap (CoalitionAction action) source = coalitionStoredMap action source

{-@ opaque-reflect coalitionAction @-}
{-@ coalitionAction :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> {action:CoalitionAction sa ss sd so sf ta ts td | coalitionActionSource action == owner} @-}
coalitionAction :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionAction sa ss sd so sf ta ts td
coalitionAction sourceOwner transversal =
  withAtlasTransversalCoveredAction sourceOwner transversal
    (\owner forward -> CoalitionAction
      (CoalitionActionData sourceOwner owner (mapCanonicalCoalition sourceOwner owner forward)))

{-@ withCoalitionAction :: action:CoalitionAction sa ss sd so sf ta ts td
      -> (forall o f. owner:Atlas ta ts td o f
            -> ({source:CoalitionData sa ss sd | MappedCoalitionValid (coalitionActionSource action) source}
                 -> {target:CoalitionData ta ts td | MappedCoalitionValid owner target
                      && target == coalitionActionMap action source})
            -> result)
      -> result @-}
withCoalitionAction :: CoalitionAction sa ss sd so sf ta ts td
  -> (forall o f. Atlas ta ts td o f
        -> (CoalitionData sa ss sd -> CoalitionData ta ts td) -> result)
  -> result
withCoalitionAction (CoalitionAction action) useAction =
  useAction (coalitionStoredTarget action) (\source -> coalitionStoredMap action source)

-- | Erase the target owner while retaining the exact stored function.
-- ALIGN: COALITION-FORWARD-CARRIER.
-- ALIGN: COALITION-FORWARD-INTERPRETATION.
{-@ reflect mapCoalitionElement @-}
{-@ mapCoalitionElement :: owner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | MappedCoalitionValid owner source}
      -> CoalitionData ta ts td @-}
mapCoalitionElement :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd -> CoalitionData ta ts td
mapCoalitionElement sourceOwner transversal source =
  coalitionActionMap (coalitionAction sourceOwner transversal) source

-- | Retain one target owner and the raw mapper's exact result for every source.
-- ALIGN: COALITION-FORWARD-OWNED-ACTION.
-- ALIGN: COALITION-FORWARD-ACTION-RETENTION.
{-@ withMappedCoalitionAction
      :: sourceOwner:Atlas sa ss sd so sf
      -> transversal:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> (forall o f. owner:Atlas ta ts td o f
            -> ({source:CoalitionData sa ss sd | MappedCoalitionValid sourceOwner source}
                 -> {target:CoalitionData ta ts td | MappedCoalitionValid owner target
                      && target == mapCoalitionElement sourceOwner transversal source})
            -> result)
      -> result @-}
withMappedCoalitionAction
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (forall o f. Atlas ta ts td o f
        -> (CoalitionData sa ss sd -> CoalitionData ta ts td) -> result)
  -> result
withMappedCoalitionAction sourceOwner transversal useAction =
  withCoalitionAction (coalitionAction sourceOwner transversal) useAction

-- | Map and canonicalize using the Atlas retained by the transversal. The
-- callback receives a valid canonical coalition for that exact target owner.
-- ALIGN: COALITION-FORWARD-OWNED-ELIMINATION.
-- ALIGN: COALITION-FORWARD-IMAGE-RETENTION.
{-@ withMappedCoalitionElement
      :: sourceOwner:Atlas sa ss sd so sf
      -> transversal:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | MappedCoalitionValid sourceOwner source}
      -> (forall o f. owner:Atlas ta ts td o f
            -> {element:CoalitionData ta ts td | MappedCoalitionValid owner element
                 && element == mapCoalitionElement sourceOwner transversal source}
            -> result)
      -> result @-}
withMappedCoalitionElement
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> CoalitionData sa ss sd
  -> (forall o f. Atlas ta ts td o f -> CoalitionData ta ts td -> result)
  -> result
withMappedCoalitionElement sourceOwner transversal source useElement =
  withMappedCoalitionAction sourceOwner transversal
    (\owner forward -> useElement owner (forward source))
