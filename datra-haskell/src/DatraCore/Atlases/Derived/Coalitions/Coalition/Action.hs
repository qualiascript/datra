{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition actions retain the mapped image's certifying owner.
module Coalition.Action (withMappedCoalitionAction, withMappedCoalitionElement) where

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

-- | Retain one target owner for every canonical result of the operation.
-- ALIGN: COALITION-FORWARD-OWNED-ACTION.
{-@ withMappedCoalitionAction
      :: sourceOwner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> (forall o f. owner:Atlas ta ts td o f
            -> ({source:CoalitionData sa ss sd | MappedCoalitionValid sourceOwner source}
                 -> {target:CoalitionData ta ts td | MappedCoalitionValid owner target})
            -> result)
      -> result @-}
withMappedCoalitionAction
  :: Atlas sa ss sd so sf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (forall o f. Atlas ta ts td o f
        -> (CoalitionData sa ss sd -> CoalitionData ta ts td) -> result)
  -> result
withMappedCoalitionAction sourceOwner transversal useAction =
  withAtlasTransversalCoveredAction sourceOwner transversal
    (\owner forward -> useAction owner (mapCanonicalCoalition sourceOwner owner forward))

-- | Map and canonicalize using the Atlas retained by the transversal. The
-- callback receives a valid canonical coalition for that exact target owner.
-- ALIGN: COALITION-FORWARD-OWNED-ELIMINATION.
{-@ withMappedCoalitionElement
      :: sourceOwner:Atlas sa ss sd so sf
      -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
      -> source:{CoalitionData sa ss sd | MappedCoalitionValid sourceOwner source}
      -> (forall o f. owner:Atlas ta ts td o f
            -> {element:CoalitionData ta ts td | MappedCoalitionValid owner element}
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
