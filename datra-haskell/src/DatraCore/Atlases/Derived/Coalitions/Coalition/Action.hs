{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked coalition actions retain the mapped image's certifying owner.
module Coalition.Action (withMappedCoalitionElement) where

import Atlas (Atlas, AtlasObject, atlasPageElements)
import AtlasCoveredPageElement (CoveredPageElement, coveredPageElementValid)
import AtlasTransversal (AtlasTransversal, withAtlasTransversalCoveredImage)
import Coalition.Element.Data
  ( CoalitionData, coalitionCoveredElement, coalitionFromCovered
  , coalitionElementValid, coalitionElementSource )
import PageElements (originPageElement)

{-@ predicate MappedCoalitionValid A E = coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}

{-@ canonicalizeCoalitionImage
      :: (forall o f. owner:Atlas a s d o f
            -> {element:CoalitionData a s d | MappedCoalitionValid owner element}
            -> result)
      -> owner:Atlas a s d origin final
      -> {image:CoveredPageElement a s d | coveredPageElementValid owner image}
      -> result @-}
canonicalizeCoalitionImage
  :: (forall o f. Atlas a s d o f -> CoalitionData a s d -> result)
  -> Atlas a s d origin final -> CoveredPageElement a s d -> result
canonicalizeCoalitionImage useElement owner image =
  useElement owner (coalitionFromCovered owner image)

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
  withAtlasTransversalCoveredImage sourceOwner transversal
    (coalitionCoveredElement sourceOwner source) (canonicalizeCoalitionImage useElement)
