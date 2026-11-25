{-# LANGUAGE CPP #-}
-- LiquidHaskell retains the re-exported carrier contracts for public callers.
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Public coalition carriers, checked operations, and transversal action.
module Coalition.Element
  ( CoalitionElement
  , CoalitionData
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElementView
  , coalitionViewSource
  , coalitionElementViewSource
  , coalitionElement
  , coalitionElementEliminate
  , coalitionElementWitnessIndependent
  , coalitionElementExtensionality
  , coalitionElementRankExtensionality
  , coalitionElementRank
  , coalitionElementCode
  , coalitionElementSource
  , coalitionElementValid
  , withCoalitionElement
  , withCoalitionElementOf
  , coalitionElementReaches
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalitionCoveredElement
  , coalitionFromCovered
  , coalitionFromCoveredRoundTrip
  , coalition
  , coalitionUnrank
  , mapCoalitionElement
  , withMappedCoalitionElement
  ) where

import Coalition.Element.Data
import Coalition.Action (withMappedCoalitionElement)
import Coalition.Action.Internal (mapCoalitionElement)
