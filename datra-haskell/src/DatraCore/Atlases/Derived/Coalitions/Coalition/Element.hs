{-# LANGUAGE CPP #-}
-- LiquidHaskell retains the carrier and action contracts, including the raw
-- mapper's canonical-source precondition, for callers of this public interface.
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
  , coalitionUnitInsertion, coalitionCounitInsertion
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
  , coalitionElementAlongArrow
  , coalitionElementAtNormalized
  , coalitionElementCoverageAt
  , coalitionCoveredElement
  , coalitionFromCovered
  , coalitionFromCoveredRoundTrip
  , coalition
  , coalitionUnrank
  , mapCoalitionElement
  , withMappedCoalitionElement
  , withMappedCoalitionAction
  ) where

import Coalition.Element.Data hiding (coalitionElementAlongArrow, coalitionElementAtNormalized)
import qualified Coalition.Element.Data as Data (coalitionElementAlongArrow, coalitionElementAtNormalized)
import Atlas (Atlas, atlasPageElements, mapAtlasData, normalizeAtlasElement)
import AtlasExtent (cellTraceValid)
import DomanialInsertion.Core (DomanialInsertion (..))
import PageElements (PageElement, originPageElement)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)
import Coalition.Action (mapCoalitionElement, withMappedCoalitionAction, withMappedCoalitionElement)

-- | Preserve the checked transport contract through the public interface.
{-@ coalitionElementAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> element:{CoalitionData a s d | coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element (arrowSource arrow)}
      -> {coalitionElementReaches element (arrowTarget arrow)
           && coalitionElementAt owner (arrowTarget arrow) element
             == applyInsertion (mapAtlasData owner arrow)
                  (coalitionElementAt owner (arrowSource arrow) element)} @-}
coalitionElementAlongArrow :: Atlas a s d o f -> PageElementArrow s source target
  -> CoalitionData a s d -> ()
coalitionElementAlongArrow = Data.coalitionElementAlongArrow

-- | Preserve the checked transport contract through the public interface.
{-@ coalitionElementAtNormalized :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | coalitionElementValid owner element
           && coalitionElementSource element == originPageElement (atlasPageElements owner)
           && coalitionElementReaches element target}
      -> {coalitionElementReaches element (normalizeAtlasElement owner target)
           && coalitionElementAt owner (normalizeAtlasElement owner target) element
                == coalitionElementAt owner target element} @-}
coalitionElementAtNormalized :: Atlas a s d o f -> PageElement s object
  -> CoalitionData a s d -> ()
coalitionElementAtNormalized = Data.coalitionElementAtNormalized
