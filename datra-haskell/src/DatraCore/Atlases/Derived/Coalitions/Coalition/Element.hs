{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Coalition values and their dependent elimination and transversal action.
-- The constructor stays private so callers cannot pair arbitrary data with
-- unrelated coverage evidence.
module Coalition.Element
  ( CoalitionElement
  , coalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  ) where

import Coalition.Element.Internal
  ( CoalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  )

import qualified Coalition.Element.Internal as Internal (coalitionElement)
import Atlas (Atlas, AtlasObject, atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (AtlasCoverageWitness, coverageWitnessCovers)
import PageElements (PageElement, originPageElement)
import PageElements.Structure (SomePageElement (..))

-- | Introduce an origin datum with coverage checked for that exact datum.
-- ALIGN: COALITION-CHECKED-CONSTRUCTOR.
{-@ coalitionElement :: owner:Atlas a s d o f
      -> origin:{PageElement s object | cellTraceValid owner origin
           && SomePageElement origin == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner origin datum}
      -> witness:{AtlasCoverageWitness (AtlasObject a s d) |
           coverageWitnessCovers owner origin datum witness}
      -> CoalitionElement (AtlasObject a s d) @-}
coalitionElement
  :: Atlas a s d o f -> PageElement s object -> d object
  -> AtlasCoverageWitness (AtlasObject a s d) -> CoalitionElement (AtlasObject a s d)
coalitionElement _ = Internal.coalitionElement
