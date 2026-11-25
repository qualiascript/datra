{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Coalition values and their dependent elimination and transversal action.
-- The constructor stays private so callers cannot pair arbitrary data with
-- unrelated coverage evidence.
module Coalition.Element
  ( CoalitionElement
  , CoalitionData
  , coalitionElement
  , coalitionElementEliminate
  , coalitionElementRank
  , withCoalitionElement
  , withCoalitionElementOf
  , coalitionCoveredElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  ) where

import Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData
  , coalitionElementRank
  , withCoalitionElement
  , coalitionCoveredElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  )

import qualified Coalition.Element.Internal as Internal (CoalitionData (..), coalitionElement)
import Atlas (Atlas, atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, coverageWitnessOriginRank, atlasCoveredByWitness
  , coveredPageElementValid, coveredPageElementSource, withAtlasCoveredPageElementOf
  , atlasCoveredPageElementWitness )
import PageElements (PageElement, originPageElement)
import PageElements.Structure (SomePageElement (..))

{-@ reflect Internal.coalitionElement @-}
{-@ reflect atlasCoveredByWitness @-}
{-@ reflect withCoalitionElement @-}
{-@ reflect coalitionCoveredElement @-}
{-@ reflect coalitionElementRank @-}

{-@ predicate CoalitionValid A E =
      coveredPageElementValid A (coalitionCoveredElement E)
      && coveredPageElementSource (coalitionCoveredElement E)
           == originPageElement (atlasPageElements A) @-}

-- | Introduce an origin datum with coverage checked for that exact datum.
-- ALIGN: COALITION-CHECKED-CONSTRUCTOR.
{-@ reflect coalitionElement @-}
{-@ coalitionElement :: owner:Atlas a s d o f
      -> origin:{PageElement s object | cellTraceValid owner origin
           && SomePageElement origin == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner origin datum}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner origin datum witness}
      -> {element:CoalitionData a s d | CoalitionValid owner element
           && coalitionElementRank element == coverageWitnessOriginRank witness} @-}
coalitionElement
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoalitionData a s d
coalitionElement owner source datum witness =
  Internal.coalitionElement (atlasCoveredByWitness owner source datum witness)

-- | Elimination retains the exact source and datum supplied to construction.
-- ALIGN: COALITION-PUBLIC-CONSTRUCTOR-ELIM.
{-@ coalitionElementEliminate :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> useElement:(forall other. PageElement s other -> d other -> result)
      -> {withCoalitionElement (coalitionElement owner source datum witness) useElement
           == useElement source datum} @-}
coalitionElementEliminate :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
  -> (forall other. PageElement s other -> d other -> result) -> ()
coalitionElementEliminate _ _ _ _ _ = ()

-- | Expose the origin, accepted datum, and coverage through the owning Atlas.
-- ALIGN: COALITION-CERTIFIED-ELIM.
{-@ withCoalitionElementOf :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
                && SomePageElement source == originPageElement (atlasPageElements owner)}
           -> datum:{d object | atlasAcceptsDatum owner source datum}
           -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness
                && coverageWitnessOriginRank witness == coalitionElementRank element}
           -> result)
      -> result @-}
withCoalitionElementOf :: Atlas a s d o f -> CoalitionData a s d
  -> (forall object. PageElement s object -> d object -> CoverageWitness a s d -> result) -> result
withCoalitionElementOf owner (Internal.CoalitionElement covered) useElement =
  withAtlasCoveredPageElementOf owner covered
    (\source datum witness -> useElement source datum witness)
