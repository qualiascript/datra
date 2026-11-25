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
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElementView
  , coalitionViewSource
  , coalitionElementViewSource
  , coalitionElement
  , coalitionElementEliminate
  , coalitionElementWitnessIndependent
  , coalitionElementExtensionality
  , coalitionElementRank
  , coalitionElementSource
  , coalitionElementValid
  , withCoalitionElement
  , withCoalitionElementOf
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  ) where

import Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElementRank
  , coalitionElementSource
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , mapCoalitionElement
  )

import qualified Coalition.Element.Internal as Internal (CoalitionData (..), coalitionElement)
import Atlas (Atlas, atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, coverageWitnessOriginRank
  , coverageWitnessRankMatches, atlasOriginImageRank )
import Charter.Data
  ( ChartedDatum, chartCellData, chartedCellDataValue, chartedDatumValid, chartedCellCoverage
  , chartedCellDataEqual )
import Numeric.Natural (Natural)
import PageElements (PageElement, originPageElement)
import PageElements.Structure (SomePageElement (..))

{-@ reflect Internal.coalitionElement @-}
{-@ reflect withCoalitionElement @-}
{-@ reflect viewCoalitionElement @-}
{-@ reflect coalitionElementRank @-}
{-@ reflect coalitionElementSource @-}

-- | Validate the canonical code and cached rank of the stored origin datum.
{-@ reflect coalitionElementValid @-}
coalitionElementValid :: Atlas a s d o f -> CoalitionData a s d -> Bool
coalitionElementValid owner (Internal.CoalitionElement source datum originRank) =
  if chartedDatumValid owner source datum
    then originRank == atlasOriginImageRank owner source (chartedCellDataValue datum)
    else False

{-@ predicate CoalitionValid A E =
      coalitionElementValid A E
      && coalitionElementSource E == originPageElement (atlasPageElements A) @-}

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
  coverageWitnessRankMatches owner source datum witness `seq`
    Internal.coalitionElement source (chartCellData owner source datum witness ())
      (coverageWitnessOriginRank witness)

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
coalitionElementEliminate owner source datum witness _ =
  chartCellData owner source datum witness () `seq` ()

-- | The first-order view retains the dependent constructor payload.
-- ALIGN: COALITION-CONSTRUCTOR-VIEW.
{-@ coalitionElementView :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {viewCoalitionElement (coalitionElement owner source datum witness) == CoalitionView source datum} @-}
coalitionElementView :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> ()
coalitionElementView owner source datum witness = chartCellData owner source datum witness () `seq` ()

-- | Recovered coverage reconstructs the same canonical datum and rank cache.
-- ALIGN: COALITION-CANONICAL-RECONSTRUCTION.
{-@ coalitionElementReconstruct :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{ChartedDatum a s d object | chartedDatumValid owner source datum}
      -> originRank:{Natural | originRank == atlasOriginImageRank owner source (chartedCellDataValue datum)}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source (chartedCellDataValue datum) witness}
      -> {coalitionElement owner source (chartedCellDataValue datum) witness
           == Internal.coalitionElement source datum originRank} @-}
coalitionElementReconstruct :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object
  -> Natural -> CoverageWitness a s d -> ()
coalitionElementReconstruct owner source datum _ witness =
  let value = chartedCellDataValue datum
  in coverageWitnessRankMatches owner source value witness `seq`
     chartedCellDataEqual owner source datum (chartCellData owner source value witness ())

-- | Coverage choices do not distinguish canonical coalition values.
-- ALIGN: COALITION-WITNESS-INDEPENDENT.
{-@ coalitionElementWitnessIndependent :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> first:{CoverageWitness a s d | coverageWitnessCovers owner source datum first}
      -> second:{CoverageWitness a s d | coverageWitnessCovers owner source datum second}
      -> {coalitionElement owner source datum first == coalitionElement owner source datum second} @-}
coalitionElementWitnessIndependent :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> CoverageWitness a s d -> ()
coalitionElementWitnessIndependent owner source datum first second =
  coverageWitnessRankMatches owner source datum first `seq`
  coverageWitnessRankMatches owner source datum second `seq`
  chartedCellDataEqual owner source (chartCellData owner source datum first ())
    (chartCellData owner source datum second ())

-- | Observe the source without exposing the dependent datum.
{-@ reflect coalitionViewSource @-}
coalitionViewSource :: CoalitionView s d -> SomePageElement s
coalitionViewSource (CoalitionView source _) = SomePageElement source

-- ALIGN: COALITION-VIEW-SOURCE.
{-@ coalitionElementViewSource :: element:CoalitionData a s d
      -> {coalitionViewSource (viewCoalitionElement element) == coalitionElementSource element} @-}
coalitionElementViewSource :: CoalitionData a s d -> ()
coalitionElementViewSource (Internal.CoalitionElement _ _ _) = ()

{-@ reflect coalitionViewCovered @-}
coalitionViewCovered :: Atlas a s d o f -> CoalitionView s d -> CoverageWitness a s d -> Bool
coalitionViewCovered owner (CoalitionView source datum) witness =
  if cellTraceValid owner source then
    if atlasAcceptsDatum owner source datum then
      coverageWitnessCovers owner source datum witness
    else False
  else False

{-@ reflect rebuildCoalitionView @-}
{-@ rebuildCoalitionView :: owner:Atlas a s d o f
      -> viewed:{CoalitionView s d | coalitionViewSource viewed == originPageElement (atlasPageElements owner)}
      -> witness:{CoverageWitness a s d | coalitionViewCovered owner viewed witness}
      -> {element:CoalitionData a s d | CoalitionValid owner element
           && viewCoalitionElement element == viewed} @-}
rebuildCoalitionView :: Atlas a s d o f -> CoalitionView s d -> CoverageWitness a s d -> CoalitionData a s d
rebuildCoalitionView owner (CoalitionView source datum) witness =
  coalitionElementView owner source datum witness `seq` coalitionElement owner source datum witness

{-@ coalitionViewWitnessIndependent :: owner:Atlas a s d o f
      -> viewed:{CoalitionView s d | coalitionViewSource viewed == originPageElement (atlasPageElements owner)}
      -> first:{CoverageWitness a s d | coalitionViewCovered owner viewed first}
      -> second:{CoverageWitness a s d | coalitionViewCovered owner viewed second}
      -> {rebuildCoalitionView owner viewed first == rebuildCoalitionView owner viewed second} @-}
coalitionViewWitnessIndependent :: Atlas a s d o f -> CoalitionView s d
  -> CoverageWitness a s d -> CoverageWitness a s d -> ()
coalitionViewWitnessIndependent owner (CoalitionView source datum) first second =
  coalitionElementWitnessIndependent owner source datum first second

-- | Equal views reconstruct the same canonical carrier by witness independence.
-- ALIGN: COALITION-VIEW-EXTENSIONALITY.
{-@ coalitionElementExtensionality :: owner:Atlas a s d o f
      -> left:{CoalitionData a s d | CoalitionValid owner left}
      -> right:{CoalitionData a s d | CoalitionValid owner right
           && viewCoalitionElement right == viewCoalitionElement left}
      -> {left == right} @-}
coalitionElementExtensionality :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d -> ()
coalitionElementExtensionality owner
    (Internal.CoalitionElement leftSource leftData leftRank)
    (Internal.CoalitionElement rightSource rightData rightRank) =
  let leftDatum = chartedCellDataValue leftData
      rightDatum = chartedCellDataValue rightData
      leftView = CoalitionView leftSource leftDatum
      rightView = CoalitionView rightSource rightDatum
      leftWitness = chartedCellCoverage owner leftSource leftData
      rightWitness = chartedCellCoverage owner rightSource rightData
  in coalitionElementReconstruct owner leftSource leftData leftRank leftWitness `seq`
     coalitionElementReconstruct owner rightSource rightData rightRank rightWitness `seq`
     coalitionElementView owner leftSource leftDatum leftWitness `seq`
     coalitionElementView owner rightSource rightDatum rightWitness `seq`
     rebuildCoalitionView owner leftView leftWitness `seq`
     rebuildCoalitionView owner rightView rightWitness `seq`
     coalitionViewWitnessIndependent owner leftView leftWitness rightWitness

-- | Expose the origin, accepted datum, and coverage through the owning Atlas.
-- ALIGN: COALITION-CERTIFIED-ELIM.
{-@ withCoalitionElementOf :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
                && SomePageElement source == originPageElement (atlasPageElements owner)}
           -> datum:{d object | atlasAcceptsDatum owner source datum}
           -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness
                && coverageWitnessOriginRank witness == coalitionElementRank element
                && element == coalitionElement owner source datum witness}
           -> result)
      -> result @-}
withCoalitionElementOf :: Atlas a s d o f -> CoalitionData a s d
  -> (forall object. PageElement s object -> d object -> CoverageWitness a s d -> result) -> result
withCoalitionElementOf owner (Internal.CoalitionElement source datum originRank) useElement =
  let value = chartedCellDataValue datum
      witness = chartedCellCoverage owner source datum
  in coverageWitnessRankMatches owner source value witness `seq`
     coalitionElementReconstruct owner source datum originRank witness `seq`
     useElement source value witness
