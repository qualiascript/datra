{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif CoalitionAccepted(v:@(0), accepts:func(0, [@(0); bool])) { accepts v } @-}
{-@ qualif CoalitionOrigin(v:@(0), key:func(0, [@(0); (PageElements.Structure.SomePageElement @(1))]),
      selected:(PageElements.Structure.SomePageElement @(1))) { key v == selected } @-}

-- | Checked coalition carriers, canonicalization, and dependent elimination.
-- The constructor stays private so callers cannot pair arbitrary data with
-- unrelated coverage evidence.
module Coalition.Element.Data
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
  ) where

import Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElementRank
  , coalitionElementCode
  , coalitionElementSource
  , withCoalitionElement
  )

import qualified Coalition.Element.Internal as Internal (CoalitionData (..), coalitionElement)
import Atlas (Atlas, atlasPageElements, atlasAcceptsDatum, mapAtlasData)
import AtlasExtent (cellTraceValid, cellTraceHasOrigin, cellOriginRankMap)
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, coverageWitnessOriginRank
  , coverageWitnessRankMatches, atlasOriginImageRank, coverageWitnessTransport
  , CoveredPageElement, atlasCoveredByWitness, coveredPageElementValid
  , coveredPageElementSource, withAtlasCoveredPageElementOf, atlasCoveredPageElementWitness
  , coverageRankCanonicalSameOrigin, coverageRankCanonicalUnique )
import Charter.Data
  ( ChartedDatum, chartCellData, chartedCellDataValue, chartedDatumValid, chartedCellCoverage
  , chartedCellDataEqual, chartedCellDataRank, chartedUnrank, chartedRankRoundTrip )
import Dominion (Dominion, dominion, rank, unrank)
import DomanialInsertion (applyInsertion)
import Numeric.Natural (Natural)
import PageElements (PageElement, originPageElement, somePageElementTraceValid
  , pageElementArrow, somePageElementPrecedes, somePageElementTransported)
import PageElements.Structure (SomePageElement (..))

{-@ reflect Internal.coalitionElement @-}
{-@ reflect withCoalitionElement @-}
{-@ reflect viewCoalitionElement @-}
{-@ reflect coalitionElementRank @-}
{-@ reflect coalitionElementCode @-}
{-@ reflect coalitionElementSource @-}
{-@ opaque-reflect rank @-}
{-@ opaque-reflect unrank @-}

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

-- | Recover the exact covered source through Charter's checked witness interface.
-- ALIGN: COALITION-COVERED-CARRIER.
{-@ opaque-reflect coalitionCoveredElement @-}
{-@ coalitionCoveredElement :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {covered:CoveredPageElement a s d | coveredPageElementValid owner covered
           && coveredPageElementSource covered == coalitionElementSource element
           && coverageWitnessOriginRank (atlasCoveredPageElementWitness covered) == coalitionElementRank element} @-}
coalitionCoveredElement :: Atlas a s d o f -> CoalitionData a s d -> CoveredPageElement a s d
coalitionCoveredElement owner (Internal.CoalitionElement source datum _) =
  let value = chartedCellDataValue datum
      witness = chartedCellCoverage owner source datum
  in coverageWitnessRankMatches owner source value witness `seq`
     atlasCoveredByWitness owner source value witness

-- | Canonicalize covered data at the owning origin, retaining its checked witness.
-- ALIGN: COALITION-FROM-COVERED.
{-@ opaque-reflect coalitionFromCovered @-}
{-@ coalitionFromCovered :: owner:Atlas a s d o f
      -> covered:{CoveredPageElement a s d | coveredPageElementValid owner covered}
      -> {element:CoalitionData a s d | CoalitionValid owner element
           && coalitionElementRank element == coverageWitnessOriginRank (atlasCoveredPageElementWitness covered)} @-}
coalitionFromCovered :: Atlas a s d o f -> CoveredPageElement a s d -> CoalitionData a s d
coalitionFromCovered owner covered =
  case originPageElement (atlasPageElements owner) of
    SomePageElement origin ->
      withAtlasCoveredPageElementOf owner covered $ \source datum witness ->
        cellTraceHasOrigin owner source `seq`
        let arrow = pageElementArrow source origin
            mapped = applyInsertion (mapAtlasData owner arrow) datum
        in coverageWitnessTransport owner arrow datum witness `seq`
           coalitionElement owner origin mapped witness

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

-- | The stored source must have an actual page-element arrow to the target.
-- ALIGN: COALITION-TRANSPORT-ARROW.
{-@ reflect coalitionElementReaches @-}
coalitionElementReaches :: CoalitionData a s d -> PageElement s object -> Bool
coalitionElementReaches element target =
  somePageElementPrecedes (coalitionElementSource element) (SomePageElement target)
    && somePageElementTransported (coalitionElementSource element) (SomePageElement target)

-- | Transport the dependent datum along a certified arrow in its owning Atlas.
-- ALIGN: COALITION-DATUM-TRANSPORT.
-- ALIGN: COALITION-DATUM-RANK.
{-@ reflect coalitionElementAt @-}
{-@ coalitionElementAt :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | CoalitionValid owner element
           && coalitionElementReaches element target}
      -> {datum:d object | atlasAcceptsDatum owner target datum
           && atlasOriginImageRank owner target datum == coalitionElementRank element} @-}
coalitionElementAt :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d -> d object
coalitionElementAt owner target (Internal.CoalitionElement source datum _) =
  let arrow = pageElementArrow source target
      value = chartedCellDataValue datum
  in cellTraceHasOrigin owner source `seq`
     cellTraceHasOrigin owner target `seq`
     cellOriginRankMap owner arrow value `seq`
     applyInsertion (mapAtlasData owner arrow) value

-- | The original certified witness also covers the transported datum.
-- ALIGN: COALITION-COVERAGE-TRANSPORT.
{-@ coalitionElementCoverageAt :: owner:Atlas a s d o f
      -> target:{PageElement s object | cellTraceValid owner target}
      -> element:{CoalitionData a s d | CoalitionValid owner element
           && coalitionElementReaches element target}
      -> {witness:CoverageWitness a s d |
           coverageWitnessCovers owner target (coalitionElementAt owner target element) witness
           && coverageWitnessOriginRank witness == coalitionElementRank element} @-}
coalitionElementCoverageAt :: Atlas a s d o f -> PageElement s object -> CoalitionData a s d
  -> CoverageWitness a s d
coalitionElementCoverageAt owner target element@(Internal.CoalitionElement source datum _) =
  let value = chartedCellDataValue datum
      witness = chartedCellCoverage owner source datum
  in coverageWitnessRankMatches owner source value witness `seq`
     coverageWitnessTransport owner (pageElementArrow source target) value witness `seq`
     coalitionElementAt owner target element `seq` witness

-- | The shared canonical cache determines the coalition's origin-rank cache.
-- ALIGN: COALITION-FROM-CHARTED.
{-@ reflect coalitionFromCharted @-}
{-@ coalitionFromCharted :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{ChartedDatum a s d object | chartedDatumValid owner source datum}
      -> {element:CoalitionData a s d | CoalitionValid owner element
           && coalitionElementCode element == chartedCellDataRank datum} @-}
coalitionFromCharted :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object
  -> CoalitionData a s d
coalitionFromCharted owner source datum =
  Internal.coalitionElement source datum (atlasOriginImageRank owner source (chartedCellDataValue datum))

-- | Keep the chosen occurrence explicit until the dependent decoder has run.
{-@ reflect coalitionUnrankAt @-}
{-@ coalitionUnrankAt :: owner:Atlas a s d o f
      -> selected:{SomePageElement s |
           somePageElementTraceValid (atlasPageElements owner) selected
           && selected == originPageElement (atlasPageElements owner)}
      -> Natural -> Maybe ({element:CoalitionData a s d | CoalitionValid owner element}) @-}
coalitionUnrankAt :: Atlas a s d o f -> SomePageElement s -> Natural -> Maybe (CoalitionData a s d)
coalitionUnrankAt owner (SomePageElement source) candidate =
  case chartedUnrank owner source candidate of
    Nothing -> Nothing
    Just datum -> Just (coalitionFromCharted owner source datum)

-- | Decode a finite coverage candidate and retain the canonical origin carrier.
-- ALIGN: COALITION-DECODE.
-- ALIGN: COALITION-DECODE-VALUE.
{-@ reflect coalitionUnrank @-}
{-@ coalitionUnrank :: owner:Atlas a s d o f -> Natural
      -> Maybe ({element:CoalitionData a s d | CoalitionValid owner element}) @-}
coalitionUnrank :: Atlas a s d o f -> Natural -> Maybe (CoalitionData a s d)
coalitionUnrank owner candidate =
  coalitionUnrankAt owner (originPageElement (atlasPageElements owner)) candidate

-- | Charter's exact decoder law recovers the stored cache; validity recovers
-- the same origin-rank field, so the result is the original coalition record.
-- ALIGN: COALITION-ROUNDTRIP.
{-@ coalitionRankRoundTrip :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {coalitionUnrank owner (coalitionElementCode element) == Just element} @-}
coalitionRankRoundTrip :: Atlas a s d o f -> CoalitionData a s d -> ()
coalitionRankRoundTrip owner (Internal.CoalitionElement source datum _) =
  chartedRankRoundTrip owner source datum

-- | Equal origin ranks determine equal canonical codes and hence equal records.
-- ALIGN: COALITION-RANK-EXTENSIONALITY.
{-@ coalitionElementRankExtensionality :: owner:Atlas a s d o f
      -> left:{CoalitionData a s d | CoalitionValid owner left}
      -> right:{CoalitionData a s d | CoalitionValid owner right
           && coalitionElementRank right == coalitionElementRank left}
      -> {left == right} @-}
coalitionElementRankExtensionality :: Atlas a s d o f -> CoalitionData a s d -> CoalitionData a s d -> ()
coalitionElementRankExtensionality owner
    left@(Internal.CoalitionElement leftSource leftDatum _)
    right@(Internal.CoalitionElement rightSource rightDatum _) =
  let leftValue = chartedCellDataValue leftDatum
      rightValue = chartedCellDataValue rightDatum
      leftCode = chartedCellDataRank leftDatum
      rightCode = chartedCellDataRank rightDatum
  in coverageRankCanonicalSameOrigin owner leftSource leftValue rightSource rightValue leftCode `seq`
     coverageRankCanonicalUnique owner rightSource rightValue leftCode rightCode `seq`
     coalitionRankRoundTrip owner left `seq`
     coalitionRankRoundTrip owner right

-- | The covered-data round trip preserves the whole canonical carrier.
-- ALIGN: COALITION-FROM-COVERED-ROUNDTRIP.
{-@ coalitionFromCoveredRoundTrip :: owner:Atlas a s d o f
      -> element:{CoalitionData a s d | CoalitionValid owner element}
      -> {coalitionFromCovered owner (coalitionCoveredElement owner element) == element} @-}
coalitionFromCoveredRoundTrip :: Atlas a s d o f -> CoalitionData a s d -> ()
coalitionFromCoveredRoundTrip owner element =
  coalitionElementRankExtensionality owner
    (coalitionFromCovered owner (coalitionCoveredElement owner element)) element

{-@ coalitionDominionOn :: accepts:(value -> Bool)
      -> source:(value -> SomePageElement scope) -> origin:SomePageElement scope
      -> valueRank:({x:value | accepts x && source x == origin} -> Natural)
      -> valueAt:(Natural -> Maybe ({x:value | accepts x && source x == origin}))
      -> (x:{value | accepts x && source x == origin} -> {valueAt (valueRank x) == Just x})
      -> {result:Dominion ({x:value | accepts x && source x == origin}) |
           rank result == valueRank && unrank result == valueAt} @-}
coalitionDominionOn :: (value -> Bool) -> (value -> SomePageElement scope) -> SomePageElement scope
  -> (value -> Natural) -> (Natural -> Maybe value) -> (value -> ()) -> Dominion value
coalitionDominionOn _ _ _ = dominion

-- | The covered origin carrier, ranked by its canonical coverage code.
-- ALIGN: COALITION-CARRIER-EQUIVALENCE.
-- ALIGN: COALITION-DOMINION.
{-@ coalition :: owner:Atlas a s d o f
      -> {result:Dominion ({element:CoalitionData a s d | CoalitionValid owner element}) |
           rank result == coalitionElementCode && unrank result == coalitionUnrank owner} @-}
coalition :: Atlas a s d o f -> Dominion (CoalitionData a s d)
coalition owner =
  coalitionDominionOn (coalitionElementValid owner) coalitionElementSource
    (originPageElement (atlasPageElements owner)) coalitionElementCode
    (coalitionUnrank owner) (coalitionRankRoundTrip owner)
