{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Canonical coalition data retaining the value in the chained extent.
module ChainedDominionAtlas.Coalition
  ( chainedDominionCoalitionElement, chainedCoalitionValue, chainedCoalitionReconstruct
  , chainedCoalitionForward, chainedCoalitionBackward, chainedCoalitionInsertion ) where

import Atlas (atlasPageElements, atlasAcceptsDatum)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement (CoverageWitness, coverageWitnessCovers)
import ChainedDominionAtlas.Coverage (chainedDominionCoverage)
import ChainedDominionAtlas.Data (ChainedDominionCellData (..), cellValue)
import ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, chainedDominionAtlas, chainedDominionMembership )
import DomanialInsertion.Core (DomanialInsertion (..))
import Coalition.Element
  ( CoalitionData, CoalitionView (..), viewCoalitionElement, coalitionElement
  , coalitionElementView, coalitionElementSource, coalitionElementValid
  , withCoalitionElementOf, coalitionElementExtensionality, coalitionUnitInsertion )
import PageElements (PageElement, originPageElement, withPageElement)
import PageElements.Structure (SomePageElement (..))

-- ALIGN: CHAINED-COALITION-VALUE.
{-@ reflect chainedCoalitionValue @-}
chainedCoalitionValue :: CoalitionData owner scope (ChainedDominionCellData value) -> value
chainedCoalitionValue element = chainedViewValue (viewCoalitionElement element)

-- ALIGN: CHAINED-COALITION-VIEW-VALUE.
{-@ reflect chainedViewValue @-}
chainedViewValue :: CoalitionView scope (ChainedDominionCellData value) -> value
chainedViewValue (CoalitionView _ datum) = cellValue datum

-- ALIGN: CHAINED-COALITION-VIEW-FROM.
{-@ reflect chainedViewFrom @-}
chainedViewFrom :: SomePageElement scope -> value -> CoalitionView scope (ChainedDominionCellData value)
chainedViewFrom (SomePageElement source) value = CoalitionView source (ChainedDominionExtentDatum value)

-- | Valid coalition data is extent-tagged at the owning origin.
-- ALIGN: CHAINED-COALITION-ORIGIN-VIEW.
{-@ chainedCoalitionOriginView :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {viewCoalitionElement element == chainedViewFrom
           (originPageElement (atlasPageElements (chainedDominionAtlas owner))) (chainedCoalitionValue element)} @-}
chainedCoalitionOriginView :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> ()
chainedCoalitionOriginView owner element =
  let valueAtlas = chainedDominionAtlas owner
  in withCoalitionElementOf valueAtlas element $ \source datum witness ->
       chainedOriginViewAt owner element source datum witness

-- ALIGN: CHAINED-COALITION-ORIGIN-VIEW-AT.
{-@ chainedOriginViewAt :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:CoalitionData ownerScope scope (ChainedDominionCellData value)
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source
           && SomePageElement source == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> datum:{ChainedDominionCellData value object | atlasAcceptsDatum (chainedDominionAtlas owner) source datum}
      -> witness:{CoverageWitness ownerScope scope (ChainedDominionCellData value) |
           coverageWitnessCovers (chainedDominionAtlas owner) source datum witness
           && element == coalitionElement (chainedDominionAtlas owner) source datum witness}
      -> {viewCoalitionElement element == chainedViewFrom
           (originPageElement (atlasPageElements (chainedDominionAtlas owner))) (chainedCoalitionValue element)} @-}
chainedOriginViewAt :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> PageElement scope object
  -> ChainedDominionCellData value object -> CoverageWitness ownerScope scope (ChainedDominionCellData value) -> ()
chainedOriginViewAt owner _ source datum witness =
  coalitionElementView (chainedDominionAtlas owner) source datum witness `seq`
  chainedDominionMembership owner source datum `seq`
  case datum of
    ChainedDominionExtentDatum _ -> ()
    ChainedDominionRegionDatum _ -> ()

-- | The recovered value determines the entire canonical coalition, including
-- its coverage code and cached origin rank.
-- ALIGN: CHAINED-COALITION-RECONSTRUCTION.
{-@ chainedCoalitionReconstruct :: owner:ChainedDominionAtlas ownerScope scope value
      -> element:{CoalitionData ownerScope scope (ChainedDominionCellData value) |
           coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> {chainedDominionCoalitionElement owner (chainedCoalitionValue element) == element} @-}
chainedCoalitionReconstruct :: ChainedDominionAtlas ownerScope scope value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> ()
chainedCoalitionReconstruct owner element =
  let rebuilt = chainedDominionCoalitionElement owner (chainedCoalitionValue element)
  in chainedCoalitionOriginView owner element `seq`
     chainedCoalitionOriginView owner rebuilt `seq`
     coalitionElementExtensionality (chainedDominionAtlas owner) rebuilt element

-- ALIGN: CHAINED-OWNER-COALITION.
-- ALIGN: CHAINED-COALITION-VALUE-ROUNDTRIP.
{-@ opaque-reflect chainedDominionCoalitionElement @-}
{-@ chainedDominionCoalitionElement :: owner:ChainedDominionAtlas ownerScope scope value -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))} @-}
chainedDominionCoalitionElement :: ChainedDominionAtlas ownerScope scope value -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
chainedDominionCoalitionElement owner value =
  withPageElement (originPageElement (atlasPageElements (chainedDominionAtlas owner))) $ \origin ->
    chainedCoalitionAt owner origin value

-- ALIGN: CHAINED-COALITION-AT.
{-@ chainedCoalitionAt :: owner:ChainedDominionAtlas ownerScope scope value
      -> source:{PageElement scope object | cellTraceValid (chainedDominionAtlas owner) source
           && SomePageElement source == originPageElement (atlasPageElements (chainedDominionAtlas owner))}
      -> value:value
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == SomePageElement source} @-}
chainedCoalitionAt :: ChainedDominionAtlas ownerScope scope value -> PageElement scope object -> value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
chainedCoalitionAt owner source value =
  let valueAtlas = chainedDominionAtlas owner
      datum = ChainedDominionExtentDatum value
  in chainedDominionMembership owner source datum `seq`
     let witness = chainedDominionCoverage owner source datum
     in coalitionElementView valueAtlas source datum witness `seq`
        coalitionElement valueAtlas source datum witness

-- ALIGN: CHAINED-COALITION-FORWARD.
{-@ reflect chainedCoalitionForward @-}
{-@ chainedCoalitionForward :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
           chainedCoalitionValue element == applyInsertion insertion value
           && coalitionElementValid (chainedDominionAtlas owner) element
           && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))} @-}
chainedCoalitionForward :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value -> source
  -> CoalitionData ownerScope scope (ChainedDominionCellData value)
chainedCoalitionForward owner insertion value = chainedDominionCoalitionElement owner (applyInsertion insertion value)

-- ALIGN: CHAINED-COALITION-BACKWARD.
{-@ reflect chainedCoalitionBackward @-}
chainedCoalitionBackward :: DomanialInsertion source value
  -> CoalitionData ownerScope scope (ChainedDominionCellData value) -> Maybe source
chainedCoalitionBackward insertion element = preimage insertion (chainedCoalitionValue element)

-- ALIGN: CHAINED-COALITION-INSERTION-ROUNDTRIP.
{-@ chainedCoalitionRoundTrip :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value -> value:source
      -> {chainedCoalitionBackward insertion (chainedCoalitionForward owner insertion value) == Just value} @-}
chainedCoalitionRoundTrip :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value -> source -> ()
chainedCoalitionRoundTrip owner insertion value =
  chainedCoalitionForward owner insertion value `seq` insertionLeftInverse insertion value

-- ALIGN: CHAINED-COALITION-INSERTION.
{-@ chainedCoalitionInsertion :: owner:ChainedDominionAtlas ownerScope scope value
      -> insertion:DomanialInsertion source value
      -> {result:DomanialInsertion source
           ({element:CoalitionData ownerScope scope (ChainedDominionCellData value) |
             coalitionElementValid (chainedDominionAtlas owner) element
             && coalitionElementSource element == originPageElement (atlasPageElements (chainedDominionAtlas owner))}) |
           applyInsertion result == chainedCoalitionForward owner insertion
           && preimage result == chainedCoalitionBackward insertion} @-}
chainedCoalitionInsertion :: ChainedDominionAtlas ownerScope scope value -> DomanialInsertion source value
  -> DomanialInsertion source (CoalitionData ownerScope scope (ChainedDominionCellData value))
chainedCoalitionInsertion owner insertion =
  let valueAtlas = chainedDominionAtlas owner
  in coalitionUnitInsertion (coalitionElementValid valueAtlas) coalitionElementSource
       (originPageElement (atlasPageElements valueAtlas))
       (chainedCoalitionForward owner insertion) (chainedCoalitionBackward insertion)
       (chainedCoalitionRoundTrip owner insertion)
