{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif CoalitionAccepted(v:@(0), accepts:func(0, [@(0); bool])) { accepts v } @-}
{-@ qualif CoalitionOrigin(v:@(0), key:func(0, [@(0); (PageElements.Structure.SomePageElement @(1))]),
      selected:(PageElements.Structure.SomePageElement @(1))) { key v == selected } @-}

-- | Checked coalition-dependent assembly for Dominion inclusion.
module DomanialInclusion.LiquidInternal
  ( coalitionComponentInsertion, onePageCoverage, dominionCoverage, dominionAtlasMap
  , dominionCoalitionElement, coalitionValue, dominionCoalitionUnit
  , dominionCoalitionReconstruct, dominionCoalitionCounit
  , coaDomIncIso, coaDomIncIsoLeftInverse, coaDomIncIsoRightInverse ) where

import Atlas
  ( Atlas, atlasFolio, atlasPageElements, atlasAcceptsDatum
  , atlasNormalizationAgrees, atlasNormalizationArrow, atlasCoherenceWitness )
import AtlasCoveredPageElement
  ( CoverageWitness, atlasCoverageWitness, coverageWitnessCovers, coverageWitnessAlongArrow )
import AtlasExtent (cellTraceValid)
import AtlasMap (AtlasMap, atlasMap)
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches, coalitionElement
  , coalitionUnitInsertion, coalitionCounitInsertion
  , coalitionElementExtensionality, coalitionViewSource, coalitionElementViewSource
  , CoalitionView (..), viewCoalitionElement, coalitionElementView, coalitionElementValid, coalitionElementSource )
import DomanialInsertion.Core (DomanialInsertion (..), domanialInsertion, composeInsertions)
import DomanialInclusion.Data (DominionCellData, dominionCellProjection, dominionCellData, dominionCellDataValue, dominionCellDataReconstruct)
import DomanialInclusion.Presentation
  ( DominionAtlas, DominionAtlasObject, DominionPaginationScope, dominionAtlas, dominionAcceptsDatum )
import Folio (folioLength)
import PageElements (PageElement, normalizePageElement, withPageElement, originPageElement)
import PageElements.Structure (SomePageElement (..), pageElementPage)
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | On a one-page Atlas the normalized source is already a final region.
-- Coverage transports back to the original occurrence through coherence.
-- ALIGN: DOMINC-ONE-PAGE-COVERAGE.
{-@ onePageCoverage :: owner:{Atlas a s d o f | folioLength (atlasFolio owner) == 1}
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> {witness:CoverageWitness a s d | coverageWitnessCovers owner source datum witness} @-}
onePageCoverage :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d
onePageCoverage owner source datum =
  atlasNormalizationAgrees owner source `seq`
  pageElementPage (normalizePageElement (atlasPageElements owner) source) `seq`
  let arrow = atlasNormalizationArrow owner source
      witness = atlasCoverageWitness owner source datum source datum ()
  in atlasCoherenceWitness owner source arrow datum `seq`
     coverageWitnessAlongArrow owner arrow datum witness `seq` witness

-- | The public owner supplies the one-page premise to the general coverage law.
-- ALIGN: DOMINC-COVERAGE.
{-@ dominionCoverage :: owner:{Atlas a (DominionPaginationScope value) (DominionCellData value) () () |
           folioLength (atlasFolio owner) == 1}
      -> source:{PageElement (DominionPaginationScope value) object | cellTraceValid owner source}
      -> datum:{DominionCellData value object | atlasAcceptsDatum owner source datum}
      -> {witness:CoverageWitness a (DominionPaginationScope value) (DominionCellData value) |
           coverageWitnessCovers owner source datum witness} @-}
dominionCoverage
  :: forall a owner object. Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
  -> PageElement (DominionPaginationScope a) object
  -> DominionCellData a object
  -> CoverageWitness owner (DominionPaginationScope a) (DominionCellData a)
dominionCoverage = onePageCoverage

-- ALIGN: DOMINC-OWNER-MAP.
{-@ dominionAtlasMap :: DominionAtlas owner a -> AtlasMap (DominionAtlasObject owner a) @-}
dominionAtlasMap :: forall a owner. DominionAtlas owner a -> AtlasMap (DominionAtlasObject owner a)
dominionAtlasMap owner =
  let valueAtlas = dominionAtlas owner
  in atlasMap valueAtlas (\source datum -> dominionCoverage valueAtlas source datum)

-- | Constant membership and one-page coverage justify the public constructor.
-- ALIGN: DOMINC-OWNER-COALITION.
-- ALIGN: DOMINC-COALITION-VALUE-ROUNDTRIP.
{-@ opaque-reflect dominionCoalitionElement @-}
{-@ dominionCoalitionElement :: owner:DominionAtlas ownerScope a -> value:a
      -> {element:CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           coalitionValue element == value
           && coalitionElementValid (dominionAtlas owner) element
           && coalitionElementSource element
                == originPageElement (atlasPageElements (dominionAtlas owner))} @-}
dominionCoalitionElement :: forall a owner. DominionAtlas owner a -> a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a)
dominionCoalitionElement owner value =
  let valueAtlas = dominionAtlas owner
  in withPageElement (originPageElement (atlasPageElements valueAtlas)) $ \origin ->
       dominionCoalitionElementAt owner origin value

{-@ dominionCoalitionElementAt :: owner:DominionAtlas ownerScope a
      -> source:{PageElement (DominionPaginationScope a) object |
           cellTraceValid (dominionAtlas owner) source
           && SomePageElement source == originPageElement (atlasPageElements (dominionAtlas owner))}
      -> value:a
      -> {element:CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           coalitionValue element == value
           && coalitionElementValid (dominionAtlas owner) element
           && coalitionElementSource element == SomePageElement source} @-}
dominionCoalitionElementAt :: forall a owner object. DominionAtlas owner a -> PageElement (DominionPaginationScope a) object -> a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a)
dominionCoalitionElementAt owner source value =
  let valueAtlas = dominionAtlas owner
      datum = dominionCellData value :: DominionCellData a object
  in dominionAcceptsDatum owner source datum `seq`
     let witness = dominionCoverage valueAtlas source datum
         element = coalitionElement valueAtlas source datum witness
     in coalitionValueConstructed valueAtlas source datum witness `seq` element

{-@ coalitionValueConstructed :: owner:Atlas a s (DominionCellData value) o f
      -> source:{PageElement s object | cellTraceValid owner source
           && SomePageElement source == originPageElement (atlasPageElements owner)}
      -> datum:{DominionCellData value object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s (DominionCellData value) |
           coverageWitnessCovers owner source datum witness}
      -> {coalitionValue (coalitionElement owner source datum witness) == dominionCellDataValue datum} @-}
coalitionValueConstructed :: Atlas a s (DominionCellData value) o f -> PageElement s object
  -> DominionCellData value object -> CoverageWitness a s (DominionCellData value) -> ()
coalitionValueConstructed owner source datum witness =
  coalitionElementView owner source datum witness

{-@ reflect coalitionValue @-}
coalitionValue :: CoalitionData owner scope (DominionCellData a) -> a
coalitionValue element = dominionViewValue (viewCoalitionElement element)

{-@ reflect dominionViewValue @-}
dominionViewValue :: CoalitionView scope (DominionCellData a) -> a
dominionViewValue (CoalitionView _ datum) = dominionCellDataValue datum

{-@ reflect dominionViewFrom @-}
dominionViewFrom :: SomePageElement scope -> a -> CoalitionView scope (DominionCellData a)
dominionViewFrom (SomePageElement source) value = CoalitionView source (dominionCellData value)

{-@ dominionViewReconstruct :: viewed:CoalitionView scope (DominionCellData a)
      -> {dominionViewFrom (coalitionViewSource viewed) (dominionViewValue viewed) == viewed} @-}
dominionViewReconstruct :: CoalitionView scope (DominionCellData a) -> ()
dominionViewReconstruct (CoalitionView _ datum) = dominionCellDataReconstruct datum

{-@ reflect coalitionValuePreimage @-}
coalitionValuePreimage :: CoalitionData owner scope (DominionCellData a) -> Maybe a
coalitionValuePreimage element = Just (coalitionValue element)

{-@ dominionCoalitionRoundTrip :: owner:DominionAtlas ownerScope a -> value:a
      -> {coalitionValuePreimage (dominionCoalitionElement owner value) == Just value} @-}
dominionCoalitionRoundTrip :: DominionAtlas owner a -> a -> ()
dominionCoalitionRoundTrip owner value = dominionCoalitionElement owner value `seq` ()

-- ALIGN: DOMINC-CHECKED-COALITION-UNIT.
{-@ dominionCoalitionUnit :: owner:DominionAtlas ownerScope a
      -> {insertion:DomanialInsertion a
           (DominionCoalition ownerScope a owner) |
           applyInsertion insertion == dominionCoalitionElement owner
           && preimage insertion == coalitionValuePreimage} @-}
dominionCoalitionUnit :: DominionAtlas owner a
  -> DomanialInsertion a (CoalitionData owner (DominionPaginationScope a) (DominionCellData a))
dominionCoalitionUnit owner =
  let valueAtlas = dominionAtlas owner
      origin = originPageElement (atlasPageElements valueAtlas)
  in coalitionUnitInsertion (coalitionElementValid valueAtlas) coalitionElementSource origin
       (dominionCoalitionElement owner) coalitionValuePreimage (dominionCoalitionRoundTrip owner)

{-@ predicate DominionCoalitionValid O E =
      coalitionElementValid (dominionAtlas O) E
      && coalitionElementSource E == originPageElement (atlasPageElements (dominionAtlas O)) @-}

{-@ type DominionCoalition ownerScope a O =
      {element:CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           DominionCoalitionValid O element} @-}

-- | Constant-data projection determines the whole canonical origin carrier.
-- ALIGN: DOMINC-COALITION-RECONSTRUCTION.
{-@ dominionCoalitionReconstruct :: owner:DominionAtlas ownerScope a
      -> element:{CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           DominionCoalitionValid owner element}
      -> {dominionCoalitionElement owner (coalitionValue element) == element} @-}
dominionCoalitionReconstruct :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> ()
dominionCoalitionReconstruct owner element =
  let valueAtlas = dominionAtlas owner
      rebuilt = dominionCoalitionElement owner (coalitionValue element)
  in coalitionElementViewSource element `seq`
     coalitionElementViewSource rebuilt `seq`
     dominionViewReconstruct (viewCoalitionElement element) `seq`
     dominionViewReconstruct (viewCoalitionElement rebuilt) `seq`
     coalitionElementExtensionality valueAtlas rebuilt element

{-@ reflect coalitionElementPreimage @-}
{-@ coalitionElementPreimage :: owner:DominionAtlas ownerScope a -> a
      -> Maybe (DominionCoalition ownerScope a owner) @-}
coalitionElementPreimage :: DominionAtlas owner a -> a
  -> Maybe (CoalitionData owner (DominionPaginationScope a) (DominionCellData a))
coalitionElementPreimage owner value = Just (dominionCoalitionElement owner value)

{-@ dominionCoalitionCounitRoundTrip :: owner:DominionAtlas ownerScope a
      -> element:{CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           DominionCoalitionValid owner element}
      -> {coalitionElementPreimage owner (coalitionValue element) == Just element} @-}
dominionCoalitionCounitRoundTrip :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> ()
dominionCoalitionCounitRoundTrip = dominionCoalitionReconstruct

-- ALIGN: DOMINC-CHECKED-COALITION-COUNIT.
{-@ dominionCoalitionCounit :: owner:DominionAtlas ownerScope a
      -> {insertion:DomanialInsertion
           (DominionCoalition ownerScope a owner) a |
           applyInsertion insertion == coalitionValue
           && preimage insertion == coalitionElementPreimage owner} @-}
dominionCoalitionCounit :: DominionAtlas owner a
  -> DomanialInsertion (CoalitionData owner (DominionPaginationScope a) (DominionCellData a)) a
dominionCoalitionCounit owner =
  let valueAtlas = dominionAtlas owner
      origin = originPageElement (atlasPageElements valueAtlas)
  in coalitionCounitInsertion (coalitionElementValid valueAtlas) coalitionElementSource origin
       coalitionValue (coalitionElementPreimage owner) (dominionCoalitionCounitRoundTrip owner)

-- | Both directions retain the canonical carrier and their exact functions.
-- ALIGN: DOMINC-COALITION-EQUIVALENCE.
{-@ opaque-reflect coaDomIncIso @-}
{-@ coaDomIncIso :: owner:DominionAtlas ownerScope a
      -> ({counit:DomanialInsertion
             (DominionCoalition ownerScope a owner) a |
             applyInsertion counit == coalitionValue && preimage counit == coalitionElementPreimage owner},
          {unit:DomanialInsertion a
             (DominionCoalition ownerScope a owner) |
             applyInsertion unit == dominionCoalitionElement owner && preimage unit == coalitionValuePreimage}) @-}
coaDomIncIso :: DominionAtlas owner a
  -> ( DomanialInsertion (CoalitionData owner (DominionPaginationScope a) (DominionCellData a)) a
     , DomanialInsertion a (CoalitionData owner (DominionPaginationScope a) (DominionCellData a)) )
coaDomIncIso owner = (dominionCoalitionCounit owner, dominionCoalitionUnit owner)

-- ALIGN: DOMINC-COALITION-LEFT-INVERSE.
{-@ coaDomIncIsoLeftInverse :: owner:DominionAtlas ownerScope a
      -> element:{CoalitionData ownerScope (DominionPaginationScope a) (DominionCellData a) |
           DominionCoalitionValid owner element}
      -> {preimage (fst (coaDomIncIso owner)) (applyInsertion (fst (coaDomIncIso owner)) element)
           == Just element} @-}
coaDomIncIsoLeftInverse :: DominionAtlas owner a
  -> CoalitionData owner (DominionPaginationScope a) (DominionCellData a) -> ()
coaDomIncIsoLeftInverse owner element = case coaDomIncIso owner of
  (counit, _) -> insertionLeftInverse counit element

-- ALIGN: DOMINC-COALITION-RIGHT-INVERSE.
{-@ coaDomIncIsoRightInverse :: owner:DominionAtlas ownerScope a -> value:a
      -> {preimage (snd (coaDomIncIso owner)) (applyInsertion (snd (coaDomIncIso owner)) value)
           == Just value} @-}
coaDomIncIsoRightInverse :: DominionAtlas owner a -> a -> ()
coaDomIncIsoRightInverse owner value = case coaDomIncIso owner of
  (_, unit) -> insertionLeftInverse unit value

-- | A coalition inverse is defined only on covered values. The component
-- inverse additionally handles arbitrary target data, including uncovered data.
{-@
coalitionComponentInsertion
  :: targetAtlas:Atlas atlasScope scope cellData origin final
  -> targetOccurrence:{PageElement scope object | cellTraceValid targetAtlas targetOccurrence}
  -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
       coalitionElementValid targetAtlas element
       && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
       && coalitionElementReaches element targetOccurrence})
  -> backward:(cellData object -> Maybe a)
  -> (value:a -> { backward (coalitionElementAt targetAtlas targetOccurrence
                              (forward value)) == Just value })
  -> DomanialInsertion (DominionCellData a sourceObject)
       ({datum:cellData object | atlasAcceptsDatum targetAtlas targetOccurrence datum})
@-}
-- ALIGN: DOMINC-COMPONENT-INVERSE.
coalitionComponentInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (cellData object -> Maybe a)
  -> (a -> ())
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
coalitionComponentInsertion targetAtlas targetOccurrence forward backward leftInverse =
  coalitionComponentInsertionOn (atlasAcceptsDatum targetAtlas targetOccurrence)
    (coalitionComponentMap targetAtlas targetOccurrence forward) backward
    (coalitionComponentRoundTrip targetAtlas targetOccurrence forward backward leftInverse)

-- | Keep target membership explicit while composing the constant-cell projection.
{-@ coalitionComponentInsertionOn :: accepts:(b -> Bool)
      -> forward:(a -> {datum:b | accepts datum})
      -> backward:(b -> Maybe a)
      -> (value:a -> {backward (forward value) == Just value})
      -> DomanialInsertion (DominionCellData a object) ({datum:b | accepts datum}) @-}
coalitionComponentInsertionOn :: (b -> Bool) -> (a -> b) -> (b -> Maybe a) -> (a -> ())
  -> DomanialInsertion (DominionCellData a object) b
coalitionComponentInsertionOn _ forward backward leftInverse =
  composeInsertions (domanialInsertion forward backward leftInverse) dominionCellProjection

{-@ reflect coalitionComponentMap @-}
{-@ coalitionComponentMap :: targetAtlas:Atlas atlasScope scope cellData origin final
      -> targetOccurrence:{PageElement scope object | cellTraceValid targetAtlas targetOccurrence}
      -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element targetOccurrence})
      -> a -> {datum:cellData object | atlasAcceptsDatum targetAtlas targetOccurrence datum} @-}
coalitionComponentMap
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionData atlasScope scope cellData)
  -> a -> cellData object
coalitionComponentMap targetAtlas targetOccurrence forward value =
  coalitionElementAt targetAtlas targetOccurrence (forward value)

{-@ coalitionComponentRoundTrip
      :: targetAtlas:Atlas atlasScope scope cellData origin final
      -> targetOccurrence:{PageElement scope object | cellTraceValid targetAtlas targetOccurrence}
      -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element targetOccurrence})
      -> backward:(cellData object -> Maybe a)
      -> (value:a -> {backward (coalitionElementAt targetAtlas targetOccurrence (forward value)) == Just value})
      -> value:a
      -> {backward (coalitionComponentMap targetAtlas targetOccurrence forward value) == Just value} @-}
coalitionComponentRoundTrip
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (cellData object -> Maybe a)
  -> (a -> ()) -> a -> ()
coalitionComponentRoundTrip _ _ _ _ leftInverse value = leftInverse value
