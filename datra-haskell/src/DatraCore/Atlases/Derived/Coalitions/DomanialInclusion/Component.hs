{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}
{-@ qualif ComponentAccepted(v:@(0), accepts:func(0, [@(0); bool])) { accepts v } @-}

-- | Checked data components for the Dominion-inclusion hom correspondence.
module DomanialInclusion.Component
  ( coalitionComponentInsertion, coalitionComponentMap, constantComponentNaturality, acceptDominionComponent, acceptedDominionPreimage ) where

import Atlas
  ( Atlas, atlasPageElements, atlasAcceptsDatum, mapAtlasData, normalizeAtlasElement
  , normalizeAtlasElementTraceValid, atlasAcceptsDatumNormalized, atlasIdentityWitness )
import AtlasExtent (cellTraceValid)
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches
  , coalitionElementValid, coalitionElementSource )
import DomanialInsertion.Core (DomanialInsertion (..), domanialInsertion, insertionOn, composePartialInverses)
import DomanialInclusion.Data
  ( DominionCellData, dominionCellProjection, dominionCellProjectionPreimage, domIncHomFromValue
  , dominionCellDataValue, dominionCellDataReconstruct, identityCellMap )
import DomanialInclusion.Presentation
  ( DominionAtlas, DominionPaginationScope, dominionAtlas, dominionMapDataIdentity, dominionAcceptsDatum )
import PageElements (PageElement, originPageElement, pageElementTraceValid)
import PageElements.Structure
  ( PageElementArrow, arrowSource, arrowTarget, pageElementArrow, identityPageElementArrow )

-- | A constant component commutes with source transport and the target identity.
-- ALIGN: DOMINC-COMPONENT-NATURALITY.
{-@ constantComponentNaturality :: sourceOwner:DominionAtlas ownerScope a
      -> targetAtlas:Atlas atlasScope scope cellData origin final
      -> targetOccurrence:{PageElement scope object | cellTraceValid targetAtlas targetOccurrence}
      -> forward:(a -> {datum:cellData object | atlasAcceptsDatum targetAtlas targetOccurrence datum})
      -> sourceArrow:{PageElementArrow (DominionPaginationScope a) source target |
           pageElementTraceValid (atlasPageElements (dominionAtlas sourceOwner)) (arrowSource sourceArrow)
           && pageElementTraceValid (atlasPageElements (dominionAtlas sourceOwner)) (arrowTarget sourceArrow)}
      -> datum:DominionCellData a source
      -> {domIncHomFromValue forward
            (applyInsertion (mapAtlasData (dominionAtlas sourceOwner) sourceArrow) datum)
           == applyInsertion
                (mapAtlasData targetAtlas
                  (pageElementArrow (normalizeAtlasElement targetAtlas targetOccurrence)
                    (normalizeAtlasElement targetAtlas targetOccurrence)))
                (domIncHomFromValue forward datum)} @-}
constantComponentNaturality :: DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final -> PageElement scope object
  -> (a -> cellData object)
  -> PageElementArrow (DominionPaginationScope a) source target
  -> DominionCellData a source -> ()
constantComponentNaturality sourceOwner targetAtlas targetOccurrence forward sourceArrow datum =
  dominionMapDataIdentity sourceOwner sourceArrow `seq`
    dominionCellDataReconstruct (identityCellMap datum) `seq`
    dominionCellDataReconstruct datum `seq`
      normalizeAtlasElementTraceValid targetAtlas targetOccurrence `seq`
        atlasAcceptsDatumNormalized targetAtlas targetOccurrence
          (forward (dominionCellDataValue datum)) `seq`
          atlasIdentityWitness targetAtlas (normalizeAtlasElement targetAtlas targetOccurrence)
            (forward (dominionCellDataValue datum))

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
  -> {result:DomanialInsertion (DominionCellData a sourceObject)
       ({datum:cellData object | atlasAcceptsDatum targetAtlas targetOccurrence datum}) |
       applyInsertion result == domIncHomFromValue (coalitionComponentMap targetAtlas targetOccurrence forward)
       && preimage result == composePartialInverses dominionCellProjectionPreimage backward}
@-}
-- ALIGN: DOMINC-COMPONENT-INVERSE.
-- ALIGN: DOMINC-COMPONENT-FUNCTIONS.
-- ALIGN: DOMINC-COMPONENT-PREIMAGE.
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
      -> {result:DomanialInsertion (DominionCellData a object) ({datum:b | accepts datum}) |
           applyInsertion result == domIncHomFromValue forward
           && preimage result == composePartialInverses dominionCellProjectionPreimage backward} @-}
coalitionComponentInsertionOn :: (b -> Bool) -> (a -> b) -> (b -> Maybe a) -> (a -> ())
  -> DomanialInsertion (DominionCellData a object) b
coalitionComponentInsertionOn _ forward backward leftInverse =
  dominionCellProjection `seq`
  domanialInsertion (domIncHomFromValue forward)
    (composePartialInverses (preimage dominionCellProjection) backward)
    (coalitionComponentValueRoundTrip forward backward leftInverse)

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

{-@ coalitionComponentValueRoundTrip :: forward:(a -> b) -> backward:(b -> Maybe a)
      -> (value:a -> {backward (forward value) == Just value})
      -> datum:DominionCellData a object
      -> {composePartialInverses dominionCellProjectionPreimage backward
           (domIncHomFromValue forward datum) == Just datum} @-}
coalitionComponentValueRoundTrip :: (a -> b) -> (b -> Maybe a) -> (a -> ()) -> DominionCellData a object -> ()
coalitionComponentValueRoundTrip _ _ leftInverse datum =
  dominionCellProjection `seq`
  dominionCellDataReconstruct datum `seq`
  leftInverse (dominionCellDataValue datum)

-- | Restrict the constant source carrier while preserving both maps pointwise.
-- ALIGN: DOMINC-ACCEPTED-COMPONENT.
{-@ acceptDominionComponent :: owner:DominionAtlas ownerScope a
      -> source:PageElement (DominionPaginationScope a) object
      -> accepts:(b -> Bool)
      -> insertion:DomanialInsertion (DominionCellData a object) ({datum:b | accepts datum})
      -> {result:DomanialInsertion
           ({datum:DominionCellData a object | atlasAcceptsDatum (dominionAtlas owner) source datum}) ({datum:b | accepts datum}) |
           applyInsertion result == applyInsertion insertion
           && preimage result == acceptedDominionPreimage owner source (preimage insertion)} @-}
acceptDominionComponent :: DominionAtlas owner a
  -> PageElement (DominionPaginationScope a) object
  -> (b -> Bool) -> DomanialInsertion (DominionCellData a object) b
  -> DomanialInsertion (DominionCellData a object) b
acceptDominionComponent owner source accepts insertion =
  insertionOn (atlasAcceptsDatum (dominionAtlas owner) source) accepts
    (applyInsertion insertion)
    (acceptedDominionPreimage owner source (preimage insertion))
    (insertionLeftInverse insertion)

-- ALIGN: DOMINC-ACCEPTED-PREIMAGE.
{-@ reflect acceptedDominionPreimage @-}
{-@ acceptedDominionPreimage :: owner:DominionAtlas ownerScope a
      -> source:PageElement (DominionPaginationScope a) object
      -> backward:(b -> Maybe (DominionCellData a object))
      -> value:b
      -> {result:Maybe ({datum:DominionCellData a object | atlasAcceptsDatum (dominionAtlas owner) source datum}) |
           result == backward value} @-}
acceptedDominionPreimage :: DominionAtlas owner a
  -> PageElement (DominionPaginationScope a) object
  -> (b -> Maybe (DominionCellData a object)) -> b -> Maybe (DominionCellData a object)
acceptedDominionPreimage owner source backward value = case backward value of
  Nothing -> Nothing
  Just datum -> dominionAcceptsDatum owner source datum `seq` Just datum
