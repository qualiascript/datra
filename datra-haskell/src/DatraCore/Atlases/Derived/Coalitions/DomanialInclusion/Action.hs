{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif ComponentAccepted(v:@(0), accepts:func(0, [@(0); bool])) { accepts v } @-}

-- | Checked constant object action for the coalition-to-inclusion construction.
module DomanialInclusion.Action
  ( OriginObjectMap, originObjectMap, constantObject, constantObjectPreservesArrow
  , constantComponentInsertion ) where

import Data.Kind (Type)
import Atlas
  ( Atlas, AtlasMappedObject, AtlasObjectMap, atlasObjectMap
  , atlasPageElements, normalizeAtlasElement, mapPrimitiveElement, atlasAcceptsDatum )
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches
  , coalitionElementValid, coalitionElementSource )
import DomanialInsertion.Core (DomanialInsertion (..), composePartialInverses)
import DomanialInclusion.Component (coalitionComponentInsertion, coalitionComponentMap, acceptDominionComponent, acceptedDominionPreimage)
import DomanialInclusion.Data (DominionCellData, dominionCellProjectionPreimage, domIncHomFromValue)
import DomanialInclusion.Presentation (DominionAtlas, DominionPaginationScope, dominionAtlas)
import PageElements (PageElement, pageElementTraceValid, originPageElement)
import PageElements.Structure
  ( SomePageElement (..), pageElementPage, pageElementPosition, pageElementTrace, pageElementCell
  , somePageElementPrecedes, somePageElementTransported
  , somePageElementPrecedesReflexive, somePageElementTransportedReflexive )

-- | The hidden target-origin cell is the image of every source object.
data OriginObjectMap (targetObject :: Type)

type instance AtlasMappedObject (OriginObjectMap targetObject) sourceObject = targetObject

originObjectMap :: AtlasObjectMap (OriginObjectMap targetObject)
originObjectMap = atlasObjectMap

-- ALIGN: DOMINC-CONSTANT-OBJECT.
{-@ reflect constantObject @-}
{-@ constantObject :: owner:Atlas a targetScope d o f
      -> target:{PageElement targetScope targetObject | pageElementTraceValid (atlasPageElements owner) target}
      -> PageElement sourceScope sourceObject
      -> {result:PageElement targetScope (AtlasMappedObject (OriginObjectMap targetObject) sourceObject) |
           pageElementTraceValid (atlasPageElements owner) result
           && pageElementPage result == pageElementPage target
           && pageElementPosition result == pageElementPosition target
           && pageElementTrace result == pageElementTrace target
           && pageElementCell result == pageElementCell target
           && SomePageElement result == SomePageElement target} @-}
constantObject :: Atlas a targetScope d o f -> PageElement targetScope targetObject
  -> PageElement sourceScope sourceObject
  -> PageElement targetScope (AtlasMappedObject (OriginObjectMap targetObject) sourceObject)
constantObject _ target _ = target

-- | Build at the mapped cell so both owning membership predicates are retained.
-- ALIGN: DOMINC-MAPPED-COMPONENT.
{-@ reflect constantComponentInsertion @-}
{-@ constantComponentInsertion :: witness:AtlasObjectMap objectMap
      -> sourceOwner:DominionAtlas owner a
      -> targetAtlas:Atlas atlasScope scope cellData origin final
      -> target:{PageElement scope targetObject | pageElementTraceValid (atlasPageElements targetAtlas) target}
      -> mapObject:(forall object. PageElement (DominionPaginationScope a) object
           -> {occurrence:PageElement scope (AtlasMappedObject objectMap object) |
                pageElementTraceValid (atlasPageElements targetAtlas) occurrence
                && SomePageElement occurrence == SomePageElement target})
      -> forward:(a -> {element:CoalitionData atlasScope scope cellData |
           coalitionElementValid targetAtlas element
           && coalitionElementSource element == originPageElement (atlasPageElements targetAtlas)
           && coalitionElementReaches element target})
      -> backward:(forall object. PageElement scope object -> cellData object -> Maybe a)
      -> leftInverse:(forall object. occurrence:{PageElement scope object |
           pageElementTraceValid (atlasPageElements targetAtlas) occurrence
           && SomePageElement occurrence == SomePageElement target}
           -> value:a -> {backward occurrence (coalitionElementAt targetAtlas occurrence (forward value)) == Just value})
      -> source:PageElement (DominionPaginationScope a) sourceObject
      -> {result:DomanialInsertion
           ({datum:DominionCellData a sourceObject | atlasAcceptsDatum (dominionAtlas sourceOwner) source datum})
           ({datum:cellData (AtlasMappedObject objectMap sourceObject) |
             atlasAcceptsDatum targetAtlas (mapObject source) datum}) |
           applyInsertion result == domIncHomFromValue
             (coalitionComponentMap targetAtlas (mapObject source) forward)
           && preimage result == acceptedDominionPreimage sourceOwner source
             (composePartialInverses dominionCellProjectionPreimage (backward (mapObject source)))} @-}
constantComponentInsertion :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> PageElement (DominionPaginationScope a) sourceObject
  -> DomanialInsertion (DominionCellData a sourceObject)
       (cellData (AtlasMappedObject objectMap sourceObject))
constantComponentInsertion _ sourceOwner targetAtlas _ mapObject forward backward leftInverse source =
  let mapped = mapObject source
  in acceptDominionComponent sourceOwner source (atlasAcceptsDatum targetAtlas mapped)
       (coalitionComponentInsertion targetAtlas mapped forward (backward mapped) (leftInverse mapped))

-- | A constant normalized object action sends every pair to one identity arrow.
-- ALIGN: DOMINC-CONSTANT-PAGE-LAW.
{-@ constantObjectPreservesArrow :: witness:AtlasObjectMap (OriginObjectMap targetObject)
      -> sourceAtlas:Atlas sa ss sd so sf
      -> targetAtlas:Atlas ta ts td to tf
      -> targetOccurrence:{PageElement ts targetObject |
           pageElementTraceValid (atlasPageElements targetAtlas) targetOccurrence}
      -> source:SomePageElement ss -> destination:SomePageElement ss
      -> {somePageElementPrecedes
            (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) source)
            (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) destination)
          && somePageElementTransported
            (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) source)
            (mapPrimitiveElement witness sourceAtlas targetAtlas (constantObject targetAtlas targetOccurrence) destination)} @-}
constantObjectPreservesArrow :: AtlasObjectMap (OriginObjectMap targetObject)
  -> Atlas sa ss sd so sf -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> SomePageElement ss -> SomePageElement ss -> ()
constantObjectPreservesArrow _ _ targetAtlas targetOccurrence
    (SomePageElement _) (SomePageElement _) =
  let normalized = SomePageElement (normalizeAtlasElement targetAtlas targetOccurrence)
  in somePageElementPrecedesReflexive normalized `seq`
       somePageElementTransportedReflexive normalized
