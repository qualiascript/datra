{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Assemble the inclusion morphism with its actual dependent components.
module DomanialInclusion.Morphism (coalitionMorphismAction) where

import Atlas
  ( Atlas, AtlasMorphismAction, AtlasObjectMap, AtlasMappedObject, atlasMorphismAction
  , atlasMorphismSource, atlasMorphismTarget, atlasMorphismObjectMapWitness
  , mapAtlasMorphismActionObject, mapAtlasMorphismActionComponent
  , atlasPageElements, atlasAcceptsDatum, mapAtlasData, normalizeAtlasElement
  , normalizeAtlasElementTraceValid, mapPrimitiveElement )
import Coalition.Element
  ( CoalitionData, coalitionElementAt, coalitionElementReaches, coalitionElementValid
  , coalitionElementSource, coalitionElementAlongArrow, coalitionElementAtNormalized )
import DomanialInsertion.Core (DomanialInsertion (..))
import DomanialInclusion.Action (constantComponentInsertion)
import DomanialInclusion.Component (coalitionComponentMap)
import DomanialInclusion.Data
  ( DominionCellData, dominionCellDataValue, dominionCellDataReconstruct, identityCellMap, domIncHomFromValue )
import DomanialInclusion.Presentation
  ( DominionAtlas, DominionPaginationScope, dominionAtlas, dominionMapDataIdentity, dominionAcceptsDatum )
import PageElements (PageElement, pageElementTraceValid, originPageElement)
import PageElements.Structure
  ( SomePageElement (..), PageElementArrow, arrowSource, arrowTarget, pageElementArrow
  , somePageElementPrecedes, somePageElementTransported )

-- ALIGN: DOMINC-MORPHISM-ASSEMBLY.
{-@ coalitionMorphismAction :: witness:AtlasObjectMap objectMap
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
      -> pageLaw:(sourceValue:SomePageElement (DominionPaginationScope a)
           -> targetValue:{SomePageElement (DominionPaginationScope a) |
                somePageElementPrecedes sourceValue targetValue
                && somePageElementTransported sourceValue targetValue}
           -> {somePageElementPrecedes
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)
               && somePageElementTransported
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)})
      -> {action:AtlasMorphismAction objectMap owner atlasScope (DominionPaginationScope a) scope
           (DominionCellData a) cellData () () origin final |
           atlasMorphismSource action == dominionAtlas sourceOwner
           && atlasMorphismTarget action == targetAtlas
           && atlasMorphismObjectMapWitness action == witness
           && mapAtlasMorphismActionObject action == mapObject
           && mapAtlasMorphismActionComponent action
                == constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse} @-}
coalitionMorphismAction :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> (SomePageElement (DominionPaginationScope a) -> SomePageElement (DominionPaginationScope a) -> ())
  -> AtlasMorphismAction objectMap owner atlasScope (DominionPaginationScope a) scope
       (DominionCellData a) cellData () () origin final
coalitionMorphismAction witness sourceOwner targetAtlas target mapObject forward backward leftInverse pageLaw =
  atlasMorphismAction witness (dominionAtlas sourceOwner) targetAtlas mapObject
    (constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse)
    pageLaw
    (constantMappedNaturality witness sourceOwner targetAtlas target mapObject forward backward leftInverse pageLaw)

-- | Expose the component equation at a datum before assembling naturality.
-- ALIGN: DOMINC-MAPPED-COMPONENT-VALUE.
{-@ constantComponentValue :: witness:AtlasObjectMap objectMap
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
      -> datum:DominionCellData a sourceObject
      -> {applyInsertion
            (constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse source) datum
           == coalitionElementAt targetAtlas (mapObject source) (forward (dominionCellDataValue datum))} @-}
constantComponentValue :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> PageElement (DominionPaginationScope a) sourceObject -> DominionCellData a sourceObject -> ()
constantComponentValue witness sourceOwner targetAtlas target mapObject forward backward leftInverse source datum =
  let mapped = mapObject source
  in dominionAcceptsDatum sourceOwner source datum `seq`
     constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse source `seq`
     dominionCellDataReconstruct datum `seq`
     domIncHomFromValue (coalitionComponentMap targetAtlas mapped forward) datum `seq`
     coalitionComponentMap targetAtlas mapped forward (dominionCellDataValue datum) `seq` ()

-- ALIGN: DOMINC-MAPPED-NATURALITY.
{-@ constantMappedNaturality :: witness:AtlasObjectMap objectMap
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
      -> pageLaw:(sourceValue:SomePageElement (DominionPaginationScope a)
           -> targetValue:{SomePageElement (DominionPaginationScope a) |
                somePageElementPrecedes sourceValue targetValue
                && somePageElementTransported sourceValue targetValue}
           -> {somePageElementPrecedes
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)
               && somePageElementTransported
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject sourceValue)
                 (mapPrimitiveElement witness (dominionAtlas sourceOwner) targetAtlas mapObject targetValue)})
      -> sourceArrow:{PageElementArrow (DominionPaginationScope a) sourceObject targetObject2 |
           pageElementTraceValid (atlasPageElements (dominionAtlas sourceOwner)) (arrowSource sourceArrow)
           && pageElementTraceValid (atlasPageElements (dominionAtlas sourceOwner)) (arrowTarget sourceArrow)}
      -> datum:DominionCellData a sourceObject
      -> {applyInsertion
            (constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse
              (normalizeAtlasElement (dominionAtlas sourceOwner) (arrowTarget sourceArrow)))
            (applyInsertion (mapAtlasData (dominionAtlas sourceOwner) sourceArrow) datum)
           == applyInsertion
                (mapAtlasData targetAtlas (pageElementArrow
                  (normalizeAtlasElement targetAtlas
                    (mapObject (normalizeAtlasElement (dominionAtlas sourceOwner) (arrowSource sourceArrow))))
                  (normalizeAtlasElement targetAtlas
                    (mapObject (normalizeAtlasElement (dominionAtlas sourceOwner) (arrowTarget sourceArrow))))))
                (applyInsertion
                  (constantComponentInsertion witness sourceOwner targetAtlas target mapObject forward backward leftInverse
                    (normalizeAtlasElement (dominionAtlas sourceOwner) (arrowSource sourceArrow))) datum)} @-}
constantMappedNaturality :: AtlasObjectMap objectMap
  -> DominionAtlas owner a
  -> Atlas atlasScope scope cellData origin final
  -> PageElement scope targetObject
  -> (forall object. PageElement (DominionPaginationScope a) object -> PageElement scope (AtlasMappedObject objectMap object))
  -> (a -> CoalitionData atlasScope scope cellData)
  -> (forall object. PageElement scope object -> cellData object -> Maybe a)
  -> (forall object. PageElement scope object -> a -> ())
  -> (SomePageElement (DominionPaginationScope a) -> SomePageElement (DominionPaginationScope a) -> ())
  -> PageElementArrow (DominionPaginationScope a) sourceObject targetObject2
  -> DominionCellData a sourceObject -> ()
constantMappedNaturality witness sourceOwner targetAtlas target mapObject forward backward leftInverse pageLaw sourceArrow datum =
  let sourceAtlas = dominionAtlas sourceOwner
      source = normalizeAtlasElement sourceAtlas (arrowSource sourceArrow)
      destination = normalizeAtlasElement sourceAtlas (arrowTarget sourceArrow)
      left = mapObject source
      right = mapObject destination
      element = forward (dominionCellDataValue datum)
  in pageLaw (SomePageElement (arrowSource sourceArrow)) (SomePageElement (arrowTarget sourceArrow)) `seq`
     normalizeAtlasElementTraceValid targetAtlas left `seq`
     normalizeAtlasElementTraceValid targetAtlas right `seq`
     constantComponentValue witness sourceOwner targetAtlas target mapObject forward backward leftInverse source datum `seq`
     constantComponentValue witness sourceOwner targetAtlas target mapObject forward backward leftInverse destination (identityCellMap datum) `seq`
     dominionMapDataIdentity sourceOwner sourceArrow `seq`
     dominionCellDataReconstruct (identityCellMap datum) `seq`
     dominionCellDataReconstruct datum `seq`
     coalitionElementAtNormalized targetAtlas left element `seq`
     coalitionElementAtNormalized targetAtlas right element `seq`
     coalitionElementAlongArrow targetAtlas
       (pageElementArrow (normalizeAtlasElement targetAtlas left) (normalizeAtlasElement targetAtlas right)) element
