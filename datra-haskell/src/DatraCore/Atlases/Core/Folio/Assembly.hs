{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif Accepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Shared origin and append operations retaining accepted page carriers.
module Folio.Assembly (collapseToOrigin, appendOrderedPage, extendPages, extendPagesLookup, extendPagesThroughLookup) where

import Chain.Internal (Chain, chainPosition)
import Chain.Order (chainPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedConsolidation)
import DatraOrdinal.Laws (ordinalLTIrreflexive)
import DatraOrdinal (Ordinal)
import Folio.Presentation (FolioData, appendPageData, folioLengthData, lastPageData)
import Numeric.Natural (Natural)
import PageElements.Internal (folioTraceLookup, appendedEarlierLookup)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: FOLIO-COLLAPSE-ORIGIN.
{-@ collapseToOrigin :: contains:(a -> Bool)
      -> source:Chain {cell:a | contains cell} -> target:Chain ()
      -> chosen:{a | contains chosen}
      -> {result:OrderedConsolidation {cell:a | contains cell} () |
           orderedSource result == source && orderedTarget result == target} @-}
collapseToOrigin :: (a -> Bool) -> Chain a -> Chain ()
  -> a -> OrderedConsolidation a ()
{-@ ple collapseToOrigin @-}
collapseToOrigin contains source target chosen =
  orderedConsolidation source target
    (restrictedConsolidation contains unitContains collapseValue (collapseChosen chosen)
      (collapseMonotone target) (collapseInverse chosen))

{-@ reflect unitContains @-}
unitContains :: () -> Bool
unitContains () = True

{-@ reflect collapseValue @-}
collapseValue :: a -> ()
collapseValue _ = ()

{-@ reflect collapseChosen @-}
collapseChosen :: a -> () -> a
collapseChosen chosen () = chosen

{-@ collapseInverse :: chosen:a -> value:() -> {collapseValue (collapseChosen chosen value) == value} @-}
{-@ ple collapseInverse @-}
collapseInverse :: a -> () -> ()
collapseInverse _ () = ()

{-@ collapseMonotone :: target:Chain () -> first:a -> mappedFirst:() -> second:a
      -> {result:() | result == collapseValue second && unitContains result && chainPrecedes target mappedFirst result} @-}
{-@ ple collapseMonotone @-}
collapseMonotone :: Chain () -> a -> () -> a -> ()
collapseMonotone target _ () _ = ordinalLTIrreflexive (chainPosition target ()) `seq` ()

-- ALIGN: FOLIO-APPEND-ACCEPTED.
{-@ reflect appendOrderedPage @-}
{-@ appendOrderedPage :: previousContains:(a -> Bool) -> nextContains:(b -> Bool)
      -> pages:FolioData origin {cell:a | previousContains cell}
      -> transition:{OrderedConsolidation {cell:b | nextContains cell} {cell:a | previousContains cell} |
           orderedTarget transition == lastPageData pages}
      -> {result:FolioData origin {cell:b | nextContains cell} |
           folioLengthData result == folioLengthData pages + 1 && lastPageData result == orderedSource transition} @-}
appendOrderedPage :: (a -> Bool) -> (b -> Bool)
  -> FolioData origin a -> OrderedConsolidation b a -> FolioData origin b
appendOrderedPage _ _ pages transition = appendPageData pages (orderedSource transition) transition

-- | Extend a certified prefix with a family of accepted pages and transitions.
-- ALIGN: FOLIO-EXTEND-PREFIX.
-- ALIGN: FOLIO-EXTEND-PREFIX-INTERPRETATION.
{-@ reflect extendPages @-}
{-@ extendPages :: contains:(Natural -> a -> Bool)
      -> position:(index:Natural -> {cell:a | contains index cell} -> Ordinal)
      -> next:(index:{Natural | index > 0}
           -> target:{Chain {cell:a | contains (index - 1) cell} |
                chainPosition target == position (index - 1)}
           -> {mapping:OrderedConsolidation {cell:a | contains index cell} {cell:a | contains (index - 1) cell} |
                chainPosition (orderedSource mapping) == position index && orderedTarget mapping == target})
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{FolioData origin {cell:a | contains (page - 1) cell} |
           chainPosition (lastPageData pages) == position (page - 1)}
      -> {result:FolioData origin {cell:a | contains (depth - 1) cell} |
           folioLengthData result == folioLengthData pages + depth - page
           && chainPosition (lastPageData result) == position (depth - 1)} / [depth - page] @-}
extendPages :: (Natural -> a -> Bool) -> (Natural -> a -> Ordinal)
  -> (Natural -> Chain a -> OrderedConsolidation a a)
  -> Natural -> Natural -> FolioData origin a -> FolioData origin a
extendPages contains position next page depth pages
  | page == depth = pages
  | otherwise =
      let transition = next page (lastPageData pages)
          extended = appendOrderedPage (contains (page - 1)) (contains page) pages transition
      in extendPages contains position next (page + 1) depth extended

-- ALIGN: FOLIO-EXTEND-LOOKUP-PRESERVED.
{-@ extendPagesLookup :: contains:(Natural -> a -> Bool)
      -> position:(index:Natural -> {cell:a | contains index cell} -> Ordinal)
      -> next:(index:{Natural | index > 0}
           -> target:{Chain {cell:a | contains (index - 1) cell} |
                chainPosition target == position (index - 1)}
           -> {mapping:OrderedConsolidation {cell:a | contains index cell} {cell:a | contains (index - 1) cell} |
                chainPosition (orderedSource mapping) == position index && orderedTarget mapping == target})
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{FolioData origin {cell:a | contains (page - 1) cell} |
           chainPosition (lastPageData pages) == position (page - 1)}
      -> index:{Natural | index < folioLengthData pages} -> ordinal:Ordinal
      -> {folioTraceLookup (extendPages contains position next page depth pages) index ordinal
           == folioTraceLookup pages index ordinal} / [depth - page] @-}
{-@ ple extendPagesLookup @-}
extendPagesLookup :: (Natural -> a -> Bool) -> (Natural -> a -> Ordinal)
  -> (Natural -> Chain a -> OrderedConsolidation a a)
  -> Natural -> Natural -> FolioData origin a -> Natural -> Ordinal -> ()
extendPagesLookup contains position next page depth pages index ordinal
  | page == depth = ()
  | otherwise =
      let transition = next page (lastPageData pages)
          extended = appendOrderedPage (contains (page - 1)) (contains page) pages transition
      in extendPagesLookup contains position next (page + 1) depth extended index ordinal `seq`
        appendedEarlierLookup pages (orderedSource transition) transition index ordinal

-- | Resolve an intermediate page through the prefix ending at that page.
-- ALIGN: FOLIO-EXTEND-INTERMEDIATE-LOOKUP.
{-@ extendPagesThroughLookup :: contains:(Natural -> a -> Bool)
      -> position:(index:Natural -> {cell:a | contains index cell} -> Ordinal)
      -> next:(index:{Natural | index > 0}
           -> target:{Chain {cell:a | contains (index - 1) cell} |
                chainPosition target == position (index - 1)}
           -> {mapping:OrderedConsolidation {cell:a | contains index cell} {cell:a | contains (index - 1) cell} |
                chainPosition (orderedSource mapping) == position index && orderedTarget mapping == target})
      -> page:{Natural | page > 0} -> middle:{Natural | page <= middle} -> depth:{Natural | middle <= depth}
      -> pages:{FolioData origin {cell:a | contains (page - 1) cell} |
           chainPosition (lastPageData pages) == position (page - 1)}
      -> index:{Natural | index < folioLengthData pages + middle - page} -> ordinal:Ordinal
      -> {folioTraceLookup (extendPages contains position next page depth pages) index ordinal
           == folioTraceLookup (extendPages contains position next page middle pages) index ordinal}
      / [middle - page] @-}
{-@ ple extendPagesThroughLookup @-}
extendPagesThroughLookup :: (Natural -> a -> Bool) -> (Natural -> a -> Ordinal)
  -> (Natural -> Chain a -> OrderedConsolidation a a)
  -> Natural -> Natural -> Natural -> FolioData origin a -> Natural -> Ordinal -> ()
extendPagesThroughLookup contains position next page middle depth pages index ordinal
  | page == middle = extendPagesLookup contains position next page depth pages index ordinal
  | otherwise =
      let transition = next page (lastPageData pages)
          extended = appendOrderedPage (contains (page - 1)) (contains page) pages transition
      in extendPagesThroughLookup contains position next (page + 1) middle depth extended index ordinal
