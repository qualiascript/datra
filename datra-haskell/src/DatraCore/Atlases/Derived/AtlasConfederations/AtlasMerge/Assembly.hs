{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif MergeAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Assemble the finite merge folio with certified native page endpoints.
module AtlasMerge.Assembly (atlasMergeLength, atlasMergeFolio) where

import Atlas.Internal (Atlas, atlasFolio)
import AtlasMerge.Page
  ( AtlasMergePageCell (..), atlasMergePageChain, mergePageContains, mergePagePosition, mergePageTransition )
import Chain.Internal (Chain, chainPosition)
import Chain.Singleton (singletonChain)
import Chain.Order (chainPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedConsolidation)
import DatraOrdinal.Laws (ordinalLTIrreflexive)
import Folio.Internal (Folio)
import Folio.Presentation (folioData, appendPageData, folioLengthData, lastPageData)
import Numeric.Natural (Natural)
import PageElements.Internal (folioPageOrderType)
import PageElements.TraceChain (pageTraceOrigin)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: MERGE-FOLIO-LENGTH.
-- ALIGN: MERGE-FOLIO-LENGTH-INTERPRETATION.
{-@ reflect atlasMergeLength @-}
{-@ atlasMergeLength :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> {count:Natural | count > 1} @-}
atlasMergeLength :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural
{-@ ple atlasMergeLength @-}
atlasMergeLength left right =
  max (folioLengthData (atlasFolio left)) (folioLengthData (atlasFolio right)) + 1

-- ALIGN: MERGE-FIRST-CELL.
{-@ firstMergeCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) 0 cell} @-}
{-@ ple firstMergeCell @-}
firstMergeCell :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergePageCell
firstMergeCell left _ = AtlasMergeLeftCell (pageTraceOrigin (atlasFolio left))

-- ALIGN: MERGE-COLLAPSE-ORIGIN.
{-@ collapseToOrigin :: contains:(AtlasMergePageCell -> Bool)
      -> source:Chain {cell:AtlasMergePageCell | contains cell} -> target:Chain ()
      -> chosen:{AtlasMergePageCell | contains chosen}
      -> {result:OrderedConsolidation {cell:AtlasMergePageCell | contains cell} () |
           orderedSource result == source && orderedTarget result == target} @-}
collapseToOrigin :: (AtlasMergePageCell -> Bool) -> Chain AtlasMergePageCell -> Chain ()
  -> AtlasMergePageCell -> OrderedConsolidation AtlasMergePageCell ()
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

-- ALIGN: MERGE-FOLIO-PREFIX.
{-@ appendRemainingPages :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> {result:Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (depth - 1) cell} |
           folioLengthData result == depth + 1
           && chainPosition (lastPageData result) == mergePagePosition (folioPageOrderType (atlasFolio left) (depth - 1))}
      / [depth - page] @-}
appendRemainingPages :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> Folio () AtlasMergePageCell -> Folio () AtlasMergePageCell
appendRemainingPages left right page depth pages
  | page == depth = pages
  | otherwise =
      let transition = mergePageTransition left right page (lastPageData pages)
      in appendRemainingPages left right (page + 1) depth
           (appendMergePage
             (mergePageContains (atlasFolio left) (atlasFolio right) (page - 1))
             (mergePageContains (atlasFolio left) (atlasFolio right) page) pages transition)

{-@ appendMergePage :: previousContains:(AtlasMergePageCell -> Bool) -> nextContains:(AtlasMergePageCell -> Bool)
      -> pages:Folio () {cell:AtlasMergePageCell | previousContains cell}
      -> transition:{OrderedConsolidation {cell:AtlasMergePageCell | nextContains cell}
           {cell:AtlasMergePageCell | previousContains cell} | orderedTarget transition == lastPageData pages}
      -> {result:Folio () {cell:AtlasMergePageCell | nextContains cell} |
           folioLengthData result == folioLengthData pages + 1 && lastPageData result == orderedSource transition} @-}
appendMergePage :: (AtlasMergePageCell -> Bool) -> (AtlasMergePageCell -> Bool)
  -> Folio () AtlasMergePageCell -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
  -> Folio () AtlasMergePageCell
appendMergePage _ _ pages transition = appendPageData pages (orderedSource transition) transition

-- ALIGN: MERGE-FOLIO.
-- ALIGN: MERGE-COMPONENT-PAGE-INDEX.
-- ALIGN: MERGE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: MERGE-FINITE-INTERVAL-INTERPRETATION.
{-@ atlasMergeFolio :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> {result:Folio () {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (atlasMergeLength left right - 2) cell} |
             folioLengthData result == atlasMergeLength left right} @-}
atlasMergeFolio :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Folio () AtlasMergePageCell
atlasMergeFolio left right =
  let depth = atlasMergeLength left right - 1
      origin = folioData singletonChain () (\() -> ())
      firstChain = atlasMergePageChain left right 0
      firstTransition = collapseToOrigin (mergePageContains (atlasFolio left) (atlasFolio right) 0)
        firstChain (lastPageData origin) (firstMergeCell left right)
      firstPage = appendPageData origin firstChain firstTransition
  in appendRemainingPages left right 1 depth firstPage
