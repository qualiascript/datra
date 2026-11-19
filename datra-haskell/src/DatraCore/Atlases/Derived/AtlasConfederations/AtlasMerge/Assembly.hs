{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif MergeAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Assemble the finite merge folio with certified native page endpoints.
module AtlasMerge.Assembly
  ( atlasMergeLength, atlasMergeFolio, atlasMergePrefix, atlasMergePrefixLookup, atlasMergePageLookup, atlasMergeCellLookup, atlasMergePrefixTrace
  , appendRemainingPages, appendRemainingLookup ) where

import Atlas.Internal (Atlas, atlasFolio)
import AtlasMerge.Page
  ( AtlasMergePageCell (..), atlasMergePageChain, mergePageContains, mergePagePosition, mergePageTransition
  , previousMergeCell, nextMergeCell )
import Chain.Internal (Chain, chainPosition)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedApply, orderedPreimage)
import Chain.Singleton (singletonChain)
import Folio.Assembly (collapseToOrigin, extendPages, extendPagesLookup, extendPagesThroughLookup, extendPagesFinalTrace)
import Folio.Internal (Folio)
import Folio.Presentation (folioData, appendPageData, folioLengthData, lastPageData)
import DatraOrdinal (Ordinal)
import Numeric.Natural (Natural)
import PageElements.Internal (folioPageOrderType, folioTraceLookup, genuinePageElementTrace, finalPageTraceLookup, prependCopies)
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

-- | The page-indexed position family used by the shared prefix builder.
{-@ reflect mergePositionAt @-}
{-@ mergePositionAt :: left:Atlas la ls ld lo lf -> page:Natural
      -> {position:(AtlasMergePageCell -> Ordinal) |
           position == mergePagePosition (folioPageOrderType (atlasFolio left) page)} @-}
mergePositionAt :: Atlas la ls ld lo lf -> Natural -> AtlasMergePageCell -> Ordinal
mergePositionAt left page = mergePagePosition (folioPageOrderType (atlasFolio left) page)

{-@ reflect mergeTransitionAt @-}
{-@ mergeTransitionAt :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           chainPosition target == mergePositionAt left (page - 1)}
      -> {result:OrderedConsolidation
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             chainPosition (orderedSource result) == mergePositionAt left page && orderedTarget result == target
             && orderedApply result == previousMergeCell left right page
             && orderedPreimage result == nextMergeCell left right page} @-}
mergeTransitionAt :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
mergeTransitionAt left right page target =
  mergePositionAt left (page - 1) `seq` mergePositionAt left page `seq`
    mergePageTransition left right page target

-- ALIGN: MERGE-FOLIO-PREFIX.
-- ALIGN: MERGE-PREFIX-EXTENSION-EQUALITY.
{-@ reflect appendRemainingPages @-}
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
{-@ ple appendRemainingPages @-}
appendRemainingPages left right page depth pages =
  mergePositionAt left (page - 1) `seq` mergePositionAt left (depth - 1) `seq`
  extendPages (mergePageContains (atlasFolio left) (atlasFolio right))
    (mergePositionAt left)
    (mergeTransitionAt left right) page depth pages

-- | Extending the finite merge preserves every lookup in its existing prefix.
-- ALIGN: MERGE-PREFIX-LOOKUP-PRESERVED.
{-@ appendRemainingLookup :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0} -> depth:{Natural | page <= depth}
      -> pages:{Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
           folioLengthData pages == page + 1
           && chainPosition (lastPageData pages) == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> index:{Natural | index < folioLengthData pages} -> position:Ordinal
      -> {folioTraceLookup (appendRemainingPages left right page depth pages) index position
           == folioTraceLookup pages index position} / [depth - page] @-}
{-@ ple appendRemainingLookup @-}
appendRemainingLookup :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> Folio () AtlasMergePageCell -> Natural -> Ordinal -> ()
appendRemainingLookup left right page depth pages index position =
  mergePositionAt left (page - 1) `seq`
  extendPagesLookup (mergePageContains (atlasFolio left) (atlasFolio right))
    (mergePositionAt left)
    (mergeTransitionAt left right) page depth pages index position

-- | The certified seed shared by every finite merge prefix.
{-@ opaque-reflect firstMergePage @-}
{-@ firstMergePage :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> {result:Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) 0 cell} |
           folioLengthData result == 2
           && chainPosition (lastPageData result) == mergePagePosition (folioPageOrderType (atlasFolio left) 0)} @-}
firstMergePage :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Folio () AtlasMergePageCell
firstMergePage left right =
  let origin = folioData singletonChain () (\() -> ())
      firstChain = atlasMergePageChain left right 0
      firstTransition = collapseToOrigin (mergePageContains (atlasFolio left) (atlasFolio right) 0)
        firstChain (lastPageData origin) (firstMergeCell left right)
      firstPage = appendPageData origin firstChain firstTransition
  in firstPage

-- ALIGN: MERGE-CONSTRUCTED-PREFIX.
{-@ reflect atlasMergePrefix @-}
{-@ atlasMergePrefix :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> depth:{Natural | depth > 0}
      -> {result:Folio () {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (depth - 1) cell} |
           folioLengthData result == depth + 1
           && chainPosition (lastPageData result) == mergePagePosition (folioPageOrderType (atlasFolio left) (depth - 1))} @-}
atlasMergePrefix :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Folio () AtlasMergePageCell
atlasMergePrefix left right depth = appendRemainingPages left right 1 depth (firstMergePage left right)

-- ALIGN: MERGE-CONSTRUCTED-PREFIX-LOOKUP.
{-@ atlasMergePrefixLookup :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> middle:{Natural | middle > 0} -> depth:{Natural | middle <= depth}
      -> index:{Natural | index <= middle} -> position:Ordinal
      -> {folioTraceLookup (atlasMergePrefix left right depth) index position
           == folioTraceLookup (atlasMergePrefix left right middle) index position} @-}
{-@ ple atlasMergePrefixLookup @-}
atlasMergePrefixLookup :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> Natural -> Natural -> Natural -> Ordinal -> ()
atlasMergePrefixLookup left right middle depth index position =
  mergePositionAt left 0 `seq`
    extendPagesThroughLookup (mergePageContains (atlasFolio left) (atlasFolio right))
      (mergePositionAt left) (mergeTransitionAt left right) 1 middle depth (firstMergePage left right) index position

-- ALIGN: MERGE-COLLAPSE-ORIGIN.
-- ALIGN: MERGE-FOLIO.
-- ALIGN: MERGE-COMPONENT-PAGE-INDEX.
-- ALIGN: MERGE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: MERGE-FINITE-INTERVAL-INTERPRETATION.
{-@ reflect atlasMergeFolio @-}
{-@ atlasMergeFolio :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> {result:Folio () {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (atlasMergeLength left right - 2) cell} |
             folioLengthData result == atlasMergeLength left right} @-}
atlasMergeFolio :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Folio () AtlasMergePageCell
atlasMergeFolio left right = atlasMergePrefix left right (atlasMergeLength left right - 1)

-- ALIGN: MERGE-GENUINE-PAGE-LOOKUP.
{-@ atlasMergePageLookup :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0 && page < atlasMergeLength left right} -> position:Ordinal
      -> {folioTraceLookup (atlasMergeFolio left right) page position
           == folioTraceLookup (atlasMergePrefix left right page) page position} @-}
{-@ ple atlasMergePageLookup @-}
atlasMergePageLookup :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Ordinal -> ()
atlasMergePageLookup left right page position =
  atlasMergePrefixLookup left right page (atlasMergeLength left right - 1) page position

-- ALIGN: MERGE-GENUINE-CELL-LOOKUP.
{-@ atlasMergeCellLookup :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0 && page < atlasMergeLength left right}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell}
      -> {folioTraceLookup (atlasMergeFolio left right) page
             (mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1)) cell)
           == Just (genuinePageElementTrace (atlasMergePrefix left right page) cell)} @-}
{-@ ple atlasMergeCellLookup @-}
atlasMergeCellLookup :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
atlasMergeCellLookup left right page cell =
  atlasMergePageLookup left right page (mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1)) cell) `seq`
    finalPageTraceLookup (atlasMergePrefix left right page) cell

-- | Follow the final native merge transition into the preceding constructed prefix.
-- ALIGN: MERGE-PREFIX-TRACE-STEP.
{-@ atlasMergePrefixTrace :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> depth:{Natural | depth > 0}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) depth cell}
      -> {genuinePageElementTrace (atlasMergePrefix left right (depth + 1)) cell
           == prependCopies 1 (mergePagePosition (folioPageOrderType (atlasFolio left) depth) cell)
                (genuinePageElementTrace (atlasMergePrefix left right depth) (previousMergeCell left right depth cell))} @-}
{-@ ple atlasMergePrefixTrace @-}
atlasMergePrefixTrace :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
atlasMergePrefixTrace left right depth cell =
  mergePositionAt left 0 `seq` mergePositionAt left (depth - 1) `seq` mergePositionAt left depth `seq`
    mergeTransitionAt left right depth (lastPageData (atlasMergePrefix left right depth)) `seq`
      extendPagesFinalTrace (mergePageContains (atlasFolio left) (atlasFolio right))
        (mergePositionAt left) (mergeTransitionAt left right) 1 depth (firstMergePage left right) cell
