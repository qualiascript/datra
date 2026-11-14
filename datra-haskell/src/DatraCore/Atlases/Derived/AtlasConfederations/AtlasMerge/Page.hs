{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif TraceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Merge page chains restricted to canonical component traces.
module AtlasMerge.Page
  ( AtlasMergePageCell (..)
  , atlasMergePageChain
  , mergePagePosition
  , mergePageContains
  , previousMergeCell
  , nextMergeCell
  , mergePageTransition
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import Chain.Internal (Chain, chainPosition, chainOrderType, reindexChain, reindexedPosition)
import Chain.Position (withChainPosition)
import Chain.Sum (sumChains, sumChainPosition)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget)
import Consolidation.Endpoints (withConsolidationEndpoints)
import Consolidation.Reindex (reindexConsolidation)
import Consolidation.Sum (sumConsolidations)
import DatraOrdinal.Internal (Ordinal, addOrdinals)
import Folio.Internal (Folio)
import Numeric.Natural (Natural)
import PageElements.Internal (folioPageOrderType)
import PageElements.TraceChain (traceHead, pageTraceChain, pageTraceContains, pageTraceTransition, previousTrace, pageTracePrevious, pageTraceNext)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

data AtlasMergePageCell
  = AtlasMergeLeftCell [Ordinal]
  | AtlasMergeRightCell [Ordinal]
  deriving (Eq, Show)

{-@ reflect mergePagePosition @-}
mergePagePosition :: Ordinal -> AtlasMergePageCell -> Ordinal
mergePagePosition _ (AtlasMergeLeftCell positions) = traceHead positions
mergePagePosition leftOrder (AtlasMergeRightCell positions) = addOrdinals leftOrder (traceHead positions)

{-@ reflect mergePageContains @-}
mergePageContains :: Folio lo lf -> Folio ro rf -> Natural -> AtlasMergePageCell -> Bool
mergePageContains left right page = mergeCellAccepted (pageTraceContains left page) (pageTraceContains right page)

{-@ reflect mergeCellAccepted @-}
mergeCellAccepted :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> AtlasMergePageCell -> Bool
mergeCellAccepted left _ (AtlasMergeLeftCell positions) = left positions
mergeCellAccepted _ right (AtlasMergeRightCell positions) = right positions

{-@ reflect mergeCellFromParts @-}
{-@ ple mergeCellFromParts @-}
{-@ mergeCellFromParts :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> Either {positions:[Ordinal] | left positions}
                {positions:[Ordinal] | right positions}
      -> {cell:AtlasMergePageCell | mergeCellAccepted left right cell} @-}
mergeCellFromParts :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Either [Ordinal] [Ordinal] -> AtlasMergePageCell
mergeCellFromParts _ _ (Left positions) = AtlasMergeLeftCell positions
mergeCellFromParts _ _ (Right positions) = AtlasMergeRightCell positions

{-@ reflect mergeCellParts @-}
{-@ ple mergeCellParts @-}
{-@ mergeCellParts :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> {cell:AtlasMergePageCell | mergeCellAccepted left right cell}
      -> Either {positions:[Ordinal] | left positions}
                {positions:[Ordinal] | right positions} @-}
mergeCellParts :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> AtlasMergePageCell -> Either [Ordinal] [Ordinal]
mergeCellParts _ _ (AtlasMergeLeftCell positions) = Left positions
mergeCellParts _ _ (AtlasMergeRightCell positions) = Right positions

{-@ mergePartsRoundTrip :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> parts:Either {positions:[Ordinal] | left positions}
                      {positions:[Ordinal] | right positions}
      -> {mergeCellParts left right (mergeCellFromParts left right parts) == parts} @-}
{-@ ple mergePartsRoundTrip @-}
mergePartsRoundTrip :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Either [Ordinal] [Ordinal] -> ()
mergePartsRoundTrip _ _ (Left _) = ()
mergePartsRoundTrip _ _ (Right _) = ()

{-@ mergeCellRoundTrip :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> cell:{AtlasMergePageCell | mergeCellAccepted left right cell}
      -> {mergeCellFromParts left right (mergeCellParts left right cell) == cell} @-}
{-@ ple mergeCellRoundTrip @-}
mergeCellRoundTrip :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> AtlasMergePageCell -> ()
mergeCellRoundTrip _ _ (AtlasMergeLeftCell _) = ()
mergeCellRoundTrip _ _ (AtlasMergeRightCell _) = ()

-- ALIGN: MERGE-NATIVE-CHAIN-INTERPRETATION.
-- ALIGN: MERGE-PAGE-CHAIN.
-- ALIGN: MERGE-PAGE-LOOKUP-BOUNDS.
-- ALIGN: MERGE-PAGE-TRACE-ENCODING.
-- ALIGN: MERGE-PAGE-ORDER-INTERPRETATION.
-- ALIGN: MERGE-FINITE-PAGE-EQUIVALENCE.
{-@ atlasMergePageChain :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf -> page:Natural
      -> {result:Chain {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) page cell} |
             chainPosition result == mergePagePosition (folioPageOrderType (atlasFolio left) page)} @-}
{-@ ple atlasMergePageChain @-}
atlasMergePageChain
  :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
atlasMergePageChain left right page =
  mergePageChainFromParts
    (pageTraceContains (atlasFolio left) page)
    (pageTraceContains (atlasFolio right) page)
    (pageTraceChain (atlasFolio left) page)
    (pageTraceChain (atlasFolio right) page)

{-@ mergePageChainFromParts :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> leftChain:{Chain {positions:[Ordinal] | left positions} | chainPosition leftChain == traceHead}
      -> rightChain:{Chain {positions:[Ordinal] | right positions} | chainPosition rightChain == traceHead}
      -> {result:Chain {cell:AtlasMergePageCell | mergeCellAccepted left right cell} |
           chainPosition result == mergePagePosition (chainOrderType leftChain)} @-}
{-@ ple mergePageChainFromParts @-}
mergePageChainFromParts
  :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Chain [Ordinal] -> Chain [Ordinal] -> Chain AtlasMergePageCell
mergePageChainFromParts left right leftChain rightChain =
  let summed = sumChains leftChain rightChain
      native = reindexChain (mergeCellAccepted left right) summed
        (mergeCellFromParts left right) (mergeCellParts left right)
        (mergePartsRoundTrip left right) (mergeCellRoundTrip left right)
  in withChainPosition (mergeCellAccepted left right) native (mergePagePosition (chainOrderType leftChain))
       (mergePositionEquation left right leftChain rightChain summed native)

{-@ mergePositionEquation :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> leftChain:{Chain {positions:[Ordinal] | left positions} | chainPosition leftChain == traceHead}
      -> rightChain:{Chain {positions:[Ordinal] | right positions} | chainPosition rightChain == traceHead}
      -> summed:{Chain (Either {positions:[Ordinal] | left positions} {positions:[Ordinal] | right positions}) |
           chainPosition summed == sumChainPosition leftChain rightChain}
      -> native:{Chain {cell:AtlasMergePageCell | mergeCellAccepted left right cell} |
           chainPosition native == reindexedPosition (mergeCellAccepted left right) summed (mergeCellParts left right)}
      -> cell:{AtlasMergePageCell | mergeCellAccepted left right cell}
      -> {mergePagePosition (chainOrderType leftChain) cell == chainPosition native cell} @-}
mergePositionEquation :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Chain [Ordinal] -> Chain [Ordinal]
  -> Chain (Either [Ordinal] [Ordinal]) -> Chain AtlasMergePageCell -> AtlasMergePageCell -> ()
{-@ ple mergePositionEquation @-}
mergePositionEquation left right leftChain rightChain summed _ cell@(AtlasMergeLeftCell _) =
  reindexedPosition (mergeCellAccepted left right) summed (mergeCellParts left right) cell `seq`
    sumChainPosition leftChain rightChain (mergeCellParts left right cell) `seq` ()
mergePositionEquation left right leftChain rightChain summed _ cell@(AtlasMergeRightCell _) =
  reindexedPosition (mergeCellAccepted left right) summed (mergeCellParts left right) cell `seq`
    sumChainPosition leftChain rightChain (mergeCellParts left right cell) `seq` ()

-- | The predecessor remains a canonical cell of the same component.
-- ALIGN: MERGE-PAGE-PREVIOUS.
-- ALIGN: MERGE-PAGE-PREVIOUS-VALID.
{-@ reflect previousMergeCell @-}
{-@ previousMergeCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
      -> {result:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) result} @-}
{-@ ple previousMergeCell @-}
previousMergeCell
  :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> AtlasMergePageCell
previousMergeCell left _ page (AtlasMergeLeftCell positions) =
  pageTracePrevious (atlasFolio left) (page - 1) positions `seq`
    AtlasMergeLeftCell (previousTrace positions)
previousMergeCell _ right page (AtlasMergeRightCell positions) =
  pageTracePrevious (atlasFolio right) (page - 1) positions `seq`
    AtlasMergeRightCell (previousTrace positions)

-- ALIGN: MERGE-PAGE-NEXT.
-- ALIGN: MERGE-PAGE-NEXT-VALID.
-- ALIGN: MERGE-PAGE-PREIMAGE.
{-@ nextMergeCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell}
      -> {result:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) page result
           && previousMergeCell left right page result == cell} @-}
{-@ ple nextMergeCell @-}
nextMergeCell
  :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> AtlasMergePageCell
nextMergeCell left _ page (AtlasMergeLeftCell positions) =
  AtlasMergeLeftCell (pageTraceNext (atlasFolio left) (page - 1) positions)
nextMergeCell _ right page (AtlasMergeRightCell positions) =
  AtlasMergeRightCell (pageTraceNext (atlasFolio right) (page - 1) positions)

-- | Sum the native trace transitions and transport their checked orders and
-- chosen preimages through the merge-cell encoding.
-- ALIGN: MERGE-PAGE-TRANSITION.
-- ALIGN: MERGE-PAGE-TRANSITION-INTERPRETATION.
-- ALIGN: MERGE-NATIVE-TRANSITION.
{-@ mergePageTransition :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             chainPosition target == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> {result:OrderedConsolidation
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             chainPosition (orderedSource result) == mergePagePosition (folioPageOrderType (atlasFolio left) page)
             && orderedTarget result == target} @-}
{-@ ple mergePageTransition @-}
mergePageTransition :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
mergePageTransition left right page target =
  let mapping = mergeTraceTransition (atlasFolio left) (atlasFolio right) page
  in withConsolidationEndpoints
       (mergeCellAccepted (pageTraceContains (atlasFolio left) page) (pageTraceContains (atlasFolio right) page))
       (mergeCellAccepted (pageTraceContains (atlasFolio left) (page - 1)) (pageTraceContains (atlasFolio right) (page - 1)))
       mapping (orderedSource mapping) target (const ()) (const ())

{-@ mergeTraceTransition :: leftPages:Folio lo lf -> rightPages:Folio ro rf
      -> page:{Natural | page > 0}
      -> {result:OrderedConsolidation
           {cell:AtlasMergePageCell | mergeCellAccepted (pageTraceContains leftPages page) (pageTraceContains rightPages page) cell}
           {cell:AtlasMergePageCell | mergeCellAccepted (pageTraceContains leftPages (page - 1)) (pageTraceContains rightPages (page - 1)) cell} |
             chainPosition (orderedSource result) == mergePagePosition (folioPageOrderType leftPages page)
             && chainPosition (orderedTarget result) == mergePagePosition (folioPageOrderType leftPages (page - 1))} @-}
mergeTraceTransition :: Folio lo lf -> Folio ro rf -> Natural
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
mergeTraceTransition leftPages rightPages page =
  let sourceLeft = pageTraceContains leftPages page
      sourceRight = pageTraceContains rightPages page
      targetLeft = pageTraceContains leftPages (page - 1)
      targetRight = pageTraceContains rightPages (page - 1)
      leftTransition = pageTraceTransition leftPages (page - 1)
        (pageTraceChain leftPages page) (pageTraceChain leftPages (page - 1))
      rightTransition = pageTraceTransition rightPages (page - 1)
        (pageTraceChain rightPages page) (pageTraceChain rightPages (page - 1))
      summed = sumTraceTransitions sourceLeft sourceRight targetLeft targetRight leftTransition rightTransition
      native = reindexConsolidation
        (mergeCellAccepted sourceLeft sourceRight) (mergeCellAccepted targetLeft targetRight) summed
        (mergeCellFromParts sourceLeft sourceRight) (mergeCellParts sourceLeft sourceRight)
        (mergePartsRoundTrip sourceLeft sourceRight) (mergeCellRoundTrip sourceLeft sourceRight)
        (mergeCellFromParts targetLeft targetRight) (mergeCellParts targetLeft targetRight)
        (mergePartsRoundTrip targetLeft targetRight) (mergeCellRoundTrip targetLeft targetRight)
      sourcePositions = mergePositionEquation sourceLeft sourceRight
        (orderedSource leftTransition) (orderedSource rightTransition) (orderedSource summed) (orderedSource native)
      targetPositions = mergePositionEquation targetLeft targetRight
        (orderedTarget leftTransition) (orderedTarget rightTransition) (orderedTarget summed) (orderedTarget native)
      source = withChainPosition (mergeCellAccepted sourceLeft sourceRight) (orderedSource native) (mergePagePosition (folioPageOrderType leftPages page)) sourcePositions
      target = withChainPosition (mergeCellAccepted targetLeft targetRight) (orderedTarget native) (mergePagePosition (folioPageOrderType leftPages (page - 1))) targetPositions
  in withConsolidationEndpoints (mergeCellAccepted sourceLeft sourceRight) (mergeCellAccepted targetLeft targetRight)
       native source target sourcePositions targetPositions

{-@ sumTraceTransitions :: sourceLeft:([Ordinal] -> Bool) -> sourceRight:([Ordinal] -> Bool)
      -> targetLeft:([Ordinal] -> Bool) -> targetRight:([Ordinal] -> Bool)
      -> left:OrderedConsolidation {positions:[Ordinal] | sourceLeft positions} {positions:[Ordinal] | targetLeft positions}
      -> right:OrderedConsolidation {positions:[Ordinal] | sourceRight positions} {positions:[Ordinal] | targetRight positions}
      -> {result:OrderedConsolidation
           (Either {positions:[Ordinal] | sourceLeft positions} {positions:[Ordinal] | sourceRight positions})
           (Either {positions:[Ordinal] | targetLeft positions} {positions:[Ordinal] | targetRight positions}) |
             chainPosition (orderedSource result) == sumChainPosition (orderedSource left) (orderedSource right)
             && chainPosition (orderedTarget result) == sumChainPosition (orderedTarget left) (orderedTarget right)} @-}
sumTraceTransitions :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> ([Ordinal] -> Bool)
  -> OrderedConsolidation [Ordinal] [Ordinal] -> OrderedConsolidation [Ordinal] [Ordinal]
  -> OrderedConsolidation (Either [Ordinal] [Ordinal]) (Either [Ordinal] [Ordinal])
sumTraceTransitions _ _ _ _ = sumConsolidations
