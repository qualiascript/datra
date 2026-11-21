{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ opaque-reflect chainOrderType @-}
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

import Atlas (Atlas, atlasFolio)
import Chain (Chain, chainPosition, chainOrderType, reindexChain, reindexedPosition)
import Chain.Position (withChainPosition)
import Chain.Sum (sumChains, sumChainPosition)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedApply, orderedPreimage, withConsolidationFunctions)
import Consolidation.Endpoints (withConsolidationEndpoints)
import Consolidation.Reindex (reindexConsolidation, reindexApply, reindexPreimage)
import Consolidation.Sum (sumConsolidations, sumApply, sumPreimage)
import DatraOrdinal (Ordinal, addOrdinals)
import Folio (Folio)
import Numeric.Natural (Natural)
import PageElements (folioPageOrderType)
import PageElements.TraceChain (traceHead, pageTraceChain, pageTraceContains, pageTraceTransition, previousTrace, previousPageTrace, pageTraceNext)

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
  AtlasMergeLeftCell (previousPageTrace (atlasFolio left) (page - 1) positions)
previousMergeCell _ right page (AtlasMergeRightCell positions) =
  AtlasMergeRightCell (previousPageTrace (atlasFolio right) (page - 1) positions)

-- ALIGN: MERGE-PAGE-NEXT.
-- ALIGN: MERGE-PAGE-NEXT-VALID.
-- ALIGN: MERGE-PAGE-PREIMAGE.
{-@ reflect nextMergeCell @-}
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
-- ALIGN: MERGE-TRANSITION-STORED-MAP.
-- ALIGN: MERGE-TRANSITION-STORED-PREIMAGE.
{-@ mergePageTransition :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             chainPosition target == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))}
      -> {result:OrderedConsolidation
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             chainPosition (orderedSource result) == mergePagePosition (folioPageOrderType (atlasFolio left) page)
             && orderedTarget result == target
             && orderedApply result == previousMergeCell left right page
             && orderedPreimage result == nextMergeCell left right page} @-}
{-@ ple mergePageTransition @-}
mergePageTransition :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
mergePageTransition left right page target =
  let mapping = mergeTraceTransition left right page
  in withConsolidationEndpoints
       (mergeCellAccepted (pageTraceContains (atlasFolio left) page) (pageTraceContains (atlasFolio right) page))
       (mergeCellAccepted (pageTraceContains (atlasFolio left) (page - 1)) (pageTraceContains (atlasFolio right) (page - 1)))
       mapping (orderedSource mapping) target (const ()) (const ())

{-@ mergeTraceTransition :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> {result:OrderedConsolidation
           {cell:AtlasMergePageCell | mergeCellAccepted (pageTraceContains (atlasFolio left) page) (pageTraceContains (atlasFolio right) page) cell}
           {cell:AtlasMergePageCell | mergeCellAccepted (pageTraceContains (atlasFolio left) (page - 1)) (pageTraceContains (atlasFolio right) (page - 1)) cell} |
             chainPosition (orderedSource result) == mergePagePosition (folioPageOrderType (atlasFolio left) page)
             && chainPosition (orderedTarget result) == mergePagePosition (folioPageOrderType (atlasFolio left) (page - 1))
             && orderedApply result == previousMergeCell left right page
             && orderedPreimage result == nextMergeCell left right page} @-}
{-@ ple mergeTraceTransition @-}
mergeTraceTransition :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell
mergeTraceTransition left right page =
  let leftPages = atlasFolio left
      rightPages = atlasFolio right
      sourceLeft = pageTraceContains leftPages page
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
      exact = withConsolidationFunctions (mergeCellAccepted sourceLeft sourceRight) (mergeCellAccepted targetLeft targetRight)
        native (previousMergeCell left right page) (nextMergeCell left right page)
        (mergeForwardEquation left right page leftTransition rightTransition summed native)
        (\cell -> mergePageContains leftPages rightPages (page - 1) cell `seq`
          nextMergeCell left right page cell `seq`
          reindexPreimage summed (mergeCellFromParts sourceLeft sourceRight) (mergeCellParts targetLeft targetRight) cell `seq`
          sumPreimage leftTransition rightTransition (mergeCellParts targetLeft targetRight cell) `seq`
            case cell of
              AtlasMergeLeftCell positions ->
                sumPreimage leftTransition rightTransition (Left positions) `seq`
                mergeCellFromParts sourceLeft sourceRight (Left (pageTraceNext leftPages (page - 1) positions)) `seq` ()
              AtlasMergeRightCell positions ->
                sumPreimage leftTransition rightTransition (Right positions) `seq`
                mergeCellFromParts sourceLeft sourceRight (Right (pageTraceNext rightPages (page - 1) positions)) `seq` ())
  in withConsolidationEndpoints (mergeCellAccepted sourceLeft sourceRight) (mergeCellAccepted targetLeft targetRight)
       exact source target sourcePositions targetPositions

{-@ sumTraceTransitions :: sourceLeft:([Ordinal] -> Bool) -> sourceRight:([Ordinal] -> Bool)
      -> targetLeft:([Ordinal] -> Bool) -> targetRight:([Ordinal] -> Bool)
      -> left:OrderedConsolidation {positions:[Ordinal] | sourceLeft positions} {positions:[Ordinal] | targetLeft positions}
      -> right:OrderedConsolidation {positions:[Ordinal] | sourceRight positions} {positions:[Ordinal] | targetRight positions}
      -> {result:OrderedConsolidation
           (Either {positions:[Ordinal] | sourceLeft positions} {positions:[Ordinal] | sourceRight positions})
           (Either {positions:[Ordinal] | targetLeft positions} {positions:[Ordinal] | targetRight positions}) |
             chainPosition (orderedSource result) == sumChainPosition (orderedSource left) (orderedSource right)
             && chainPosition (orderedTarget result) == sumChainPosition (orderedTarget left) (orderedTarget right)
             && orderedApply result == sumApply left right
             && orderedPreimage result == sumPreimage left right} @-}
sumTraceTransitions :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> ([Ordinal] -> Bool)
  -> OrderedConsolidation [Ordinal] [Ordinal] -> OrderedConsolidation [Ordinal] [Ordinal]
  -> OrderedConsolidation (Either [Ordinal] [Ordinal]) (Either [Ordinal] [Ordinal])
sumTraceTransitions _ _ _ _ = sumConsolidations

{-@ mergeForwardEquation :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> leftTransition:{OrderedConsolidation
           {positions:[Ordinal] | pageTraceContains (atlasFolio left) page positions}
           {positions:[Ordinal] | pageTraceContains (atlasFolio left) (page - 1) positions} |
             orderedApply leftTransition == previousPageTrace (atlasFolio left) (page - 1)
             && orderedPreimage leftTransition == pageTraceNext (atlasFolio left) (page - 1)}
      -> rightTransition:{OrderedConsolidation
           {positions:[Ordinal] | pageTraceContains (atlasFolio right) page positions}
           {positions:[Ordinal] | pageTraceContains (atlasFolio right) (page - 1) positions} |
             orderedApply rightTransition == previousPageTrace (atlasFolio right) (page - 1)
             && orderedPreimage rightTransition == pageTraceNext (atlasFolio right) (page - 1)}
      -> summed:{OrderedConsolidation
           (Either {positions:[Ordinal] | pageTraceContains (atlasFolio left) page positions}
                   {positions:[Ordinal] | pageTraceContains (atlasFolio right) page positions})
           (Either {positions:[Ordinal] | pageTraceContains (atlasFolio left) (page - 1) positions}
                   {positions:[Ordinal] | pageTraceContains (atlasFolio right) (page - 1) positions}) |
             orderedApply summed == sumApply leftTransition rightTransition
             && orderedPreimage summed == sumPreimage leftTransition rightTransition}
      -> native:{OrderedConsolidation
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
           {cell:AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) (page - 1) cell} |
             orderedApply native == reindexApply summed
               (mergeCellFromParts (pageTraceContains (atlasFolio left) (page - 1)) (pageTraceContains (atlasFolio right) (page - 1)))
               (mergeCellParts (pageTraceContains (atlasFolio left) page) (pageTraceContains (atlasFolio right) page))
             && orderedPreimage native == reindexPreimage summed
               (mergeCellFromParts (pageTraceContains (atlasFolio left) page) (pageTraceContains (atlasFolio right) page))
               (mergeCellParts (pageTraceContains (atlasFolio left) (page - 1)) (pageTraceContains (atlasFolio right) (page - 1)))}
      -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
      -> {previousMergeCell left right page cell == orderedApply native cell} @-}
{-@ ple mergeForwardEquation @-}
mergeForwardEquation :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural
  -> OrderedConsolidation [Ordinal] [Ordinal] -> OrderedConsolidation [Ordinal] [Ordinal]
  -> OrderedConsolidation (Either [Ordinal] [Ordinal]) (Either [Ordinal] [Ordinal])
  -> OrderedConsolidation AtlasMergePageCell AtlasMergePageCell -> AtlasMergePageCell -> ()
mergeForwardEquation left right page leftTransition rightTransition summed native cell =
  let leftPages = atlasFolio left
      rightPages = atlasFolio right
      sourceLeft = pageTraceContains leftPages page
      sourceRight = pageTraceContains rightPages page
      targetLeft = pageTraceContains leftPages (page - 1)
      targetRight = pageTraceContains rightPages (page - 1)
  in mergePageContains leftPages rightPages page cell `seq`
    previousMergeCell left right page cell `seq`
    reindexApply summed (mergeCellFromParts targetLeft targetRight) (mergeCellParts sourceLeft sourceRight) cell `seq`
    sumApply leftTransition rightTransition (mergeCellParts sourceLeft sourceRight cell) `seq`
    case cell of
      AtlasMergeLeftCell positions ->
        sumApply leftTransition rightTransition (Left positions) `seq`
        mergeCellFromParts targetLeft targetRight (Left (previousPageTrace leftPages (page - 1) positions)) `seq` ()
      AtlasMergeRightCell positions ->
        sumApply leftTransition rightTransition (Right positions) `seq`
        mergeCellFromParts targetLeft targetRight (Right (previousPageTrace rightPages (page - 1) positions)) `seq` ()
