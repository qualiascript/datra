{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif TraceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Merge page chains restricted to canonical component traces.
module AtlasMerge.Page
  ( AtlasMergePageCell (..)
  , atlasMergePageChain
  , mergePageContains
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import Chain.Internal (Chain, reindexChain)
import Chain.LiquidInternal (sumChains)
import DatraOrdinal.Internal (Ordinal)
import Folio.Internal (Folio)
import Numeric.Natural (Natural)
import PageElements.TraceChain (pageTraceChain, pageTraceContains)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

data AtlasMergePageCell
  = AtlasMergeLeftCell [Ordinal]
  | AtlasMergeRightCell [Ordinal]
  deriving (Eq, Show)

{-@ reflect mergePageContains @-}
mergePageContains :: Folio lo lf -> Folio ro rf -> Natural -> AtlasMergePageCell -> Bool
mergePageContains left right page = mergeCellAccepted (pageTraceContains left page) (pageTraceContains right page)

{-@ reflect mergeCellAccepted @-}
mergeCellAccepted :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> AtlasMergePageCell -> Bool
mergeCellAccepted left _ (AtlasMergeLeftCell positions) = left positions
mergeCellAccepted _ right (AtlasMergeRightCell positions) = right positions

{-@ reflect mergeCellFromParts @-}
{-@ mergeCellFromParts :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> Either {positions:[Ordinal] | left positions}
                {positions:[Ordinal] | right positions}
      -> {cell:AtlasMergePageCell | mergeCellAccepted left right cell} @-}
mergeCellFromParts :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Either [Ordinal] [Ordinal] -> AtlasMergePageCell
mergeCellFromParts _ _ (Left positions) = AtlasMergeLeftCell positions
mergeCellFromParts _ _ (Right positions) = AtlasMergeRightCell positions

{-@ reflect mergeCellParts @-}
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
mergePartsRoundTrip :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Either [Ordinal] [Ordinal] -> ()
mergePartsRoundTrip _ _ (Left _) = ()
mergePartsRoundTrip _ _ (Right _) = ()

{-@ mergeCellRoundTrip :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> cell:{AtlasMergePageCell | mergeCellAccepted left right cell}
      -> {mergeCellFromParts left right (mergeCellParts left right cell) == cell} @-}
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
      -> Chain {cell:AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) page cell} @-}
atlasMergePageChain
  :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Chain AtlasMergePageCell
atlasMergePageChain left right page =
  mergePageChainFromParts
    (pageTraceContains (atlasFolio left) page)
    (pageTraceContains (atlasFolio right) page)
    (pageTraceChain (atlasFolio left) page)
    (pageTraceChain (atlasFolio right) page)

{-@ mergePageChainFromParts :: left:([Ordinal] -> Bool) -> right:([Ordinal] -> Bool)
      -> Chain {positions:[Ordinal] | left positions}
      -> Chain {positions:[Ordinal] | right positions}
      -> Chain {cell:AtlasMergePageCell | mergeCellAccepted left right cell} @-}
mergePageChainFromParts
  :: ([Ordinal] -> Bool) -> ([Ordinal] -> Bool) -> Chain [Ordinal] -> Chain [Ordinal] -> Chain AtlasMergePageCell
mergePageChainFromParts left right leftChain rightChain =
  reindexChain (mergeCellAccepted left right) (sumChains leftChain rightChain)
    (mergeCellFromParts left right)
    (mergeCellParts left right)
    (mergePartsRoundTrip left right)
    (mergeCellRoundTrip left right)
