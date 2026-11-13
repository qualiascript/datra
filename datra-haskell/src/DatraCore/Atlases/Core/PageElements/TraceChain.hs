{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | A page chain whose carrier consists of its canonical transport traces.
module PageElements.TraceChain
  ( pageTraceChain
  , pageTraceContains
  , traceHead
  ) where

import Chain.Internal (Chain, chain, chainOrdinalLT, positionMatches)
import DatraOrdinal.Internal (Ordinal, finiteOrdinal)
import Folio.Internal (Folio)
import Numeric.Natural (Natural)
import PageElements.Internal
  ( folioTraceLookup
  , folioTraceLookupHead
  , traceLookupPresent
  , traceLookupStartsWith
  , folioPageOrderType
  , folioTraceLookupBounded
  )
import PageElements.LiquidInternal (traceStartsWith)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

{-@ reflect traceHead @-}
traceHead :: [Ordinal] -> Ordinal
traceHead [] = finiteOrdinal 0
traceHead (position : _) = position

{-@ traceHeadMatches :: position:Ordinal -> positions:{[Ordinal] | traceStartsWith position positions}
      -> {traceHead positions == position} @-}
traceHeadMatches :: Ordinal -> [Ordinal] -> ()
traceHeadMatches _ [] = ()
traceHeadMatches _ (_ : _) = ()

{-@ reflect pageTraceContains @-}
pageTraceContains :: Folio origin final -> Natural -> [Ordinal] -> Bool
pageTraceContains pages page positions =
  folioTraceLookup pages page (traceHead positions) == Just positions

{-@ reflect pageTraceLookup @-}
{-@ pageTraceLookup :: pages:Folio origin final -> page:Natural
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position})
      -> position:Ordinal
      -> {result:Maybe ({positions:[Ordinal] | pageTraceContains pages page positions
           && traceHead positions == position}) | result == lookupTrace position} @-}
pageTraceLookup
  :: Folio origin final -> Natural -> (Ordinal -> Maybe [Ordinal]) -> Ordinal -> Maybe [Ordinal]
pageTraceLookup pages page lookupTrace position =
  folioTraceLookupHead pages page position `seq`
    case lookupTrace position of
      Nothing -> Nothing
      Just positions -> traceHeadMatches position positions `seq` Just positions

{-@ pageTracePositionBelow :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> positions:{[Ordinal] | pageTraceContains pages page positions}
      -> {chainOrdinalLT (traceHead positions) order} @-}
pageTracePositionBelow
  :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> [Ordinal] -> ()
pageTracePositionBelow _ _ _ lookupTrace positions = lookupTrace (traceHead positions) `seq` ()

{-@ pageTracePositionInjective :: pages:Folio origin final -> page:Natural
      -> first:{[Ordinal] | pageTraceContains pages page first}
      -> second:{[Ordinal] | pageTraceContains pages page second}
      -> {traceHead first == traceHead second => first == second} @-}
pageTracePositionInjective :: Folio origin final -> Natural -> [Ordinal] -> [Ordinal] -> ()
pageTracePositionInjective _ _ _ _ = ()

{-@ pageTracePositionSurjective :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> position:Ordinal
      -> {chainOrdinalLT position order =>
           positionMatches traceHead position (pageTraceLookup pages page lookupTrace position)} @-}
pageTracePositionSurjective
  :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> Ordinal -> ()
pageTracePositionSurjective pages page _ lookupTrace position =
  lookupTrace position `seq`
    case pageTraceLookup pages page lookupTrace position of
      Nothing -> ()
      Just _ -> ()

-- | Restrict the carrier before passing it to the proof-bearing Chain constructor.
-- ALIGN: PE-TRACE-CHAIN.
{-@ pageTraceChain :: pages:Folio origin final -> page:Natural
      -> Chain {positions:[Ordinal] | pageTraceContains pages page positions} @-}
pageTraceChain :: Folio origin final -> Natural -> Chain [Ordinal]
pageTraceChain pages page =
  pageTraceChainAtOrder pages page (folioPageOrderType pages page) (boundedFolioTraceLookup pages page)

{-@ boundedFolioTraceLookup :: pages:Folio origin final -> page:Natural -> position:Ordinal
      -> {result:Maybe [Ordinal] | result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position (folioPageOrderType pages page)} @-}
boundedFolioTraceLookup :: Folio origin final -> Natural -> Ordinal -> Maybe [Ordinal]
boundedFolioTraceLookup pages page position =
  folioTraceLookupBounded pages page position `seq` folioTraceLookup pages page position

{-@ pageTraceChainAtOrder :: pages:Folio origin final -> page:Natural -> order:Ordinal
      -> lookupTrace:(position:Ordinal -> {result:Maybe [Ordinal] |
           result == folioTraceLookup pages page position
           && traceLookupPresent result == chainOrdinalLT position order})
      -> Chain {positions:[Ordinal] | pageTraceContains pages page positions} @-}
pageTraceChainAtOrder :: Folio origin final -> Natural -> Ordinal -> (Ordinal -> Maybe [Ordinal]) -> Chain [Ordinal]
pageTraceChainAtOrder pages page order lookupTrace =
    chain
      order
      traceHead
      (pageTraceLookup pages page lookupTrace)
      (pageTracePositionBelow pages page order lookupTrace)
      (pageTracePositionInjective pages page)
      (pageTracePositionSurjective pages page order lookupTrace)
