{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif SequenceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | A finite ordinal sum of the members' canonical trace chains.
module AtlasSequence.Page
  ( AtlasSequencePageCell (..)
  , sequencePageContains
  , headCell
  , sequencePageOrder
  , sequencePagePosition
  , atlasSequencePageChain
  , sequencePageTransition
  ) where

import AtlasSequence.Member (AtlasSequenceMember, memberPageContains, memberPageOrder, memberPageChain, memberPageTransition)
import Chain.Internal
  ( Chain, chain, chainPosition, chainOrderType, chainOrdinalLT, positionMatches
  , reindexChain, reindexedPosition )
import Chain.Position (withChainPosition)
import Chain.Sum (sumChains, sumChainPosition)
import Chain.Order (chainPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedConsolidation)
import Consolidation.Endpoints (withConsolidationEndpoints)
import Consolidation.Reindex (reindexConsolidation)
import Consolidation.Sum (sumConsolidations)
import DatraOrdinal.Internal (Ordinal (..), finiteOrdinal, addOrdinals, coefficientsLT)
import Numeric.Natural (Natural)
import PageElements.TraceChain (traceHead)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

data AtlasSequencePageCell = AtlasSequencePageCell Natural [Ordinal]
  deriving (Eq, Show)

{-@ reflect sequencePageContains @-}
sequencePageContains :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Bool
sequencePageContains [] _ = emptyContains
sequencePageContains (member : rest) page =
  consContains (memberPageContains member page) (sequencePageContains rest page)

{-@ reflect consContains @-}
consContains :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool) -> AtlasSequencePageCell -> Bool
consContains first rest (AtlasSequencePageCell index positions)
  | index == 0 = first positions
  | otherwise = rest (AtlasSequencePageCell (index - 1) positions)

-- ALIGN: SEQUENCE-PAGE-TOTAL-ORDER.
{-@ reflect sequencePageOrder @-}
sequencePageOrder :: [AtlasSequenceMember] -> Natural -> Ordinal
sequencePageOrder [] _ = finiteOrdinal 0
sequencePageOrder (member : rest) page = addOrdinals (memberPageOrder member page) (sequencePageOrder rest page)

{-@ reflect emptyContains @-}
emptyContains :: AtlasSequencePageCell -> Bool
emptyContains _ = False

{-@ reflect emptyPosition @-}
emptyPosition :: AtlasSequencePageCell -> Ordinal
emptyPosition _ = finiteOrdinal 0

-- ALIGN: SEQUENCE-PAGE-CELL-POSITION.
-- ALIGN: SEQUENCE-PAGE-TRACE-ENCODING.
{-@ reflect sequencePagePosition @-}
{-@ sequencePagePosition :: members:[AtlasSequenceMember] -> page:Natural
      -> {cell:AtlasSequencePageCell | sequencePageContains members page cell} -> Ordinal @-}
{-@ ple sequencePagePosition @-}
sequencePagePosition :: [AtlasSequenceMember] -> Natural -> AtlasSequencePageCell -> Ordinal
sequencePagePosition [] _ = emptyPosition
sequencePagePosition (member : rest) page =
  consPosition (memberPageContains member page) (sequencePageContains rest page)
    (memberPageOrder member page) (sequencePagePosition rest page)

{-@ reflect consPosition @-}
{-@ consPosition :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> Ordinal -> ({cell:AtlasSequencePageCell | rest cell} -> Ordinal)
      -> {cell:AtlasSequencePageCell | consContains first rest cell} -> Ordinal @-}
{-@ ple consPosition @-}
consPosition :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> Ordinal -> (AtlasSequencePageCell -> Ordinal) -> AtlasSequencePageCell -> Ordinal
consPosition _ _ firstOrder restPosition (AtlasSequencePageCell index positions)
  | index == 0 = traceHead positions
  | otherwise = addOrdinals firstOrder (restPosition (AtlasSequencePageCell (index - 1) positions))

{-@ reflect consCell @-}
{-@ consCell :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> Either {positions:[Ordinal] | first positions} {cell:AtlasSequencePageCell | rest cell}
      -> {cell:AtlasSequencePageCell | consContains first rest cell} @-}
{-@ ple consCell @-}
consCell :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> Either [Ordinal] AtlasSequencePageCell -> AtlasSequencePageCell
consCell _ _ (Left positions) = AtlasSequencePageCell 0 positions
consCell _ _ (Right (AtlasSequencePageCell index positions)) = AtlasSequencePageCell (index + 1) positions

{-@ reflect consParts @-}
{-@ consParts :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> {cell:AtlasSequencePageCell | consContains first rest cell}
      -> Either {positions:[Ordinal] | first positions} {cell:AtlasSequencePageCell | rest cell} @-}
{-@ ple consParts @-}
consParts :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> AtlasSequencePageCell -> Either [Ordinal] AtlasSequencePageCell
consParts _ _ (AtlasSequencePageCell index positions)
  | index == 0 = Left positions
  | otherwise = Right (AtlasSequencePageCell (index - 1) positions)

{-@ consPartsRoundTrip :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> parts:Either {positions:[Ordinal] | first positions} {cell:AtlasSequencePageCell | rest cell}
      -> {consParts first rest (consCell first rest parts) == parts} @-}
{-@ ple consPartsRoundTrip @-}
consPartsRoundTrip :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> Either [Ordinal] AtlasSequencePageCell -> ()
consPartsRoundTrip _ _ (Left _) = ()
consPartsRoundTrip _ _ (Right (AtlasSequencePageCell _ _)) = ()

{-@ consCellRoundTrip :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> cell:{AtlasSequencePageCell | consContains first rest cell}
      -> {consCell first rest (consParts first rest cell) == cell} @-}
{-@ ple consCellRoundTrip @-}
consCellRoundTrip :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool) -> AtlasSequencePageCell -> ()
consCellRoundTrip _ _ (AtlasSequencePageCell index _)
  | index == 0 = ()
  | otherwise = ()

{-@ consChain :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> firstChain:{Chain {positions:[Ordinal] | first positions} | chainPosition firstChain == traceHead}
      -> restChain:Chain {cell:AtlasSequencePageCell | rest cell}
      -> {result:Chain {cell:AtlasSequencePageCell | consContains first rest cell} |
           chainOrderType result == addOrdinals (chainOrderType firstChain) (chainOrderType restChain)
           && chainPosition result == consPosition first rest (chainOrderType firstChain) (chainPosition restChain)} @-}
{-@ ple consChain @-}
consChain :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool) -> Chain [Ordinal]
  -> Chain AtlasSequencePageCell -> Chain AtlasSequencePageCell
consChain first rest firstChain restChain =
  let summed = sumChains firstChain restChain
      native = reindexChain (consContains first rest) summed
        (consCell first rest) (consParts first rest)
        (consPartsRoundTrip first rest) (consCellRoundTrip first rest)
  in withChainPosition (consContains first rest) native
       (consPosition first rest (chainOrderType firstChain) (chainPosition restChain))
       (consPositionEquation first rest firstChain restChain summed native)

{-@ consPositionEquation :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> firstChain:{Chain {positions:[Ordinal] | first positions} | chainPosition firstChain == traceHead}
      -> restChain:Chain {cell:AtlasSequencePageCell | rest cell}
      -> summed:{Chain (Either {positions:[Ordinal] | first positions} {cell:AtlasSequencePageCell | rest cell}) |
           chainPosition summed == sumChainPosition firstChain restChain}
      -> native:{Chain {cell:AtlasSequencePageCell | consContains first rest cell} |
           chainPosition native == reindexedPosition (consContains first rest) summed (consParts first rest)}
      -> cell:{AtlasSequencePageCell | consContains first rest cell}
      -> {consPosition first rest (chainOrderType firstChain) (chainPosition restChain) cell == chainPosition native cell} @-}
{-@ ple consPositionEquation @-}
consPositionEquation :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool) -> Chain [Ordinal]
  -> Chain AtlasSequencePageCell -> Chain (Either [Ordinal] AtlasSequencePageCell)
  -> Chain AtlasSequencePageCell -> AtlasSequencePageCell -> ()
consPositionEquation first rest firstChain restChain summed _ cell@(AtlasSequencePageCell index _)
  | index == 0 = equation
  | otherwise = equation
  where
    equation = reindexedPosition (consContains first rest) summed (consParts first rest) cell `seq`
      sumChainPosition firstChain restChain (consParts first rest cell) `seq` ()

{-@ reflect emptyLookup @-}
{-@ emptyLookup :: Ordinal -> Maybe {cell:AtlasSequencePageCell | False} @-}
emptyLookup :: Ordinal -> Maybe AtlasSequencePageCell
emptyLookup _ = Nothing

{-@ emptySurjective :: page:Natural -> position:Ordinal
      -> {chainOrdinalLT position (finiteOrdinal 0)
           => positionMatches (sequencePagePosition [] page) position (emptyLookup position)} @-}
{-@ ple emptySurjective @-}
emptySurjective :: Natural -> Ordinal -> ()
emptySurjective _ (Ordinal []) = ()
emptySurjective _ (Ordinal values@(_ : _)) = coefficientsLT values [] `seq` ()

{-@ emptyBelow :: cell:{AtlasSequencePageCell | emptyContains cell}
      -> {chainOrdinalLT (emptyPosition cell) (finiteOrdinal 0)} @-}
{-@ ple emptyBelow @-}
emptyBelow :: AtlasSequencePageCell -> ()
emptyBelow _ = ()

{-@ emptyInjective :: first:{AtlasSequencePageCell | emptyContains first}
      -> second:{AtlasSequencePageCell | emptyContains second}
      -> {emptyPosition first == emptyPosition second => first == second} @-}
{-@ ple emptyInjective @-}
emptyInjective :: AtlasSequencePageCell -> AtlasSequencePageCell -> ()
emptyInjective _ _ = ()

-- ALIGN: SEQUENCE-PAGE-CHAIN.
-- ALIGN: SEQUENCE-PAGE-LOOKUP.
-- ALIGN: SEQUENCE-PAGE-LOOKUP-BOUNDS.
-- ALIGN: SEQUENCE-PAGE-ORDER-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-PAGE-EQUIVALENCE.
-- ALIGN: SEQUENCE-NATIVE-PAGE-CHAIN.
-- ALIGN: SEQUENCE-NATIVE-PAGE-INTERPRETATION.
{-@ atlasSequencePageChain :: members:[AtlasSequenceMember] -> page:Natural
      -> {result:Chain {cell:AtlasSequencePageCell | sequencePageContains members page cell} |
           chainOrderType result == sequencePageOrder members page
           && chainPosition result == sequencePagePosition members page} / [len members] @-}
{-@ ple atlasSequencePageChain @-}
atlasSequencePageChain :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell
atlasSequencePageChain [] page = chain (finiteOrdinal 0) (sequencePagePosition [] page) emptyLookup
  emptyBelow emptyInjective (emptySurjective page)
atlasSequencePageChain members@(member : rest) page =
  let native = consChain (memberPageContains member page) (sequencePageContains rest page)
        (memberPageChain member page) (atlasSequencePageChain rest page)
  in withChainPosition (consContains (memberPageContains member page) (sequencePageContains rest page))
       native (sequencePagePosition members page)
       (sequencePositionEquation member rest page native)

{-@ reflect sequenceMembersCons @-}
sequenceMembersCons :: AtlasSequenceMember -> [AtlasSequenceMember] -> [AtlasSequenceMember]
sequenceMembersCons member rest = member : rest

{-@ sequencePositionEquation :: member:AtlasSequenceMember -> rest:[AtlasSequenceMember] -> page:Natural
      -> native:{Chain {cell:AtlasSequencePageCell | consContains (memberPageContains member page) (sequencePageContains rest page) cell} |
           chainPosition native == consPosition (memberPageContains member page) (sequencePageContains rest page)
             (memberPageOrder member page) (sequencePagePosition rest page)}
      -> cell:{AtlasSequencePageCell | consContains (memberPageContains member page) (sequencePageContains rest page) cell}
      -> {sequencePagePosition (sequenceMembersCons member rest) page cell == chainPosition native cell} @-}
{-@ ple sequencePositionEquation @-}
sequencePositionEquation :: AtlasSequenceMember -> [AtlasSequenceMember] -> Natural
  -> Chain AtlasSequencePageCell -> AtlasSequencePageCell -> ()
sequencePositionEquation _ _ _ _ (AtlasSequencePageCell _ _) = ()

-- | Compose the member maps while retaining the two canonical trace carriers.
-- ALIGN: SEQUENCE-NATIVE-TRANSITION.
-- ALIGN: SEQUENCE-PAGE-PREVIOUS.
-- ALIGN: SEQUENCE-PAGE-NEXT.
{-@ sequenceTraceTransition :: members:[AtlasSequenceMember] -> page:Natural
      -> {result:OrderedConsolidation
           {cell:AtlasSequencePageCell | sequencePageContains members (page + 1) cell}
           {cell:AtlasSequencePageCell | sequencePageContains members page cell} |
             chainPosition (orderedSource result) == sequencePagePosition members (page + 1)
             && chainPosition (orderedTarget result) == sequencePagePosition members page} / [len members] @-}
{-@ ple sequenceTraceTransition @-}
sequenceTraceTransition :: [AtlasSequenceMember] -> Natural
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
sequenceTraceTransition [] page =
  let source = atlasSequencePageChain [] (page + 1)
      target = atlasSequencePageChain [] page
  in emptyTransition source target
sequenceTraceTransition members@(member : rest) page =
  let sourceFirst = memberPageContains member (page + 1)
      sourceRest = sequencePageContains rest (page + 1)
      targetFirst = memberPageContains member page
      targetRest = sequencePageContains rest page
      first = memberPageTransition member page
        (memberPageChain member (page + 1)) (memberPageChain member page)
      remaining = sequenceTraceTransition rest page
      combined = consTransition sourceFirst sourceRest targetFirst targetRest first remaining
      sourcePositions = sequencePositionEquation member rest (page + 1) (orderedSource combined)
      targetPositions = sequencePositionEquation member rest page (orderedTarget combined)
      source = withChainPosition (consContains sourceFirst sourceRest) (orderedSource combined)
        (sequencePagePosition members (page + 1)) sourcePositions
      target = withChainPosition (consContains targetFirst targetRest) (orderedTarget combined)
        (sequencePagePosition members page) targetPositions
  in withConsolidationEndpoints (consContains sourceFirst sourceRest) (consContains targetFirst targetRest)
       combined source target sourcePositions targetPositions

{-@ consTransition :: sourceFirst:([Ordinal] -> Bool) -> sourceRest:(AtlasSequencePageCell -> Bool)
      -> targetFirst:([Ordinal] -> Bool) -> targetRest:(AtlasSequencePageCell -> Bool)
      -> first:{OrderedConsolidation {positions:[Ordinal] | sourceFirst positions} {positions:[Ordinal] | targetFirst positions} |
           chainPosition (orderedSource first) == traceHead && chainPosition (orderedTarget first) == traceHead}
      -> remaining:OrderedConsolidation {cell:AtlasSequencePageCell | sourceRest cell} {cell:AtlasSequencePageCell | targetRest cell}
      -> {result:OrderedConsolidation
           {cell:AtlasSequencePageCell | consContains sourceFirst sourceRest cell}
           {cell:AtlasSequencePageCell | consContains targetFirst targetRest cell} |
             chainPosition (orderedSource result) == consPosition sourceFirst sourceRest
               (chainOrderType (orderedSource first)) (chainPosition (orderedSource remaining))
             && chainPosition (orderedTarget result) == consPosition targetFirst targetRest
               (chainOrderType (orderedTarget first)) (chainPosition (orderedTarget remaining))} @-}
consTransition :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> OrderedConsolidation [Ordinal] [Ordinal]
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
consTransition sourceFirst sourceRest targetFirst targetRest first remaining =
  let summed = sumConsTransitions sourceFirst sourceRest targetFirst targetRest first remaining
      native = reindexConsolidation (consContains sourceFirst sourceRest) (consContains targetFirst targetRest) summed
        (consCell sourceFirst sourceRest) (consParts sourceFirst sourceRest)
        (consPartsRoundTrip sourceFirst sourceRest) (consCellRoundTrip sourceFirst sourceRest)
        (consCell targetFirst targetRest) (consParts targetFirst targetRest)
        (consPartsRoundTrip targetFirst targetRest) (consCellRoundTrip targetFirst targetRest)
      sourcePositions = consPositionEquation sourceFirst sourceRest
        (orderedSource first) (orderedSource remaining) (orderedSource summed) (orderedSource native)
      targetPositions = consPositionEquation targetFirst targetRest
        (orderedTarget first) (orderedTarget remaining) (orderedTarget summed) (orderedTarget native)
      source = withChainPosition (consContains sourceFirst sourceRest) (orderedSource native)
        (consPosition sourceFirst sourceRest (chainOrderType (orderedSource first)) (chainPosition (orderedSource remaining))) sourcePositions
      target = withChainPosition (consContains targetFirst targetRest) (orderedTarget native)
        (consPosition targetFirst targetRest (chainOrderType (orderedTarget first)) (chainPosition (orderedTarget remaining))) targetPositions
  in withConsolidationEndpoints (consContains sourceFirst sourceRest) (consContains targetFirst targetRest)
       native source target sourcePositions targetPositions

{-@ sumConsTransitions :: sourceFirst:([Ordinal] -> Bool) -> sourceRest:(AtlasSequencePageCell -> Bool)
      -> targetFirst:([Ordinal] -> Bool) -> targetRest:(AtlasSequencePageCell -> Bool)
      -> first:OrderedConsolidation {positions:[Ordinal] | sourceFirst positions} {positions:[Ordinal] | targetFirst positions}
      -> remaining:OrderedConsolidation {cell:AtlasSequencePageCell | sourceRest cell} {cell:AtlasSequencePageCell | targetRest cell}
      -> {result:OrderedConsolidation
           (Either {positions:[Ordinal] | sourceFirst positions} {cell:AtlasSequencePageCell | sourceRest cell})
           (Either {positions:[Ordinal] | targetFirst positions} {cell:AtlasSequencePageCell | targetRest cell}) |
             chainPosition (orderedSource result) == sumChainPosition (orderedSource first) (orderedSource remaining)
             && chainPosition (orderedTarget result) == sumChainPosition (orderedTarget first) (orderedTarget remaining)} @-}
sumConsTransitions :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool)
  -> OrderedConsolidation [Ordinal] [Ordinal]
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
  -> OrderedConsolidation (Either [Ordinal] AtlasSequencePageCell) (Either [Ordinal] AtlasSequencePageCell)
sumConsTransitions _ _ _ _ = sumConsolidations

-- | Retain the actual preceding page as the transition's exact target.
-- ALIGN: SEQUENCE-PAGE-TRANSITION.
-- ALIGN: SEQUENCE-PAGE-TRANSITION-INTERPRETATION.
{-@ sequencePageTransition :: members:[AtlasSequenceMember] -> page:{Natural | page > 0}
      -> target:{Chain {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
           chainPosition target == sequencePagePosition members (page - 1)}
      -> {result:OrderedConsolidation
           {cell:AtlasSequencePageCell | sequencePageContains members page cell}
           {cell:AtlasSequencePageCell | sequencePageContains members (page - 1) cell} |
             chainPosition (orderedSource result) == sequencePagePosition members page
             && orderedTarget result == target} @-}
{-@ ple sequencePageTransition @-}
sequencePageTransition :: [AtlasSequenceMember] -> Natural -> Chain AtlasSequencePageCell
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
sequencePageTransition members page target =
  let mapping = sequenceTraceTransition members (page - 1)
  in withConsolidationEndpoints (sequencePageContains members page) (sequencePageContains members (page - 1))
       mapping (orderedSource mapping) target (const ()) (const ())

{-@ reflect emptyCellMap @-}
{-@ emptyCellMap :: {cell:AtlasSequencePageCell | emptyContains cell}
      -> {cell:AtlasSequencePageCell | emptyContains cell} @-}
emptyCellMap :: AtlasSequencePageCell -> AtlasSequencePageCell
emptyCellMap cell = cell

{-@ emptyInverse :: cell:{AtlasSequencePageCell | emptyContains cell}
      -> {emptyCellMap (emptyCellMap cell) == cell} @-}
{-@ ple emptyInverse @-}
emptyInverse :: AtlasSequencePageCell -> ()
emptyInverse _ = ()

{-@ emptyMonotone :: target:Chain {cell:AtlasSequencePageCell | emptyContains cell}
      -> first:{AtlasSequencePageCell | emptyContains first}
      -> mappedFirst:{AtlasSequencePageCell | emptyContains mappedFirst}
      -> second:{AtlasSequencePageCell | emptyContains second}
      -> {result:AtlasSequencePageCell | emptyContains result && result == emptyCellMap second
           && chainPrecedes target mappedFirst result} @-}
{-@ ple emptyMonotone @-}
emptyMonotone :: Chain AtlasSequencePageCell -> AtlasSequencePageCell -> AtlasSequencePageCell
  -> AtlasSequencePageCell -> AtlasSequencePageCell
emptyMonotone _ _ _ second = second

{-@ emptyTransition :: source:Chain {cell:AtlasSequencePageCell | emptyContains cell}
      -> target:Chain {cell:AtlasSequencePageCell | emptyContains cell}
      -> {result:OrderedConsolidation {cell:AtlasSequencePageCell | emptyContains cell}
           {cell:AtlasSequencePageCell | emptyContains cell} |
             orderedSource result == source && orderedTarget result == target} @-}
emptyTransition :: Chain AtlasSequencePageCell -> Chain AtlasSequencePageCell
  -> OrderedConsolidation AtlasSequencePageCell AtlasSequencePageCell
emptyTransition source target = orderedConsolidation source target
  (restrictedConsolidation emptyContains emptyContains emptyCellMap emptyCellMap
    (emptyMonotone target) emptyInverse)

{-@ headCell :: first:([Ordinal] -> Bool) -> rest:(AtlasSequencePageCell -> Bool)
      -> positions:{[Ordinal] | first positions}
      -> {cell:AtlasSequencePageCell | consContains first rest cell && cell == AtlasSequencePageCell 0 positions} @-}
{-@ ple headCell @-}
headCell :: ([Ordinal] -> Bool) -> (AtlasSequencePageCell -> Bool) -> [Ordinal] -> AtlasSequencePageCell
headCell first rest positions = consCell first rest (Left positions)
