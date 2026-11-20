{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif ReindexAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}
{-@ LIQUID "--prune-unsorted" @-}

-- | Hidden chain representation and proof-bearing operations.
module Chain.Internal
  ( Chain
  , ChainIndex (..)
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainLookup
  , chainIndex
  , chainIndexOf
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , reindexChain
  , reindexedPosition
  , compareInChain
  , hasArrow
  , spine
  ) where

import Numeric.Natural (Natural)

import DatraOrdinal (Ordinal, finiteOrdinal, naturalAtOrdinal, omega, ordinalLT)
import DatraOrdinal.Laws
  ( finiteOrdinalBelowOmega, finiteOrdinalInjective
  , naturalAtOrdinalComplete, naturalOrdinalMatches )

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

{-@ reflect chainOrdinalLT @-}
{-@
chainOrdinalLT
  :: left:Ordinal
  -> right:Ordinal
  -> { resultValue:Bool | resultValue == ordinalLT left right }
@-}
chainOrdinalLT :: Ordinal -> Ordinal -> Bool
chainOrdinalLT left right = ordinalLT left right

{-@ reflect positionMatches @-}
positionMatches :: (object -> Ordinal) -> Ordinal -> Maybe object -> Bool
positionMatches _ _ Nothing = False
positionMatches position expected (Just object) = position object == expected

{-@
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainLookup :: Ordinal -> Maybe object
  , chainPositionBelow :: objectValue:object ->
      { proof:() |
          chainOrdinalLT (chainPosition objectValue) chainOrderType }
  , chainPositionInjective :: left:object -> right:object ->
      { proof:() |
          chainPosition left == chainPosition right => left == right }
  , chainPositionSurjective :: position:Ordinal ->
      { proof:() |
          chainOrdinalLT position chainOrderType
            => positionMatches chainPosition position
                 (chainLookup position) }
  }
@-}
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainLookup :: Ordinal -> Maybe object
  , chainPositionBelow :: object -> ()
  , chainPositionInjective :: object -> object -> ()
  , chainPositionSurjective :: Ordinal -> ()
  }

-- | An ordinal certified to index an object of a chain.  Its constructor is
-- hidden by the public module; retaining the object makes elimination total.
{-@
data ChainIndex object = ChainIndex
  { chainIndexOrderType :: Ordinal
  , chainIndexPosition :: {
      position:Ordinal |
      chainOrdinalLT position chainIndexOrderType }
  , chainIndexObject :: object
  }
@-}
data ChainIndex object = ChainIndex
  { chainIndexOrderType :: Ordinal
  , chainIndexPosition :: Ordinal
  , chainIndexObject :: object
  }
  deriving (Eq, Show)

-- | Construct a chain from its indexing equivalence and proofs.
{-@
chain
  :: orderType:Ordinal
  -> position:(object -> Ordinal)
  -> objectAt:(Ordinal -> Maybe object)
  -> (objectValue:object ->
       { proof:() | chainOrdinalLT (position objectValue) orderType })
  -> (left:object -> right:object ->
       { proof:() | position left == position right => left == right })
  -> (ordinalValue:Ordinal ->
       { proof:() |
           chainOrdinalLT ordinalValue orderType
             => positionMatches position ordinalValue
                  (objectAt ordinalValue) })
  -> {result:Chain object | chainOrderType result == orderType
       && chainPosition result == position && chainLookup result == objectAt}
@-}
chain
  :: Ordinal
  -> (object -> Ordinal)
  -> (Ordinal -> Maybe object)
  -> (object -> ())
  -> (object -> object -> ())
  -> (Ordinal -> ())
  -> Chain object
chain = Chain

-- | Transport a chain along an explicitly checked carrier equivalence.
-- ALIGN: CHAIN-REINDEX.
{-@ reindexChain :: targetContains:(b -> Bool) -> source:Chain a -> forward:(a -> {value:b | targetContains value}) -> backward:({value:b | targetContains value} -> a)
      -> (value:a -> {backward (forward value) == value})
      -> (value:{b | targetContains value} -> {forward (backward value) == value})
      -> {result:Chain {value:b | targetContains value} |
           chainOrderType result == chainOrderType source
           && chainPosition result == reindexedPosition targetContains source backward} @-}
reindexChain :: (b -> Bool) -> Chain a -> (a -> b) -> (b -> a) -> (a -> ()) -> (b -> ()) -> Chain b
reindexChain targetContains source forward backward leftInverse rightInverse =
  Chain
    (chainOrderType source)
    (reindexedPosition targetContains source backward)
    (reindexedLookup targetContains source forward)
    (reindexedBelow targetContains source backward)
    (reindexedInjective targetContains source forward backward rightInverse)
    (reindexedSurjective targetContains source forward backward leftInverse)

{-@ reindexedBelow :: targetContains:(b -> Bool) -> source:Chain a -> backward:({value:b | targetContains value} -> a) -> value:{b | targetContains value}
      -> {chainOrdinalLT (reindexedPosition targetContains source backward value) (chainOrderType source)} @-}
reindexedBelow :: (b -> Bool) -> Chain a -> (b -> a) -> b -> ()
reindexedBelow targetContains source backward value = chainPositionBelow source (backward value)

{-@ reindexedInjective :: targetContains:(b -> Bool) -> source:Chain a -> forward:(a -> {value:b | targetContains value}) -> backward:({value:b | targetContains value} -> a)
      -> (value:{b | targetContains value} -> {forward (backward value) == value})
      -> first:{b | targetContains first} -> second:{b | targetContains second}
      -> {reindexedPosition targetContains source backward first == reindexedPosition targetContains source backward second
           => first == second} @-}
reindexedInjective :: (b -> Bool) -> Chain a -> (a -> b) -> (b -> a) -> (b -> ()) -> b -> b -> ()
reindexedInjective targetContains source _ backward rightInverse first second =
  chainPositionInjective source (backward first) (backward second) `seq`
    rightInverse first `seq` rightInverse second

{-@ reindexedPosition :: targetContains:(b -> Bool) -> source:Chain a -> backward:({value:b | targetContains value} -> a) -> {value:b | targetContains value} -> Ordinal @-}
{-@ reflect reindexedPosition @-}
reindexedPosition :: (b -> Bool) -> Chain a -> (b -> a) -> b -> Ordinal
reindexedPosition targetContains source backward value = chainPosition source (backward value)

{-@ reindexedLookup :: targetContains:(b -> Bool) -> source:Chain a -> forward:(a -> {value:b | targetContains value}) -> Ordinal -> Maybe {value:b | targetContains value} @-}
{-@ reflect reindexedLookup @-}
reindexedLookup :: (b -> Bool) -> Chain a -> (a -> b) -> Ordinal -> Maybe b
reindexedLookup targetContains source forward position = case chainLookup source position of
  Nothing -> Nothing
  Just value -> Just (forward value)

{-@ reindexedSurjective :: targetContains:(b -> Bool) -> source:Chain a -> forward:(a -> {value:b | targetContains value}) -> backward:({value:b | targetContains value} -> a)
      -> (value:a -> {backward (forward value) == value})
      -> position:Ordinal
      -> {chainOrdinalLT position (chainOrderType source) =>
           positionMatches (reindexedPosition targetContains source backward) position
             (reindexedLookup targetContains source forward position)} @-}
reindexedSurjective :: (b -> Bool) -> Chain a -> (a -> b) -> (b -> a) -> (a -> ()) -> Ordinal -> ()
reindexedSurjective targetContains source _ _ leftInverse position =
  chainPositionSurjective source position `seq`
    case chainLookup source position of
      Nothing -> ()
      Just value -> leftInverse value

-- | Refine an arbitrary ordinal to an in-bounds chain index.
{-@ reflect chainIndex @-}
{-@
chainIndex
  :: valueChain:Chain object
  -> position:Ordinal
  -> Maybe ({ index:ChainIndex object |
       chainIndexOrderType index == chainOrderType valueChain
       && chainIndexPosition index == position
       && chainOrdinalLT position (chainOrderType valueChain)
       && chainPosition valueChain (chainIndexObject index) == position })
@-}
-- ALIGN: CHAIN-INDEX-LOOKUP.
-- ALIGN: CHAIN-INDEX-ROUNDTRIP.
-- ALIGN: CHAIN-INDEX-BOUNDS.
chainIndex :: Chain object -> Ordinal -> Maybe (ChainIndex object)
chainIndex valueChain position
  | not (chainOrdinalLT position (chainOrderType valueChain)) = Nothing
  | otherwise = case chainPositionSurjective valueChain position of
      () -> case chainLookup valueChain position of
        Nothing -> Nothing
        Just object ->
          Just (ChainIndex (chainOrderType valueChain) position object)

-- | The certified index occupied by an existing chain object.
{-@
chainIndexOf
  :: valueChain:Chain object
  -> objectValue:object
  -> { index:ChainIndex object |
       chainIndexOrderType index == chainOrderType valueChain
       && chainIndexPosition index == chainPosition valueChain objectValue
       && chainIndexObject index == objectValue
       && chainOrdinalLT
            (chainIndexPosition index)
            (chainOrderType valueChain) }
@-}
-- ALIGN: CHAIN-LOOKUP-POSITION.
chainIndexOf :: Chain object -> object -> ChainIndex object
chainIndexOf valueChain objectValue =
  chainPositionBelow valueChain objectValue `seq`
    ChainIndex
      (chainOrderType valueChain)
      (chainPosition valueChain objectValue)
      objectValue

-- | Retrieve the object at a certified chain index.
{-@ reflect chainObjectAt @-}
chainObjectAt :: ChainIndex object -> object
chainObjectAt index = chainIndexObject index

compareInChain :: Chain object -> object -> object -> Ordering
compareInChain valueChain left right =
  compare (chainPosition valueChain left) (chainPosition valueChain right)

hasArrow :: Chain object -> object -> object -> Bool
hasArrow valueChain source target =
  compareInChain valueChain source target /= GT

-- ALIGN: CHAIN-SPINE.
spine :: Chain Natural
spine =
  Chain omega finiteOrdinal naturalAtOrdinal
    finiteOrdinalBelowOmega finiteOrdinalInjective spinePositionSurjective

{-@ spinePositionSurjective :: position:Ordinal
      -> {chainOrdinalLT position omega
           => positionMatches finiteOrdinal position (naturalAtOrdinal position)} @-}
spinePositionSurjective :: Ordinal -> ()
spinePositionSurjective position =
  naturalAtOrdinalComplete position `seq`
    case naturalAtOrdinal position of
      Nothing -> ()
      Just _ -> ()
