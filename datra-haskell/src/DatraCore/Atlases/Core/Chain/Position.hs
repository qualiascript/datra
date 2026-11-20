{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ qualif PositionAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Choose an extensionally equal position function without changing lookup.
module Chain.Position (withChainPosition) where

import Chain.Internal
  ( Chain, chain, chainPosition, chainLookup, chainOrderType, chainOrdinalLT
  , positionMatches, chainPositionBelow, chainPositionInjective, chainPositionSurjective )
import DatraOrdinal (Ordinal)

-- ALIGN: CHAIN-POSITION-TRANSPORT.
{-@ withChainPosition :: contains:(a -> Bool) -> original:Chain {value:a | contains value} -> position:({value:a | contains value} -> Ordinal)
      -> (value:{a | contains value} -> {position value == chainPosition original value})
      -> {result:Chain {value:a | contains value} | chainPosition result == position
           && chainLookup result == chainLookup original && chainOrderType result == chainOrderType original} @-}
withChainPosition :: (a -> Bool) -> Chain a -> (a -> Ordinal) -> (a -> ()) -> Chain a
withChainPosition contains original position same =
  chain (chainOrderType original) position (chainLookup original)
    (positionBelow contains original position same) (positionInjective contains original position same)
    (positionSurjective contains original position same)

{-@ positionBelow :: contains:(a -> Bool) -> original:Chain {value:a | contains value} -> position:({value:a | contains value} -> Ordinal)
      -> (value:{a | contains value} -> {position value == chainPosition original value})
      -> value:{a | contains value} -> {chainOrdinalLT (position value) (chainOrderType original)} @-}
positionBelow :: (a -> Bool) -> Chain a -> (a -> Ordinal) -> (a -> ()) -> a -> ()
positionBelow _ original _ same value = same value `seq` chainPositionBelow original value

{-@ positionInjective :: contains:(a -> Bool) -> original:Chain {value:a | contains value} -> position:({value:a | contains value} -> Ordinal)
      -> (value:{a | contains value} -> {position value == chainPosition original value})
      -> first:{a | contains first} -> second:{a | contains second} -> {position first == position second => first == second} @-}
positionInjective :: (a -> Bool) -> Chain a -> (a -> Ordinal) -> (a -> ()) -> a -> a -> ()
positionInjective _ original _ same first second =
  same first `seq` same second `seq` chainPositionInjective original first second

{-@ positionSurjective :: contains:(a -> Bool) -> original:Chain {value:a | contains value} -> position:({value:a | contains value} -> Ordinal)
      -> (value:{a | contains value} -> {position value == chainPosition original value})
      -> index:Ordinal -> {chainOrdinalLT index (chainOrderType original)
           => positionMatches position index (chainLookup original index)} @-}
positionSurjective :: (a -> Bool) -> Chain a -> (a -> Ordinal) -> (a -> ()) -> Ordinal -> ()
positionSurjective _ original _ same index =
  chainPositionSurjective original index `seq`
    case chainLookup original index of
      Nothing -> ()
      Just value -> same value
