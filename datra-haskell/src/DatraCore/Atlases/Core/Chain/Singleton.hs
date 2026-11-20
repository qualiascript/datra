{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | The checked singleton chain shared by Atlas origin constructions.
module Chain.Singleton (singletonChain, singletonChainPosition, chainSingletonPosition) where

import Chain.Internal (Chain, chain, chainOrderType, chainPosition, chainPositionBelow, chainOrdinalLT, positionMatches, chainPositionSurjective, chainLookup)
import DatraOrdinal (Ordinal, finiteOrdinal)
import DatraOrdinal.Laws (ordinalBelowOne, ordinalNotBelowZero, ordinalZeroLeast)

-- | Every value of a singleton chain occupies its least position.
-- ALIGN: CHAIN-UNIQUE-POSITION.
{-@ ple chainSingletonPosition @-}
{-@ chainSingletonPosition :: page:Chain a -> selected:a
      -> unique:(value:a -> {value == selected}) -> value:a
      -> {chainPosition page value == finiteOrdinal 0} @-}
chainSingletonPosition :: Chain a -> a -> (a -> ()) -> a -> ()
chainSingletonPosition page selected unique value =
  chainPositionBelow page selected `seq`
  ordinalNotBelowZero (chainPosition page selected) `seq`
  ordinalZeroLeast (chainOrderType page) `seq`
  chainPositionSurjective page (finiteOrdinal 0) `seq`
    case chainLookup page (finiteOrdinal 0) of
      Nothing -> ()
      Just first -> unique first `seq` unique value

-- ALIGN: CHAIN-SINGLETON.
{-@ opaque-reflect singletonChain @-}
{-@ singletonChain :: {result:Chain () | chainOrderType result == finiteOrdinal 1} @-}
{-@ ple singletonChain @-}
singletonChain :: Chain ()
singletonChain = chain (finiteOrdinal 1) unitPosition unitLookup
  unitBelow (\() () -> ()) unitSurjective

-- ALIGN: CHAIN-SINGLETON-POSITION.
{-@ singletonChainPosition :: value:() -> {chainPosition singletonChain value == finiteOrdinal 0} @-}
{-@ ple singletonChainPosition @-}
singletonChainPosition :: () -> ()
singletonChainPosition value = chainPositionBelow singletonChain value `seq`
  ordinalBelowOne (chainPosition singletonChain value)

{-@ reflect unitPosition @-}
unitPosition :: () -> Ordinal
unitPosition () = finiteOrdinal 0

{-@ reflect unitLookup @-}
unitLookup :: Ordinal -> Maybe ()
unitLookup position = if position == finiteOrdinal 0 then Just () else Nothing

{-@ unitBelow :: value:() -> {chainOrdinalLT (unitPosition value) (finiteOrdinal 1)} @-}
{-@ ple unitBelow @-}
unitBelow :: () -> ()
unitBelow () = ()

{-@ unitSurjective :: position:Ordinal -> {chainOrdinalLT position (finiteOrdinal 1)
      => positionMatches unitPosition position (unitLookup position)} @-}
{-@ ple unitSurjective @-}
unitSurjective :: Ordinal -> ()
unitSurjective position = ordinalBelowOne position `seq`
  case unitLookup position of
    Nothing -> ()
    Just () -> ()

