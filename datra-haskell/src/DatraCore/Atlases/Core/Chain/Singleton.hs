{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | The checked singleton chain shared by Atlas origin constructions.
module Chain.Singleton (singletonChain) where

import Chain.Internal (Chain, chain, chainOrderType, chainOrdinalLT, positionMatches)
import DatraOrdinal.Internal (Ordinal, finiteOrdinal)
import DatraOrdinal.Laws (ordinalBelowOne)

-- ALIGN: CHAIN-SINGLETON.
{-@ singletonChain :: {result:Chain () | chainOrderType result == finiteOrdinal 1} @-}
{-@ ple singletonChain @-}
singletonChain :: Chain ()
singletonChain = chain (finiteOrdinal 1) unitPosition unitLookup
  unitBelow (\() () -> ()) unitSurjective

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

