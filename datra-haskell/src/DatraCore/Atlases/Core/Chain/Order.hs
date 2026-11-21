{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The non-strict order of a concrete chain, expressed through its positions.
module Chain.Order (chainPrecedes, reindexedPrecedes) where

import Chain.Internal (Chain, chainPosition, chainOrdinalLT, reindexedPosition)

-- ALIGN: CHAIN-ORDER-PREDICATE.
{-@ reflect chainPrecedes @-}
chainPrecedes :: Chain object -> object -> object -> Bool
chainPrecedes page earlier later =
  not (chainOrdinalLT (chainPosition page later) (chainPosition page earlier))

-- ALIGN: CHAIN-REINDEX-ORDER.
{-@ reindexedPrecedes :: contains:(b -> Bool) -> original:Chain a
      -> backward:({value:b | contains value} -> a)
      -> page:{Chain {value:b | contains value} |
           chainPosition page == reindexedPosition contains original backward}
      -> first:{b | contains first} -> second:{b | contains second}
      -> {chainPrecedes page first second == chainPrecedes original (backward first) (backward second)} @-}
reindexedPrecedes :: (b -> Bool) -> Chain a -> (b -> a) -> Chain b -> b -> b -> ()
reindexedPrecedes contains original backward _ first second =
  reindexedPosition contains original backward first `seq`
    reindexedPosition contains original backward second `seq` ()
