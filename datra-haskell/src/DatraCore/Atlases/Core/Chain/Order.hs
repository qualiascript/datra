{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | The non-strict order of a concrete chain, expressed through its positions.
module Chain.Order (chainPrecedes) where

import Chain (Chain, chainPosition, chainOrdinalLT)

-- ALIGN: CHAIN-ORDER-PREDICATE.
{-@ reflect chainPrecedes @-}
chainPrecedes :: Chain object -> object -> object -> Bool
chainPrecedes page earlier later =
  not (chainOrdinalLT (chainPosition page later) (chainPosition page earlier))
