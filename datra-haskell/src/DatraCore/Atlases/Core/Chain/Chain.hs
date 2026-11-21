{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Public chain API backed by the hidden chain implementation.
module Chain
  ( Chain
  , chainLookup
  , reindexChain
  , reindexedPosition
  , ChainIndex
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainIndex
  , chainIndexOf
  , chainIndexOrderType
  , chainIndexPosition
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , compareInChain
  , hasArrow
  , sumChains
  , spine
  ) where

import Chain.Internal
  ( Chain
  , chainLookup
  , reindexChain
  , reindexedPosition
  , ChainIndex
  , chain
  , chainIndex
  , chainIndexOf
  , chainIndexOrderType
  , chainIndexPosition
  , chainObjectAt
  , chainOrderType
  , chainOrdinalLT
  , chainPosition
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , compareInChain
  , hasArrow
  , positionMatches
  , spine
  )
import Chain.Sum (sumChains)

{-@ opaque-reflect chainPosition @-}
{-@ opaque-reflect chainOrderType @-}
{-@ opaque-reflect chainLookup @-}
{-@ opaque-reflect chainIndexPosition @-}
{-@ opaque-reflect chainIndexOrderType @-}
