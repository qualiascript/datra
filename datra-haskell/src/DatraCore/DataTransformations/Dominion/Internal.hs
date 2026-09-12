{-# LANGUAGE CPP #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden dominion representation and proof-bearing operations.
module Dominion.Internal
  ( Dominion (..)
  , dominion
  , CountableSet (..)
  , embed
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

{-@
data Dominion a = Dominion
  { rank :: a -> Natural
  , unrank :: Natural -> Maybe a
  , dominionCoherence :: x:a ->
      { proof:() | unrank (rank x) == Just x }
  }
@-}
data Dominion a = Dominion
  { rank   :: a -> Natural
  , unrank :: Natural -> Maybe a
  , dominionCoherence :: a -> ()
  }

-- | Construct a dominion from a total rank, its executable partial inverse,
-- and a proof of the round-trip law. LiquidHaskell checks the proof at every
-- call site.
{-@
dominion
  :: rankFunction:(a -> Natural)
  -> unrankFunction:(Natural -> Maybe a)
  -> (x:a ->
       { proof:() |
           unrankFunction (rankFunction x) == Just x })
  -> Dominion a
@-}
dominion
  :: (a -> Natural)
  -> (Natural -> Maybe a)
  -> (a -> ())
  -> Dominion a
dominion = Dominion

newtype CountableSet a = CountableSet
  { elementAt :: Natural -> Maybe a
  }

embed :: Dominion a -> CountableSet a
embed valueDominion =
  CountableSet
    { elementAt = unrank valueDominion
    }
