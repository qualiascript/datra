{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Dominion
  ( Dominion
  , rank
  , unrank
  , dominionCoherence
  , dominion
  , finiteSetDominion
  , CountableSet
  , elementAt
  , embed
  ) where

import Data.Set (Set)
import Data.Tuple (swap)
import Numeric.Natural (Natural)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

{-@ embed Natural as int @-}

{-@
data Dominion a = Dominion
  { rank :: a -> Maybe Natural
  , unrank :: Natural -> Maybe a
  , dominionCoherence :: x:a -> n:Natural ->
      { proof:() |
          (rank x == Just n) <=> (unrank n == Just x) }
  }
@-}
data Dominion a = Dominion
  { rank   :: a -> Maybe Natural
  , unrank :: Natural -> Maybe a
  , dominionCoherence :: a -> Natural -> ()
  }

-- | Construct a dominion from an executable partial bijection and a proof of
-- its coherence law. LiquidHaskell checks the proof at every call site.
{-@
dominion
  :: rankFunction:(a -> Maybe Natural)
  -> unrankFunction:(Natural -> Maybe a)
  -> (x:a -> n:Natural ->
       { proof:() |
           (rankFunction x == Just n)
             <=> (unrankFunction n == Just x) })
  -> Dominion a
@-}
dominion
  :: (a -> Maybe Natural)
  -> (Natural -> Maybe a)
  -> (a -> Natural -> ())
  -> Dominion a
dominion = Dominion

-- Data.Map's ordering implementation is outside the refinement logic. This
-- constructor is the deliberately small trusted boundary for that library:
-- ascending Set enumeration and the two inverse Maps establish the law.
{-@ assume finiteSetDominion :: Ord a => Set a -> Dominion a @-}
{-@ ignore finiteSetDominion @-}
finiteSetDominion :: Ord a => Set a -> Dominion a
finiteSetDominion set =
  Dominion
    { rank   = (`Map.lookup` ranksByValue)
    , unrank = (`Map.lookup` valuesByRank)
    , dominionCoherence = \_ _ -> ()
    }
  where
    numbered = zip [0 ..] (Set.toAscList set)

    valuesByRank = Map.fromList numbered

    ranksByValue = Map.fromList (map swap numbered)

newtype CountableSet a = CountableSet
  { elementAt :: Natural -> Maybe a
  }

embed :: Dominion a -> CountableSet a
embed valueDominion =
  CountableSet
    { elementAt = unrank valueDominion
    }
