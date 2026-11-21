{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Public dominion API backed by the hidden implementation.
module Dominion
  ( Dominion
  , rank
  , unrank
  , lookupRank
  , lookupRankRoundTrip
  , dominionCoherence
  , dominion
  , MembershipDominion
  , membershipDominion
  , dominionMembership
  , memberDominion
  , CountableSet
  , elementAt
  , embed
  ) where

import Dominion.Internal
  ( CountableSet
  , Dominion
  , MembershipDominion (MembershipDominion)
  , dominionMembership
  , memberDominion
  , dominionCoherence
  , elementAt
  , embed
  , rank
  , unrank
  )

import qualified Dominion.Internal as Internal (dominion)
import Numeric.Natural (Natural)

-- | The exposed constructor retains both supplied executable functions.
-- ALIGN: DOMINION-CONSTRUCTOR-FUNCTIONS.
{-@ dominion :: rankFunction:(a -> Natural) -> unrankFunction:(Natural -> Maybe a)
      -> (value:a -> {unrankFunction (rankFunction value) == Just value})
      -> {result:Dominion a | rank result == rankFunction && unrank result == unrankFunction} @-}
dominion :: (a -> Natural) -> (Natural -> Maybe a) -> (a -> ()) -> Dominion a
dominion = Internal.dominion

-- | Accept a decoder candidate only at its actual forward rank.
-- ALIGN: DOMINION-LOOKUP-RANK.
{-@ reflect lookupRank @-}
{-@ lookupRank :: owner:Dominion a -> index:Natural
      -> Maybe {value:a | rank owner value == index} @-}
lookupRank :: Dominion a -> Natural -> Maybe a
lookupRank owner index = case unrank owner index of
  Just value | rank owner value == index -> Just value
  _ -> Nothing

-- ALIGN: DOMINION-LOOKUP-ROUNDTRIP.
{-@ lookupRankRoundTrip :: owner:Dominion a -> value:a
      -> {lookupRank owner (rank owner value) == Just value} @-}
lookupRankRoundTrip :: Dominion a -> a -> ()
lookupRankRoundTrip owner value = dominionCoherence owner value

{-@ membershipDominion :: accepts:(a -> Bool)
      -> value:Dominion ({datum:a | accepts datum})
      -> {package:MembershipDominion a |
           dominionMembership package == accepts && memberDominion package == value} @-}
-- ALIGN: DOMINION-MEMBERSHIP-PACKAGE.
{-@ reflect membershipDominion @-}
membershipDominion :: (a -> Bool) -> Dominion a -> MembershipDominion a
membershipDominion = MembershipDominion
