{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Public dominion API backed by the hidden implementation.
module Dominion
  ( Dominion
  , rank
  , unrank
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
  , dominion
  , MembershipDominion (MembershipDominion)
  , dominionMembership
  , memberDominion
  , dominionCoherence
  , elementAt
  , embed
  , rank
  , unrank
  )

{-@ membershipDominion :: accepts:(a -> Bool)
      -> value:Dominion ({datum:a | accepts datum})
      -> {package:MembershipDominion a |
           dominionMembership package == accepts && memberDominion package == value} @-}
-- ALIGN: DOMINION-MEMBERSHIP-PACKAGE.
{-@ reflect membershipDominion @-}
membershipDominion :: (a -> Bool) -> Dominion a -> MembershipDominion a
membershipDominion = MembershipDominion
