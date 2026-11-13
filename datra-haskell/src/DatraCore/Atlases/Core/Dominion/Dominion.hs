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
  , MembershipDominion
  , membershipDominion
  , dominionMembership
  , memberDominion
  , dominionCoherence
  , elementAt
  , embed
  , rank
  , unrank
  )
