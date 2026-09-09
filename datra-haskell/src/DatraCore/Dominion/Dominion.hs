-- | Public dominion API backed by the hidden implementation.
module Dominion
  ( Dominion
  , rank
  , unrank
  , dominionCoherence
  , dominion
  , CountableSet
  , elementAt
  , embed
  ) where

import Dominion.Internal
  ( CountableSet
  , Dominion
  , dominion
  , dominionCoherence
  , elementAt
  , embed
  , rank
  , unrank
  )
