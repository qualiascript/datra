-- | Public finite dominion API backed by the hidden implementation.
module FiniteDominion
  ( FiniteDominion
  , FiniteElement
  , FiniteIndex
  , finiteSetDominion
  , finiteAsDominion
  , finiteMember
  , finiteValue
  , finiteCardinality
  , finiteIndex
  , finiteIndexValue
  , finiteRank
  , finiteUnrank
  ) where

import FiniteDominion.Internal
  ( FiniteDominion
  , FiniteElement
  , FiniteIndex
  , finiteAsDominion
  , finiteCardinality
  , finiteIndex
  , finiteIndexValue
  , finiteMember
  , finiteRank
  , finiteSetDominion
  , finiteUnrank
  , finiteValue
  )
