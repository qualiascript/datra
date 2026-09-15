-- | The symmetric monoidal category of stable confederal data transversals
-- and its commutative monads.
module StableConfederalDataTransversalMonoidal
  ( EmptyMapValues
  , emptyMap
  , HorizontalSumValues
  , HorizontalSumValue (..)
  , horizontalSumValue
  , horizontalSum
  , (|+|)
  , horizontalSumHom
  , StableConfederalDataTransversalEndofunctor
  , stableConfederalDataTransversalEndofunctor
  , mapStableConfederalDataTransversalObject
  , mapStableConfederalDataTransversalArrow
  , stableConfederalEndofunctorIdentity
  , stableConfederalEndofunctorComposition
  , CommutativeStableConfederalDataTransversalMonad
  , commutativeStableConfederalDataTransversalMonad
  , stableConfederalReturn
  , stableConfederalFmap
  , stableConfederalJoin
  , stableConfederalBind
  , stableConfederalFubini
  , stableConfederalMonadLeftIdentity
  , stableConfederalMonadRightIdentity
  , stableConfederalMonadAssociativity
  , stableConfederalMonadCommutativity
  ) where

import HorizontalSum
import StableConfederalDataTransversal (EmptyMapValues, emptyMap)
import StableConfederalDataTransversalMonoidal.Internal
