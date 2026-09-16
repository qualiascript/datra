-- | The symmetric monoidal category of stable confederal data
-- and its commutative monads.
module StableConfederalDataMonoidal
  ( EmptyMapValues
  , emptyMap
  , HorizontalSumValues
  , HorizontalSumValue (..)
  , horizontalSumValue
  , horizontalSum
  , horizontalSumHom
  , StableConfederalDataEndofunctor
  , stableConfederalDataEndofunctor
  , mapStableConfederalDataObject
  , mapStableConfederalDataArrow
  , stableConfederalEndofunctorIdentity
  , stableConfederalEndofunctorComposition
  , CommutativeStableConfederalDataMonad
  , commutativeStableConfederalDataMonad
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
import StableConfederalData (EmptyMapValues, emptyMap)
import StableConfederalDataMonoidal.Internal
