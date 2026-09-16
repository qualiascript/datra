{-# LANGUAGE RankNTypes #-}

-- | Multiplication of singleton ellipsis naturals.
module NumericalOperators.MultiplicationOperator
  ( multiplicationOperator
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Multiply two ellipsis naturals and introduce the result with a fresh
-- scope.
multiplicationOperator
  :: EllipsisNatural leftScope
  -> EllipsisNatural rightScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
multiplicationOperator = applyNaturalOperator (Prelude.*)
