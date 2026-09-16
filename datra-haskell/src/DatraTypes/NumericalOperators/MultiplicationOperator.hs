{-# LANGUAGE RankNTypes #-}

-- | Multiplication of singleton natural values.
module NumericalOperators.MultiplicationOperator
  ( multiplicationOperator
  ) where

import EllipsisNatural qualified as Datra
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Multiply two naturals and introduce the result with a fresh
-- scope.
multiplicationOperator
  :: Datra.EllipsisNatural leftScope
  -> Datra.EllipsisNatural rightScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
multiplicationOperator = applyNaturalOperator (Prelude.*)
