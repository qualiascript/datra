{-# LANGUAGE RankNTypes #-}

-- | Multiplication of singleton natural values.
module NumericalOperators.MultiplicationOperator
  ( multiplicationOperator
  ) where

import Natural qualified as Datra
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Multiply two naturals and introduce the result with a fresh
-- scope.
multiplicationOperator
  :: Datra.Natural leftScope
  -> Datra.Natural rightScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
multiplicationOperator = applyNaturalOperator (Prelude.*)
