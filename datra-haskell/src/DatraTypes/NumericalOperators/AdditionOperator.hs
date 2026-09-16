{-# LANGUAGE RankNTypes #-}

-- | Addition of singleton natural values.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import Natural qualified as Datra
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Add two naturals and introduce the result with a fresh scope.
additionOperator
  :: Datra.Natural leftScope
  -> Datra.Natural rightScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
additionOperator = applyNaturalOperator (Prelude.+)
