{-# LANGUAGE RankNTypes #-}

-- | Exponentiation of singleton natural values.
module NumericalOperators.ExponentiationOperator
  ( exponentiationOperator
  ) where

import Natural qualified as Datra
import NumericalOperators.Internal (applyNaturalOperator)
import Prelude (Maybe)

import qualified Prelude

-- | Raise the first natural to the power of the second and introduce
-- the result with a fresh scope. As for 'Prelude.^', @0 ^ 0@ is @1@.
exponentiationOperator
  :: Datra.Natural baseScope
  -> Datra.Natural exponentScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
exponentiationOperator = applyNaturalOperator (Prelude.^)
