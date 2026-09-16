{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import Natural qualified as Datra
import NumericalOperators.ExponentiationOperator (exponentiationOperator)
import Prelude hiding ((^))

infixr 8 ^

(^)
  :: Datra.Natural baseScope
  -> Datra.Natural exponentScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
