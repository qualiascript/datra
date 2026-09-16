{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural multiplication.
module NumericalOperators.Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import Natural qualified as Datra
import NumericalOperators.MultiplicationOperator (multiplicationOperator)
import Prelude hiding ((*))

infixl 7 *

(*)
  :: Datra.Natural leftScope
  -> Datra.Natural rightScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
(*) = multiplicationOperator
