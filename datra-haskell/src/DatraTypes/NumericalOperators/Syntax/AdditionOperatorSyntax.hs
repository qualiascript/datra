{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural addition.
module NumericalOperators.Syntax.AdditionOperatorSyntax
  ( (+)
  ) where

import Natural qualified as Datra
import NumericalOperators.AdditionOperator (additionOperator)
import Prelude hiding ((+))

infixl 6 +

(+)
  :: Datra.Natural leftScope
  -> Datra.Natural rightScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
(+) = additionOperator
