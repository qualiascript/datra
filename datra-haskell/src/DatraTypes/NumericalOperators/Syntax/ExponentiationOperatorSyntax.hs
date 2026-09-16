{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import EllipsisNatural qualified as Datra
import NumericalOperators.ExponentiationOperator (exponentiationOperator)
import Prelude hiding ((^))

infixr 8 ^

(^)
  :: Datra.EllipsisNatural baseScope
  -> Datra.EllipsisNatural exponentScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
