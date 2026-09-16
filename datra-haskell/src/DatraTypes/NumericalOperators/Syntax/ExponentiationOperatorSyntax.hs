{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for ellipsis-natural exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.ExponentiationOperator (exponentiationOperator)
import Prelude hiding ((^))

infixr 8 ^

(^)
  :: EllipsisNatural baseScope
  -> EllipsisNatural exponentScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
