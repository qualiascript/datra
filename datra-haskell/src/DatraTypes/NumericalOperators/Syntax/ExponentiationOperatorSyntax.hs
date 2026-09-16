{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for finite ordinal exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.ExponentiationOperator (exponentiationOperator)
import Prelude hiding ((^))
import SuperEllipsisValue (SuperEllipsisValue)

infixr 8 ^

(^)
  :: SuperEllipsisValue target baseScope
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
