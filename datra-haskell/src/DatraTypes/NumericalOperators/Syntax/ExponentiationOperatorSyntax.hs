{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for finite ordinal exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.ExponentiationOperator
  ( ExponentiationOperand
  , ExponentiationOutput
  , exponentiationOperator
  )
import Prelude hiding ((^))

infixr 8 ^

(^)
  :: ExponentiationOperand base
  => base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        ExponentiationOutput base resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
