{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for finite ordinal exponentiation.
module NumericalOperators.Syntax.ExponentiationOperatorSyntax
  ( (^)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.ExponentiationOperator (exponentiationOperator)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalOperandLevel
  , NumericalOperandTarget
  )
import Prelude hiding ((^))
import SuperEllipsisValue (SuperEllipsisValue)

infixr 8 ^

(^)
  :: ( NumericalOperand base
     , KnownSuperEllipsisLevel (NumericalOperandLevel base)
     )
  => base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue
          (NumericalOperandTarget base) resultScope -> result)
  -> Maybe result
(^) = exponentiationOperator
