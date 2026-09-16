{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for ordinal addition.
module NumericalOperators.Syntax.AdditionOperatorSyntax
  ( (+)
  ) where

import NumericalOperators.AdditionOperator (additionOperator)
import Prelude hiding ((+))
import SuperEllipsisValue (SuperEllipsisValue)

infixl 6 +

(+)
  :: SuperEllipsisValue target leftScope
  -> SuperEllipsisValue target rightScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
(+) = additionOperator
