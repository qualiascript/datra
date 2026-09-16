{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for ordinal multiplication.
module NumericalOperators.Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import NumericalOperators.MultiplicationOperator (multiplicationOperator)
import Prelude hiding ((*))
import SuperEllipsisValue (SuperEllipsisValue)

infixl 7 *

(*)
  :: SuperEllipsisValue target leftScope
  -> SuperEllipsisValue target rightScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
(*) = multiplicationOperator
