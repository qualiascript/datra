{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for ellipsis-natural multiplication.
module NumericalOperators.Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.MultiplicationOperator (multiplicationOperator)
import Prelude hiding ((*))

infixl 7 *

(*)
  :: EllipsisNatural leftScope
  -> EllipsisNatural rightScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
(*) = multiplicationOperator
