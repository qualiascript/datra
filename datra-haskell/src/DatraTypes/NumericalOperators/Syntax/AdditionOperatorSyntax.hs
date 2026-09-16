{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for ellipsis-natural addition.
module NumericalOperators.Syntax.AdditionOperatorSyntax
  ( (+)
  ) where

import EllipsisNatural (EllipsisNatural)
import NumericalOperators.AdditionOperator (additionOperator)
import Prelude hiding ((+))

infixl 6 +

(+)
  :: EllipsisNatural leftScope
  -> EllipsisNatural rightScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
(+) = additionOperator
