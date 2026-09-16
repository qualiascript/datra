{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural addition.
module NumericalOperators.Syntax.AdditionOperatorSyntax
  ( (+)
  ) where

import EllipsisNatural qualified as Datra
import NumericalOperators.AdditionOperator (additionOperator)
import Prelude hiding ((+))

infixl 6 +

(+)
  :: Datra.EllipsisNatural leftScope
  -> Datra.EllipsisNatural rightScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
(+) = additionOperator
