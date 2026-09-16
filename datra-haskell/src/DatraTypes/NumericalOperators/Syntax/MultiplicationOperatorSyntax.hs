{-# LANGUAGE RankNTypes #-}

-- | Infix syntax for natural multiplication.
module NumericalOperators.Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import EllipsisNatural qualified as Datra
import NumericalOperators.MultiplicationOperator (multiplicationOperator)
import Prelude hiding ((*))

infixl 7 *

(*)
  :: Datra.EllipsisNatural leftScope
  -> Datra.EllipsisNatural rightScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
(*) = multiplicationOperator
