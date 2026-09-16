{-# LANGUAGE RankNTypes #-}

-- | Finite exponentiation of singleton ordinal values.
module NumericalOperators.ExponentiationOperator
  ( exponentiationOperator
  ) where

import DatraOrdinal (powerOrdinal)
import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyOrdinalExponentOperator)
import Prelude (Maybe)
import SuperEllipsisValue (SuperEllipsisValue)

-- | Raise an ordinal base to an Ellipsis-natural exponent. The result keeps
-- the base's rank; @0 ^ 0@ is one.
exponentiationOperator
  :: SuperEllipsisValue target baseScope
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
exponentiationOperator = applyOrdinalExponentOperator powerOrdinal
