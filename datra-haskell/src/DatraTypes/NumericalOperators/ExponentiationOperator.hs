{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Finite exponentiation of singleton ordinal values.
module NumericalOperators.ExponentiationOperator
  ( exponentiationOperator
  ) where

import DatraOrdinal (powerOrdinal)
import EllipsisNatural (EllipsisNatural)
import NumericalOperators.Internal (applyOrdinalExponentOperator)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalOperandLevel
  , NumericalOperandTarget
  )
import Prelude (Maybe)
import SuperEllipsisValue (SuperEllipsisValue)

-- | Raise an ordinal base to an Ellipsis-natural exponent. The result keeps
-- the base's rank; @0 ^ 0@ is one.
exponentiationOperator
  :: ( NumericalOperand base
     , KnownSuperEllipsisLevel (NumericalOperandLevel base)
     )
  => base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue
          (NumericalOperandTarget base) resultScope -> result)
  -> Maybe result
exponentiationOperator = applyOrdinalExponentOperator powerOrdinal
