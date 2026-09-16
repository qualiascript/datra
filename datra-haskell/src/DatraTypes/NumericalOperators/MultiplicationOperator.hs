{-# LANGUAGE RankNTypes #-}

-- | Multiplication of singleton ordinal values.
module NumericalOperators.MultiplicationOperator
  ( multiplicationOperator
  ) where

import DatraOrdinal (multiplyOrdinals)
import NumericalOperators.Internal (applyOrdinalOperator)
import Prelude (Maybe)
import SuperEllipsisValue (SuperEllipsisValue)

-- | Multiply two ordinals at the same super-ellipsis rank. Operand order is
-- significant outside rank one.
multiplicationOperator
  :: SuperEllipsisValue target leftScope
  -> SuperEllipsisValue target rightScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
multiplicationOperator = applyOrdinalOperator multiplyOrdinals
