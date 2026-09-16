{-# LANGUAGE RankNTypes #-}

-- | Addition of singleton ordinal values.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import DatraOrdinal (addOrdinals)
import NumericalOperators.Internal (applyOrdinalOperator)
import Prelude (Maybe)
import SuperEllipsisValue (SuperEllipsisValue)

-- | Add two ordinals at the same super-ellipsis rank and introduce the result
-- with a fresh scope. At rank one the result is an 'EllipsisNatural'.
additionOperator
  :: SuperEllipsisValue target leftScope
  -> SuperEllipsisValue target rightScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
additionOperator = applyOrdinalOperator addOrdinals
