{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Addition of singleton ordinal values.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import DatraOrdinal (addOrdinals)
import NumericalOperators.Internal (applyOrdinalOperator)
import NumericalOperators.NumericalOperand
  ( BinaryNumericalLevel
  , KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalResult
  )
import Prelude (Maybe)

-- | Add two ordinal operands at their least common super-ellipsis rank.
additionOperator
  :: ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (BinaryNumericalLevel left right)
     )
  => left
  -> right
  -> (forall resultScope.
        NumericalResult left right resultScope -> result)
  -> Maybe result
additionOperator = applyOrdinalOperator addOrdinals
