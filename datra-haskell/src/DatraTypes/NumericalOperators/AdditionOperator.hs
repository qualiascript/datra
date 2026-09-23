{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Addition of singleton ordinal values.
module NumericalOperators.AdditionOperator
  ( additionOperator
  ) where

import NumericalOperators.Internal (applyOrdinalAddition)
import NumericalOperators.NumericalOperand
  ( BinaryNumericalLevel
  , KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalResult
  )
import Prelude (Maybe)

-- | Add two ordinal operands at their least common super-ellipsis rank.
-- Adding zero therefore acts as a soft cast to an explicit value.
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
additionOperator = applyOrdinalAddition
