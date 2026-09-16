{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Multiplication of singleton ordinal values.
module NumericalOperators.MultiplicationOperator
  ( multiplicationOperator
  ) where

import DatraOrdinal (multiplyOrdinals)
import NumericalOperators.Internal (applyOrdinalMultiplication)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , MultiplicationNumericalLevel
  , MultiplicationResult
  , NumericalOperand
  )
import Prelude (Maybe)

-- | Multiply two ordinal operands at their least common super-ellipsis rank.
-- Operand order is significant outside rank one.
multiplicationOperator
  :: ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel
         (MultiplicationNumericalLevel left right)
     )
  => left
  -> right
  -> (forall resultScope.
        MultiplicationResult left right resultScope -> result)
  -> Maybe result
multiplicationOperator = applyOrdinalMultiplication multiplyOrdinals
