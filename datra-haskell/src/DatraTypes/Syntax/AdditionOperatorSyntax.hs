{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for ordinal addition.
module Syntax.AdditionOperatorSyntax
  ( (+)
  ) where

import NumericalOperators.AdditionOperator (additionOperator)
import NumericalOperators.NumericalOperand
  ( BinaryNumericalLevel
  , KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalResult
  )
import Prelude hiding ((+))

infixl 6 +

(+)
  :: ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (BinaryNumericalLevel left right)
     )
  => left
  -> right
  -> (forall resultScope.
        NumericalResult left right resultScope -> result)
  -> Maybe result
(+) = additionOperator
