{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for ordinal multiplication.
module NumericalOperators.Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import NumericalOperators.MultiplicationOperator (multiplicationOperator)
import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , MultiplicationNumericalLevel
  , MultiplicationResult
  , NumericalOperand
  )
import Prelude hiding ((*))

infixl 7 *

(*)
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
(*) = multiplicationOperator
