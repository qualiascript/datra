{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Infix syntax for ordinal multiplication.
module Syntax.MultiplicationOperatorSyntax
  ( (*)
  ) where

import NumericalOperators.MultiplicationOperator
  ( MultiplicationOperands
  , MultiplicationOutput
  , multiplicationOperator
  )
import Prelude hiding ((*))

infixl 7 *

(*)
  :: MultiplicationOperands left right
  => left
  -> right
  -> (forall resultScope.
        MultiplicationOutput left right resultScope -> result)
  -> Maybe result
(*) = multiplicationOperator
