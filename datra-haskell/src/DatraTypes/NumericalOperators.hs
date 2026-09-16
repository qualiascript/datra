-- | Operators for arithmetic on singleton ellipsis naturals.
module NumericalOperators
  ( module NumericalOperators.AdditionOperator
  , module NumericalOperators.MultiplicationOperator
  , module NumericalOperators.ExponentiationOperator
  , (+)
  , (*)
  , (^)
  ) where

import NumericalOperators.AdditionOperator
import NumericalOperators.ExponentiationOperator
import NumericalOperators.MultiplicationOperator
import NumericalOperators.Syntax.AdditionOperatorSyntax ((+))
import NumericalOperators.Syntax.ExponentiationOperatorSyntax ((^))
import NumericalOperators.Syntax.MultiplicationOperatorSyntax ((*))
import Prelude hiding ((+), (*), (^))
