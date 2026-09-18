-- | Ordinal arithmetic on singleton super-ellipsis values.
module NumericalOperators
  ( module NumericalOperators.AdditionOperator
  , module NumericalOperators.MultiplicationOperator
  , module NumericalOperators.ExponentiationOperator
  , module NumericalOperators.NumericalOperand
  , (+)
  , (*)
  , (^)
  ) where

import NumericalOperators.AdditionOperator
import NumericalOperators.ExponentiationOperator
import NumericalOperators.MultiplicationOperator
import NumericalOperators.NumericalOperand
import Prelude hiding ((+), (*), (^))
import Syntax.AdditionOperatorSyntax ((+))
import Syntax.ExponentiationOperatorSyntax ((^))
import Syntax.MultiplicationOperatorSyntax ((*))
