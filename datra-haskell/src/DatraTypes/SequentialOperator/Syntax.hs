-- | Infix syntax for flattened sequential expansion.
module SequentialOperator.Syntax
  ( (<:>)
  ) where

import SequentialOperator
  ( SequentialOperand
  , SequentialOperatorValues
  , sequentialOperator
  )
import StableConfederalData (StableConfederalData)

-- | Associate syntax to the right; the semantic presentation is flattened
-- through either parenthesization.
infixr 6 <:>

(<:>)
  :: (SequentialOperand left, SequentialOperand right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (SequentialOperatorValues left right)
(<:>) = sequentialOperator
