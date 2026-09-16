-- | Infix syntax for flattened sequential expansion.
module MapOperators.SequentialOperator.Syntax
  ( (<:>)
  ) where

import MapOperators.SequentialOperator
  ( SequentialOperand
  , SequentialOperatorValues
  , sequentialOperator
  )
import StableConfederalData (StableConfederalData)

-- | Bind more tightly than '<+>', so an unparenthesized mixture first forms
-- its local flattened sequences and then introduces expansion boundaries.
infixr 7 <:>

(<:>)
  :: (SequentialOperand left, SequentialOperand right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (SequentialOperatorValues left right)
(<:>) = sequentialOperator
