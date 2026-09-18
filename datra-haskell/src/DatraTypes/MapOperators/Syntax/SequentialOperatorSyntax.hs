-- | Infix syntax for flattened sequential expansion.
module MapOperators.Syntax.SequentialOperatorSyntax
  ( (<:>)
  ) where

import MapOperators.SequentialOperator
  ( SequentialPresentation
  , SequentialOperatorValues
  , sequentialOperator
  )
import StableConfederalData (StableConfederalData)

-- | Bind more tightly than '<+>', so an unparenthesized mixture first forms
-- its local flattened sequences and then introduces expansion boundaries.
infixr 7 <:>

(<:>)
  :: (SequentialPresentation left, SequentialPresentation right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (SequentialOperatorValues left right)
(<:>) = sequentialOperator
