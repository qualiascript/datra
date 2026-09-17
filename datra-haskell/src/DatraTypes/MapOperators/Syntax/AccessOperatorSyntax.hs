-- | Infix syntax for ordered Atlas access.
module MapOperators.Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import MapOperators.AccessOperator
  ( AccessElement
  , AccessMapOperand
  , AccessOperand
  , AccessSource
  , AccessValue
  , IndexedAtlasMap
  , accessOperator
  )

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: (AccessMapOperand mapOperand, AccessOperand operand)
  => mapOperand
  -> operand
  -> Maybe
       (IndexedAtlasMap
         (AccessElement (AccessSource operand) (AccessValue mapOperand)))
(<@>) = accessOperator
