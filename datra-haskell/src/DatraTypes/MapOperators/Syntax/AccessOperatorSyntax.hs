-- | Infix syntax for ordered Atlas access.
module MapOperators.Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import MapOperators.AccessOperator
  ( AccessElement
  , AccessOperand
  , AccessSource
  , IndexedAtlasMap
  , accessOperator
  )

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: AccessOperand operand
  => IndexedAtlasMap value
  -> operand
  -> Maybe
       (IndexedAtlasMap (AccessElement (AccessSource operand) value))
(<@>) = accessOperator
