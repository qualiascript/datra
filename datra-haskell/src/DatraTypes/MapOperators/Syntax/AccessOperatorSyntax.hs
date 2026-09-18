-- | Infix syntax for ordered Atlas access.
module MapOperators.Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import MapOperators.AccessOperator
  ( AccessElement
  , HasOrderedAtlasMap
  , HasSuperEllipsisInsertion
  , InsertionSource
  , IndexedAtlasMap
  , OrderedAtlasElement
  , accessOperator
  )

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: (HasOrderedAtlasMap mapOperand, HasSuperEllipsisInsertion operand)
  => mapOperand
  -> operand
  -> Maybe
       (IndexedAtlasMap
         (AccessElement
           (InsertionSource operand)
           (OrderedAtlasElement mapOperand)))
(<@>) = accessOperator
