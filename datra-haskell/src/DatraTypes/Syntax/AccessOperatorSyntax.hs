-- | Infix syntax for ordered Atlas access.
module Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import MapOperators.AccessOperator
  ( AccessElement
  , HasOrderedAtlasMap
  , HasSuperEllipsisInsertion
  , InsertionSource
  , OrderedAtlasMap
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
       (OrderedAtlasMap
         (AccessElement
           (InsertionSource operand)
           (OrderedAtlasElement mapOperand)))
(<@>) = accessOperator
