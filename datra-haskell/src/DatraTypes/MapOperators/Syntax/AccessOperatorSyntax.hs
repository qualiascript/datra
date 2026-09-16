-- | Infix syntax for ordered Atlas access.
module MapOperators.Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import EllipsisInsertion (EllipsisInsertion)
import MapOperators.AccessOperator
  ( AccessElement
  , IndexedAtlasMap
  , accessOperator
  )

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: IndexedAtlasMap value
  -> EllipsisInsertion source
  -> Maybe (IndexedAtlasMap (AccessElement source value))
(<@>) = accessOperator
