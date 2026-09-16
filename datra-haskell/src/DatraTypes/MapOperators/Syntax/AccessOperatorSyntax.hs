-- | Infix syntax for ordered Atlas access.
module MapOperators.Syntax.AccessOperatorSyntax
  ( (<@>)
  ) where

import MapOperators.AccessOperator
  ( AccessElement
  , IndexedAtlasMap
  , accessOperator
  )
import SuperEllipsisInsertion (SuperEllipsisInsertion)

infixl 8 <@>

-- | Infix form of 'accessOperator'.
(<@>)
  :: IndexedAtlasMap value
  -> SuperEllipsisInsertion target source
  -> Maybe (IndexedAtlasMap (AccessElement source value))
(<@>) = accessOperator
