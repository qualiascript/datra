-- | Infix syntax for an explicit non-associative grouping boundary.
module MapOperators.Syntax.ExpansionOperatorSyntax
  ( (<+>)
  ) where

import MapOperators.ExpansionOperator
  ( ExpansionOperatorValues
  , expansionOperator
  )
import StableConfederalData (StableConfederalData)

-- | Group two operands without flattening across this node.
infix 6 <+>

(<+>)
  :: StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (ExpansionOperatorValues left right)
(<+>) = expansionOperator
