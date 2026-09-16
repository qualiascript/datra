-- | Operators for assembling stable-confederal data into map presentations.
module MapOperators
  ( module MapOperators.AccessOperator
  , module MapOperators.SequentialOperator
  , module MapOperators.ExpansionOperator
  , module MapOperators.ConcatOperator
  , (<@>)
  , (<.>)
  , (<:>)
  , (<+>)
  ) where

import MapOperators.AccessOperator
import MapOperators.ConcatOperator
import MapOperators.ExpansionOperator
import MapOperators.SequentialOperator
import MapOperators.Syntax.AccessOperatorSyntax ((<@>))
import MapOperators.Syntax.ConcatOperatorSyntax ((<.>))
import MapOperators.Syntax.ExpansionOperatorSyntax ((<+>))
import MapOperators.Syntax.SequentialOperatorSyntax ((<:>))
