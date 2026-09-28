-- | Optional federation construction for Datra's postfix @?@ operator.
module Evaluation.Optional
  ( makeNothing
  , makeOptionalValue
  ) where

import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError)
import Evaluation.Construction (makeNothing)
import Evaluation.Value

-- | An optional value is definitionally @T | Nothing := ()@. Surface Datra
-- constructs it with @Maybe T@; @?@ is reserved for identifier forms.
makeOptionalValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
makeOptionalValue value = makeEitherValue value makeNothing
