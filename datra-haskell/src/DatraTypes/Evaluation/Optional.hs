-- | Optional federation construction for Datra's postfix @?@ operator.
module Evaluation.Optional
  ( makeNothing
  , makeOptionalValue
  ) where

import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError)
import Evaluation.Construction (makeNothing)
import Evaluation.Value

-- | @T?@ is definitionally @T | Nothing := ()@.
makeOptionalValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
makeOptionalValue value = makeEitherValue value makeNothing
