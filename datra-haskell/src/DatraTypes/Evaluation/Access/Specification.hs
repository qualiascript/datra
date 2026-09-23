-- | Access through the fibers of an evaluated specification morphism.
module Evaluation.Access.Specification
  ( accessSpecification
  ) where

import Evaluation.Error (InterpretingError)
import Evaluation.Specification (specifyValues)
import Evaluation.Value

-- | Select the same ordinal subrange from the source and target, then use the
-- central specification decision procedure to establish the resulting fiber
-- morphism. Keeping this operation in terms of ordinary access makes every
-- selection shape supported by access available to specifications as well.
accessSpecification
  :: ( InterpretedValue
       -> InterpretedValue
       -> Either InterpretingError InterpretedValue
     )
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessSpecification access specification insertion = do
  sourceFiber <-
    access
      (evaluatedSpecificationSourceValue specification)
      insertion
  targetFiber <-
    access
      (evaluatedSpecificationTarget specification)
      insertion
  specifyValues sourceFiber targetFiber
