-- | Access through the fibers of an evaluated specification morphism.
module Evaluation.Access.Specification
  ( accessSpecification
  ) where

import Evaluation.Error (InterpretingError)
import Evaluation.Specification (specifyValues)
import Evaluation.Value
import BooleanType (DatraBoolean (..))

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
      (targetPresentation
        (evaluatedSpecificationTarget specification)
        (evaluatedSpecificationMember specification))
      insertion
  specifyValues sourceFiber targetFiber

-- An argument-map specification records which ordered target alternative
-- matched this source. Fiber access follows that alternative, retaining the
-- source order instead of indexing the argument map's written target order.
targetPresentation
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
targetPresentation target member =
  case interpretedForm target of
    ArgumentMapForm _ underlying -> selectedAlternative underlying member
    _ -> target
  where
    selectedAlternative value witness =
      case (interpretedForm value, witness) of
        (EitherForm alternatives, EvaluatedEitherMember side selected) ->
          selectedAlternative
            (case side of
              DatraFalse -> evaluatedEitherLeft alternatives
              DatraTrue -> evaluatedEitherRight alternatives)
            selected
        _ -> value
