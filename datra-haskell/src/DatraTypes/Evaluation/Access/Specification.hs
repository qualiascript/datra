-- | Access retained projections or the fibers of an evaluated specification
-- morphism.
module Evaluation.Access.Specification
  ( accessSpecification
  ) where

import Evaluation.Error (InterpretingError)
import Evaluation.Specification.Projection (specificationProjection)
import Evaluation.Specification (contextuallySpecifyValues)
import Evaluation.Value
import BooleanType (DatraBoolean (..))

-- | A specification with retained string-template or dependent-name evidence
-- exposes that evidence as an ordinary indexable value. Otherwise, select the
-- same ordinal subrange from the source and target, then use the central
-- specification decision procedure to establish the resulting fiber morphism.
-- Keeping both paths in terms of ordinary access gives them the same insertion
-- semantics as every other indexable value.
accessSpecification
  :: ( InterpretedValue
       -> InterpretedValue
       -> Either InterpretingError InterpretedValue
     )
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessSpecification access specification insertion = do
  projection <- specificationProjection specification
  case projection of
    Just value -> access value insertion
    Nothing -> do
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
      contextuallySpecifyValues sourceFiber targetFiber

-- An argument-map specification records which ordered target alternative
-- matched this source. Fiber access follows that alternative, retaining the
-- source order instead of indexing the argument map's written target order.
targetPresentation
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
targetPresentation target member =
  case (interpretedForm target, member) of
    (ArgumentMapForm _ underlying, EvaluatedArgumentMapMember _ selected) ->
      selectedAlternative underlying selected
    (ArgumentMapForm _ underlying, _) -> selectedAlternative underlying member
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
