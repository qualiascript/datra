-- | Optional federation construction for Datra's postfix @?@ operator.
module Evaluation.Optional
  ( makeNothing
  , makeOptionalValue
  , optionalPresentType
  , justUnderlying
  , optionalUnderlying
  ) where

import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError)
import Evaluation.Construction (makeNothing)
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Value

-- | An optional value is definitionally @Nothing | Just T@.
makeOptionalValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
makeOptionalValue value =
  makeEitherValue makeNothing (simpleIdentifierTypeValue "Just" value)

-- | Recover the tagged present branch of an internal Maybe type.
optionalPresentType :: InterpretedValue -> Maybe InterpretedValue
optionalPresentType value = case interpretedForm value of
  EitherForm alternatives
    | NothingForm <- interpretedForm (evaluatedEitherLeft alternatives)
    , let present = evaluatedEitherRight alternatives
    , Just _ <- justUnderlying present -> Just present
  _ -> Nothing

-- | Forget exactly one @Just@ identifier wrapper. Other assignments retain
-- their names so ordinary named function arguments keep their semantics.
justUnderlying :: InterpretedValue -> Maybe InterpretedValue
justUnderlying value = case interpretedForm value of
  DependentIdentifierTypeForm identifier
    | SimpleIdentifierDependency "Just" <-
        evaluatedIdentifierDependency identifier ->
          Just (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification
    | Just _ <- justUnderlying
        (evaluatedSpecificationTarget specification) ->
          Just (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification
    | Just _ <- justUnderlying
        (evaluatedSpecificationTarget specification) ->
          Just (evaluatedSpecificationSourceValue specification)
  _ -> Nothing

-- | Recover the value type from either a tagged Maybe or the untagged
-- optional shape produced by potentially out-of-bounds map access.
optionalUnderlying :: InterpretedValue -> Maybe InterpretedValue
optionalUnderlying value = case interpretedForm value of
  EitherForm alternatives
    | NothingForm <- interpretedForm (evaluatedEitherLeft alternatives) ->
        let present = evaluatedEitherRight alternatives
        in Just (maybe present id (justUnderlying present))
  _ -> Nothing
