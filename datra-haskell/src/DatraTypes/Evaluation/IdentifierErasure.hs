-- | Remove one outer identifier wrapper at call and alias boundaries.
module Evaluation.IdentifierErasure
  ( stripOuterIdentifierValue
  , stripOuterIdentifierType
  ) where

import Evaluation.Error (InterpretingError (..))
import Evaluation.Value

-- | Remove one identifier wrapped around the complete value. This does not
-- erase identifiers nested inside an argument map.
stripOuterIdentifierValue
  :: InterpretedValue -> Either InterpretingError InterpretedValue
stripOuterIdentifierValue value = case interpretedForm value of
  AssignmentForm specification
    | isIdentifier (evaluatedSpecificationTarget specification) ->
        Right (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification
    | isIdentifier (evaluatedSpecificationTarget specification) ->
        Right (evaluatedSpecificationSourceValue specification)
  DependentIdentifierTypeForm identifier ->
    Right (evaluatedIdentifierUnderlying identifier)
  _ -> Left (ExpectedTotalAtlasMap (interpretedValueKind value))

-- | Type-level counterpart of 'stripOuterIdentifierValue'.
stripOuterIdentifierType
  :: InterpretedValue -> Either InterpretingError InterpretedValue
stripOuterIdentifierType = stripOuterIdentifierValue

isIdentifier :: InterpretedValue -> Bool
isIdentifier value = case interpretedForm value of
  DependentIdentifierTypeForm _ -> True
  _ -> False
