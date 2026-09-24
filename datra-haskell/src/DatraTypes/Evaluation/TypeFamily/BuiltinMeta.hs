-- | Fundamental typing operations for standard-library host meta-types.
module Evaluation.TypeFamily.BuiltinMeta
  ( specifyBuiltinMetaType
  , decideBuiltinMetaSubfederation
  ) where

import Evaluation.Error (InterpretingError (FunctionError))
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.String (federationProducesStrings)
import Evaluation.Value

specifyBuiltinMetaType
  :: (InterpretedValue -> InterpretedValue -> Decision ())
  -> BuiltinMetaType
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyBuiltinMetaType decideSubfederation kind source target =
  case decideSubfederation source target of
    DecisionProved () -> Right source
    _ -> Left (FunctionError ("expected " <> builtinMetaTypeName kind))

decideBuiltinMetaSubfederation
  :: InterpretedValue
  -> BuiltinMetaType
  -> Decision ()
decideBuiltinMetaSubfederation source target =
  if accepted then DecisionProved () else DecisionRefuted
  where
    accepted = case (interpretedForm source, target) of
      (BuiltinMetaTypeForm actual, expected) | actual == expected -> True
      (BuiltinMetaTypeForm (ASTMetaType _), ASTMetaType Nothing) -> True
      (BuiltinMetaTypeForm NatRangeMetaType, IntRangeMetaType) -> True
      (NaturalRangeForm _, NatRangeMetaType) -> True
      (ValuedNaturalRangeForm _, NatRangeMetaType) -> True
      (NaturalRangeForm _, IntRangeMetaType) -> True
      (ValuedNaturalRangeForm _, IntRangeMetaType) -> True
      (IntegerRangeForm _, IntRangeMetaType) -> True
      (ValuedIntegerRangeForm _, IntRangeMetaType) -> True
      (_, StringTemplateMetaType) ->
        federationProducesStrings (interpretedAtlasMapFederation source)
      _ -> False
