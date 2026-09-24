-- | Fundamental typing operations for standard-library host meta-types.
module Evaluation.TypeFamily.BuiltinMeta
  ( specifyBuiltinMetaType
  , decideBuiltinMetaSubfederation
  ) where

import Evaluation.Error (InterpretingError (ExpectedBuiltinType))
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
    _ -> Left (ExpectedBuiltinType (builtinMetaTypeName kind))

decideBuiltinMetaSubfederation
  :: InterpretedValue
  -> BuiltinMetaType
  -> Decision ()
decideBuiltinMetaSubfederation source target =
  if accepted then DecisionProved () else DecisionRefuted
  where
    accepted = case (interpretedForm source, target) of
      (_, AnyMetaType) ->
        case datraCanonicalType (interpretedDatraType source) of
          Just _ -> True
          Nothing -> False
      (BuiltinMetaTypeForm actual, expected) | actual == expected -> True
      (BuiltinMetaTypeForm (ASTMetaType _), ASTMetaType Nothing) -> True
      (BuiltinMetaTypeForm NatRangeMetaType, IntRangeMetaType) -> True
      (BuiltinMetaTypeForm NatValRangeMetaType, IntValRangeMetaType) -> True
      (NaturalRangeForm _, NatRangeMetaType) -> True
      (NaturalRangeForm _, IntRangeMetaType) -> True
      (IntegerRangeForm _, IntRangeMetaType) -> True
      (ValuedNaturalRangeForm _, NatValRangeMetaType) -> True
      (ValuedNaturalRangeForm _, IntValRangeMetaType) -> True
      (ValuedIntegerRangeForm _, IntValRangeMetaType) -> True
      (_, StringTemplateMetaType) ->
        federationProducesStrings (interpretedAtlasMapFederation source)
      _ -> False
