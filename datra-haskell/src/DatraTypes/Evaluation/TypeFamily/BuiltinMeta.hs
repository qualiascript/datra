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
      (CoalizationForm operand, expected) ->
        case decideBuiltinMetaSubfederation operand expected of
          DecisionProved () -> True
          _ -> False
      (_, AnyMetaType) ->
        case datraCanonicalType (interpretedDatraType source) of
          Just _ -> True
          Nothing -> False
      (_, OrdinalMetaType) -> isTransfiniteOrdinal
        (interpretedSemantics source)
      (BuiltinMetaTypeForm actual, expected) | actual == expected -> True
      (BuiltinMetaTypeForm (ASTMetaType _), ASTMetaType Nothing) -> True
      (BuiltinMetaTypeForm NatRangeMetaType, IntRangeMetaType) -> True
      (BuiltinMetaTypeForm NatValRangeMetaType, IntValRangeMetaType) -> True
      (_, NatRangeMetaType) | isPositiveInfinity source -> True
      (_, IntRangeMetaType) | isInfinity source -> True
      (_, NatValRangeMetaType) | isPositiveInfinity source -> True
      (_, IntValRangeMetaType) | isInfinity source -> True
      (NaturalRangeForm _, NatRangeMetaType) -> True
      (NaturalRangeForm _, IntRangeMetaType) -> True
      (IntegerRangeForm _, IntRangeMetaType) -> True
      (RangeForm valueRange, NatRangeMetaType) ->
        evaluatedRangeLevel valueRange == 1
      (RangeForm valueRange, IntRangeMetaType) ->
        evaluatedRangeLevel valueRange <= 2
      (RangeConcatenationForm ranges _, NatRangeMetaType) ->
        all ((== 1) . evaluatedRangeLevel) ranges
      (RangeConcatenationForm ranges _, IntRangeMetaType) ->
        all ((<= 2) . evaluatedRangeLevel) ranges
      (ConcatenatedMapForm left right, expected) ->
        isRange left expected && isRange right expected
      (ValuedNaturalRangeForm _, NatValRangeMetaType) -> True
      (ValuedNaturalRangeForm _, IntValRangeMetaType) -> True
      (ValuedIntegerRangeForm _, IntValRangeMetaType) -> True
      (EitherForm alternatives, NatRangeMetaType) ->
        rangeWithInfinity alternatives NatRangeMetaType
      (EitherForm alternatives, IntRangeMetaType) ->
        rangeWithInfinity alternatives IntRangeMetaType
      (EitherForm alternatives, NatValRangeMetaType) ->
        rangeWithInfinity alternatives NatValRangeMetaType
      (EitherForm alternatives, IntValRangeMetaType) ->
        rangeWithInfinity alternatives IntValRangeMetaType
      (_, StringTemplateMetaType) ->
        federationProducesStrings (interpretedAtlasMapFederation source)
      _ -> False

    rangeWithInfinity alternatives expected =
      let left = evaluatedEitherLeft alternatives
          right = evaluatedEitherRight alternatives
      in (isInfinity left && isRange right expected)
          || (isRange left expected && isInfinity right)

    isInfinity value =
      interpretedCanonicalResult value == CanonicalAsciiString "PosInf"
        || interpretedCanonicalResult value == CanonicalAsciiString "NegInf"

    isPositiveInfinity value =
      interpretedCanonicalResult value == CanonicalAsciiString "PosInf"

    isRange value expected =
      case (interpretedForm value, expected) of
        (CoalizationForm operand, _) -> isRange operand expected
        (_, NatRangeMetaType) | isPositiveInfinity value -> True
        (_, IntRangeMetaType) | isInfinity value -> True
        (_, NatValRangeMetaType) | isPositiveInfinity value -> True
        (_, IntValRangeMetaType) | isInfinity value -> True
        (NaturalRangeForm _, NatRangeMetaType) -> True
        (NaturalRangeForm _, IntRangeMetaType) -> True
        (IntegerRangeForm _, IntRangeMetaType) -> True
        (RangeForm valueRange, NatRangeMetaType) ->
          evaluatedRangeLevel valueRange == 1
        (RangeForm valueRange, IntRangeMetaType) ->
          evaluatedRangeLevel valueRange <= 2
        (RangeConcatenationForm ranges _, NatRangeMetaType) ->
          all ((== 1) . evaluatedRangeLevel) ranges
        (RangeConcatenationForm ranges _, IntRangeMetaType) ->
          all ((<= 2) . evaluatedRangeLevel) ranges
        (ConcatenatedMapForm left right, _) ->
          isRange left expected && isRange right expected
        (EitherForm nested, _) -> rangeWithInfinity nested expected
        (ValuedNaturalRangeForm _, NatValRangeMetaType) -> True
        (ValuedNaturalRangeForm _, IntValRangeMetaType) -> True
        (ValuedIntegerRangeForm _, IntValRangeMetaType) -> True
        _ -> False

isTransfiniteOrdinal :: ValueSemantics -> Bool
isTransfiniteOrdinal semantics = case semantics of
  ExplicitSemantics level _ -> level > 1
  FormulationSemantics level -> level > 0
  DependentIdentifierTypeSemantics _ underlying _ ->
    isTransfiniteOrdinal underlying
  AssignmentSemantics _ _ given -> isTransfiniteOrdinal given
  SpecificationSemantics source _ -> isTransfiniteOrdinal source
  _ -> False
