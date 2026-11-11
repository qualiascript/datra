-- | Fundamental typing operations for primitive Datra types.
module Evaluation.TypeFamily.Primitive
  ( specifyPrimitiveType
  , decidePrimitiveSubfederation
  ) where

import Evaluation.Error (InterpretingError (ExpectedPrimitiveType))
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Value

specifyPrimitiveType
  :: (InterpretedValue -> InterpretedValue -> Decision ())
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyPrimitiveType decideSubfederation source target =
  case decideSubfederation source target of
    DecisionProved () -> Right source
    _ -> Left ExpectedPrimitiveType

decidePrimitiveSubfederation
  :: InterpretedValue
  -> PrimitiveType
  -> Decision ()
decidePrimitiveSubfederation source target =
  if accepted then DecisionProved () else DecisionRefuted
  where
    accepted = case (interpretedForm source, target) of
      (CoalizationForm operand, expected) ->
        case decidePrimitiveSubfederation operand expected of
          DecisionProved () -> True
          _ -> False
      (_, AnyPrimitive) -> True
      (FunctionBodyForm _, SyntaxPrimitive FunctionBodyAST) -> True
      (_, OrdinalPrimitive) -> isTransfiniteOrdinal
        (interpretedSemantics source)
      (PrimitiveTypeForm actual, expected) | actual == expected -> True
      (PrimitiveTypeForm NatRangePrimitive, IntRangePrimitive) -> True
      (PrimitiveTypeForm NatValRangePrimitive, IntValRangePrimitive) -> True
      (_, NatRangePrimitive) | isPositiveInfinity source -> True
      (_, IntRangePrimitive) | isInfinity source -> True
      (_, NatValRangePrimitive) | isPositiveInfinity source -> True
      (_, IntValRangePrimitive) | isInfinity source -> True
      (NaturalRangeForm _, NatRangePrimitive) -> True
      (NaturalRangeForm _, IntRangePrimitive) -> True
      (IntegerRangeForm _, IntRangePrimitive) -> True
      (RangeForm valueRange, NatRangePrimitive) ->
        evaluatedRangeLevel valueRange == 1
      (RangeForm valueRange, IntRangePrimitive) ->
        evaluatedRangeLevel valueRange <= 2
      (RangeConcatenationForm ranges _, NatRangePrimitive) ->
        all ((== 1) . evaluatedRangeLevel) ranges
      (RangeConcatenationForm ranges _, IntRangePrimitive) ->
        all ((<= 2) . evaluatedRangeLevel) ranges
      (ConcatenatedMapForm left right, expected) ->
        isRange left expected && isRange right expected
      (ValuedNaturalRangeForm _, NatValRangePrimitive) -> True
      (ValuedNaturalRangeForm _, IntValRangePrimitive) -> True
      (ValuedIntegerRangeForm _, IntValRangePrimitive) -> True
      (EitherForm alternatives, NatRangePrimitive) ->
        rangeWithInfinity alternatives NatRangePrimitive
      (EitherForm alternatives, IntRangePrimitive) ->
        rangeWithInfinity alternatives IntRangePrimitive
      (EitherForm alternatives, NatValRangePrimitive) ->
        rangeWithInfinity alternatives NatValRangePrimitive
      (EitherForm alternatives, IntValRangePrimitive) ->
        rangeWithInfinity alternatives IntValRangePrimitive
      _ -> False

    rangeWithInfinity alternatives expected =
      let left = evaluatedEitherLeft alternatives
          right = evaluatedEitherRight alternatives
      in (isInfinity left && isRange right expected)
          || (isRange left expected && isInfinity right)

    isInfinity value =
      case interpretedSemanticResult value of
        CanonicalIntegerLimit _ -> True
        _ -> False

    isPositiveInfinity value =
      interpretedSemanticResult value
        == CanonicalIntegerLimit PositiveInfinity

    isRange value expected =
      case (interpretedForm value, expected) of
        (CoalizationForm operand, _) -> isRange operand expected
        (_, NatRangePrimitive) | isPositiveInfinity value -> True
        (_, IntRangePrimitive) | isInfinity value -> True
        (_, NatValRangePrimitive) | isPositiveInfinity value -> True
        (_, IntValRangePrimitive) | isInfinity value -> True
        (NaturalRangeForm _, NatRangePrimitive) -> True
        (NaturalRangeForm _, IntRangePrimitive) -> True
        (IntegerRangeForm _, IntRangePrimitive) -> True
        (RangeForm valueRange, NatRangePrimitive) ->
          evaluatedRangeLevel valueRange == 1
        (RangeForm valueRange, IntRangePrimitive) ->
          evaluatedRangeLevel valueRange <= 2
        (RangeConcatenationForm ranges _, NatRangePrimitive) ->
          all ((== 1) . evaluatedRangeLevel) ranges
        (RangeConcatenationForm ranges _, IntRangePrimitive) ->
          all ((<= 2) . evaluatedRangeLevel) ranges
        (ConcatenatedMapForm left right, _) ->
          isRange left expected && isRange right expected
        (EitherForm nested, _) -> rangeWithInfinity nested expected
        (ValuedNaturalRangeForm _, NatValRangePrimitive) -> True
        (ValuedNaturalRangeForm _, IntValRangePrimitive) -> True
        (ValuedIntegerRangeForm _, IntValRangePrimitive) -> True
        _ -> False

isTransfiniteOrdinal :: ValueSemantics -> Bool
isTransfiniteOrdinal (PresentedSemantics _ _ semantics) =
  isTransfiniteOrdinal semantics
isTransfiniteOrdinal semantics = case semantics of
  ExplicitSemantics level _ -> level > 1
  FormulationSemantics level -> level > 0
  DependentArgumentTypeSemantics _ underlying _ _ ->
    isTransfiniteOrdinal underlying
  AssignmentSemantics _ _ given -> isTransfiniteOrdinal given
  SpecificationSemantics source _ -> isTransfiniteOrdinal source
  _ -> False
