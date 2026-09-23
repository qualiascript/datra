-- | Datra Boolean values and logical operations.
module Evaluation.Boolean
  ( makeBoolean
  , makeBooleanType
  , equalValues
  , booleanAndValues
  , booleanOrValues
  , booleanNotValue
  , booleanCondition
  ) where

import BooleanType (DatraBoolean (..), booleanNatural)
import Evaluation.Construction (makeNatural)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Specification.Decision (Decision (DecisionProved))
import Evaluation.Specification.Subfederation (decideValueSubfederation)
import Evaluation.Value

-- | A Boolean is a named, total one-value Atlas. Its canonical form is the
-- corresponding assignment, @False := 0@ or @True := 1@.
makeBoolean :: DatraBoolean -> InterpretedValue
makeBoolean flag = value
  where
    underlying = makeNatural (booleanNatural flag)
    semantics = BooleanSemantics flag (interpretedSemantics underlying)
    value =
      makeSingletonInterpretedValue
        (BooleanForm flag)
        NoInsertion
        (interpretedMap underlying)
        TotalInterpretedMap
        semantics

-- | @Bool@ is definitionally @False := 0 | True := 1@.
makeBooleanType :: InterpretedValue
makeBooleanType =
  makeEitherValue (makeBoolean DatraFalse) (makeBoolean DatraTrue)

-- | Federation extensional equality: both subfederation inclusions must be
-- proved. A refutation or an unavailable proof produces Datra False.
equalValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
equalValues left right =
  Right
    (makeBoolean
      (if proved (decideValueSubfederation left right)
            && proved (decideValueSubfederation right left)
        then DatraTrue
        else DatraFalse))
  where
    proved (DecisionProved ()) = True
    proved _ = False

booleanAndValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
booleanAndValues left right = do
  leftFlag <- requireBoolean LeftOperand left
  rightFlag <- requireBoolean RightOperand right
  pure
    (makeBoolean
      (case (leftFlag, rightFlag) of
        (DatraTrue, DatraTrue) -> DatraTrue
        _ -> DatraFalse))

booleanOrValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
booleanOrValues left right = do
  leftFlag <- requireBoolean LeftOperand left
  rightFlag <- requireBoolean RightOperand right
  pure
    (makeBoolean
      (case (leftFlag, rightFlag) of
        (DatraFalse, DatraFalse) -> DatraFalse
        _ -> DatraTrue))

booleanNotValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
booleanNotValue operand = do
  flag <- requireBoolean LeftOperand operand
  pure
    (makeBoolean
      (case flag of
        DatraFalse -> DatraTrue
        DatraTrue -> DatraFalse))

booleanCondition
  :: InterpretedValue
  -> Either InterpretingError Bool
booleanCondition value =
  case booleanFromSemantics (interpretedSemantics value) of
    Just DatraFalse -> Right False
    Just DatraTrue -> Right True
    Nothing -> Left (ExpectedBooleanCondition (interpretedValueKind value))

requireBoolean
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError DatraBoolean
requireBoolean side value =
  case booleanFromSemantics (interpretedSemantics value) of
    Just flag -> Right flag
    Nothing -> Left (ExpectedBooleanOperand side (interpretedValueKind value))

booleanFromSemantics :: ValueSemantics -> Maybe DatraBoolean
booleanFromSemantics semantics =
  case semantics of
    BooleanSemantics flag _ -> Just flag
    SpecificationSemantics source _ -> booleanFromSemantics source
    _ -> Nothing
