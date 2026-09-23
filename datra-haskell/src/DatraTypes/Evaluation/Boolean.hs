-- | Datra Boolean values and logical operations.
module Evaluation.Boolean
  ( makeBoolean
  , makeBooleanType
  , subfederationValues
  , equalValues
  , booleanAndValues
  , booleanOrValues
  , booleanNotValue
  , booleanCondition
  ) where

import BooleanType (DatraBoolean (..), booleanNatural)
import DatraOrdinal (naturalAtOrdinal)
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
    semantics =
      IdentifierTypeSemantics
        (SimpleIdentifierDependency
          (case flag of
            DatraFalse -> "False"
            DatraTrue -> "True"))
        (interpretedSemantics underlying)
        True
    value =
      makeSingletonInterpretedValue
        (BooleanForm flag)
        NoInsertion
        (interpretedMap underlying)
        TotalInterpretedMap
        semantics

-- | @Bool@ is definitionally @False := 0 | True := 1@.
makeBooleanType :: Either InterpretingError InterpretedValue
makeBooleanType =
  makeEitherValue (makeBoolean DatraFalse) (makeBoolean DatraTrue)

-- | Boolean existence of the canonical inclusion morphism.
subfederationValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
subfederationValues source target =
  Right (makeBoolean (subfederationFlag source target))

-- | Federation extensional equality is defined directly by mutual @of@.
equalValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
equalValues left right =
  Right
    (makeBoolean
      (datraAnd
        (subfederationFlag left right)
        (subfederationFlag right left)))

subfederationFlag :: InterpretedValue -> InterpretedValue -> DatraBoolean
subfederationFlag source target =
  case decideValueSubfederation source target of
    DecisionProved () -> DatraTrue
    _ -> DatraFalse

datraAnd :: DatraBoolean -> DatraBoolean -> DatraBoolean
datraAnd DatraTrue DatraTrue = DatraTrue
datraAnd _ _ = DatraFalse

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
    IdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString)
        underlying
        True ->
      case underlying of
        ExplicitSemantics 1 ordinalValue
          | identifierString == falseIdentifier
          , naturalAtOrdinal ordinalValue == Just 0 -> Just DatraFalse
          | identifierString == trueIdentifier
          , naturalAtOrdinal ordinalValue == Just 1 -> Just DatraTrue
        _ -> Nothing
    SpecificationSemantics source _ -> booleanFromSemantics source
    _ -> Nothing
  where
    falseIdentifier = "False"
    trueIdentifier = "True"
