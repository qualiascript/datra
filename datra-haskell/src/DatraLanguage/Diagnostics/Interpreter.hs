-- | Strongly typed reasons that compilation or evaluation of a Datra AST can
-- fail. Presentation text and locale selection live in the existing
-- diagnostics presentation modules.
module DatraLanguage.Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  , AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  ) where

import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )
import Numeric.Natural (Natural)

data OperandSide = LeftOperand | RightOperand
  deriving (Eq, Show)

data InterpretedValueKind
  = NaturalValueKind
  | ExplicitOrdinalValueKind
  | FormulationValueKind
  | RangeValueKind
  | RangeConcatenationValueKind
  | AsciiStringValueKind
  | MapValueKind
  deriving (Eq, Show)

data AtlasMapFederationOperation
  = AtlasMapFederationConcatenation
  | AtlasMapFederationAccess
  deriving (Eq, Show)

-- | A constructive counterexample proving that a federation operation is
-- invalid, rather than merely beyond the compiler's current proof search.
data AtlasMapFederationRefutation
  = AtlasMapFederationConcatenationCollision Natural
  | AtlasMapFederationAccessHasEmptyCounterexample
  deriving (Eq, Show)

data AtlasMapFederationUncertainty
  = NoAtlasMapFederationDecisionProcedure AtlasMapFederationOperation
  deriving (Eq, Show)

data InterpretingError
  = ExpectedNumericalOperand OperandSide InterpretedValueKind
  | ExpectedNaturalExponent InterpretedValueKind
  | ExpectedInsertionOperand InterpretedValueKind
  | RangeConstructionRejected SuperEllipsisRangeError
  | RangeConcatenationRejected SuperEllipsisRangeConcatError
  | AccessRejected AccessError
  | AtlasMapFederationOperationRefuted AtlasMapFederationRefutation
  | AtlasMapFederationOperationUndecidable AtlasMapFederationUncertainty
  | InvalidAsciiStringCharacter Char
  deriving (Eq, Show)
