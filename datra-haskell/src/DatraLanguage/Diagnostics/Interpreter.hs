-- | Strongly typed reasons that compilation or evaluation of a Datra AST can
-- fail. Presentation text and locale selection live in the existing
-- diagnostics presentation modules.
module DatraLanguage.Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  ) where

import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

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

data InterpretingError
  = ExpectedNumericalOperand OperandSide InterpretedValueKind
  | ExpectedNaturalExponent InterpretedValueKind
  | ExpectedInsertionOperand InterpretedValueKind
  | RangeConstructionRejected SuperEllipsisRangeError
  | RangeConcatenationRejected SuperEllipsisRangeConcatError
  | AccessRejected AccessError
  | InvalidAsciiStringCharacter Char
  deriving (Eq, Show)
