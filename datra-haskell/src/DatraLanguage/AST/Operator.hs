-- | The complete operator vocabulary owned by Datra's abstract syntax.
module DatraLanguage.AST.Operator
  ( Operator (..)
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  , ellipsisSymbol
  ) where

data Operator
  = SequentialOperator
  | ExpansionOperator
  | RangeOperator
  | RangePlusOperator
  | RangeMinusOperator
  | AdditionOperator
  | SubtractionOperator
  | MinusOperator
  | SubfederationOperator
  | EqualityOperator
  | BooleanAndOperator
  | BooleanOrOperator
  | BooleanNotOperator
  | ExtractOperator
  | EvalOperator
  | BeginOperator
  | LetOperator
  | EitherOperator
  | OptionalOperator
  | MultiplicationOperator
  | ExponentiationOperator
  | ConcatenationOperator
  | AccessOperator
  | SpecificationOperator
  | IdentifierTypeOperator
  | AssignmentOperator
  deriving (Eq, Show)

-- | Canonical notation used when rendering an AST.
operatorCanonicalSymbol :: Operator -> String
operatorCanonicalSymbol SequentialOperator = "<:>"
operatorCanonicalSymbol ExpansionOperator = "<+>"
operatorCanonicalSymbol RangeOperator = "<..>"
operatorCanonicalSymbol RangePlusOperator = "..+"
operatorCanonicalSymbol RangeMinusOperator = "..-"
operatorCanonicalSymbol AdditionOperator = "+"
operatorCanonicalSymbol SubtractionOperator = "-"
operatorCanonicalSymbol MinusOperator = "minus"
operatorCanonicalSymbol SubfederationOperator = "of"
operatorCanonicalSymbol EqualityOperator = "="
operatorCanonicalSymbol BooleanAndOperator = "and"
operatorCanonicalSymbol BooleanOrOperator = "or"
operatorCanonicalSymbol BooleanNotOperator = "not"
operatorCanonicalSymbol ExtractOperator = "%"
operatorCanonicalSymbol EvalOperator = "eval"
operatorCanonicalSymbol BeginOperator = "begin"
operatorCanonicalSymbol LetOperator = "let"
operatorCanonicalSymbol EitherOperator = "Either"
operatorCanonicalSymbol OptionalOperator = "optional"
operatorCanonicalSymbol MultiplicationOperator = "*"
operatorCanonicalSymbol ExponentiationOperator = "^"
operatorCanonicalSymbol ConcatenationOperator = "<.>"
operatorCanonicalSymbol AccessOperator = "<@>"
operatorCanonicalSymbol SpecificationOperator = "~>"
operatorCanonicalSymbol IdentifierTypeOperator = ":"
operatorCanonicalSymbol AssignmentOperator = ":="

-- | Concrete source spelling, when an operator is represented by one token.
-- Sequential and expansion structure comes from map separators and nesting.
operatorSourceSymbol :: Operator -> Maybe String
operatorSourceSymbol SequentialOperator = Nothing
operatorSourceSymbol ExpansionOperator = Nothing
operatorSourceSymbol RangeOperator = Just ".."
operatorSourceSymbol RangePlusOperator = Just ".."
operatorSourceSymbol RangeMinusOperator = Just "..-"
operatorSourceSymbol AdditionOperator = Just "+"
operatorSourceSymbol SubtractionOperator = Just "-"
operatorSourceSymbol MinusOperator = Just "-"
operatorSourceSymbol SubfederationOperator = Just "of"
operatorSourceSymbol EqualityOperator = Just "="
operatorSourceSymbol BooleanAndOperator = Just "and"
operatorSourceSymbol BooleanOrOperator = Just "or"
operatorSourceSymbol BooleanNotOperator = Just "not"
operatorSourceSymbol ExtractOperator = Just "%"
operatorSourceSymbol EvalOperator = Just "eval"
operatorSourceSymbol BeginOperator = Just "begin"
operatorSourceSymbol LetOperator = Just "let"
operatorSourceSymbol EitherOperator = Just "|"
operatorSourceSymbol OptionalOperator = Just "?"
operatorSourceSymbol MultiplicationOperator = Just "*"
operatorSourceSymbol ExponentiationOperator = Just "^"
operatorSourceSymbol ConcatenationOperator = Just ","
operatorSourceSymbol AccessOperator = Just "@"
operatorSourceSymbol SpecificationOperator = Just "~>"
operatorSourceSymbol IdentifierTypeOperator = Just ":"
operatorSourceSymbol AssignmentOperator = Just ":="

ellipsisSymbol :: String
ellipsisSymbol = "..."
