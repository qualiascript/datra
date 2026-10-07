-- | The complete operator vocabulary owned by Datra's abstract syntax.
module DatraLanguage.AST.Operator
  ( Operator (..)
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  , ellipsisSymbol
  , skipSourceSymbol
  ) where

data Operator
  = FunctionTypeOperator
  | SyntaxTypeOperator
  | ApplicationOperator
  | DoOperator
  | ExternalOperator
  | SequentialOperator
  | ExpansionOperator
  | RangeOperator
  | RangePlusOperator
  | RangeMinusOperator
  | AdditionOperator
  | SubtractionOperator
  | MinusOperator
  | SubfederationOperator
  | EqualityOperator
  | InequalityOperator
  | LessThanOperator
  | LessThanOrEqualOperator
  | GreaterThanOperator
  | GreaterThanOrEqualOperator
  | BooleanAndOperator
  | BooleanOrOperator
  | BooleanNotOperator
  | CoalizationOperator
  | ValueOfOperator
  | AssertOperator
  | BeginOperator
  | LetOperator
  | EitherOperator
  | OptionalOperator
  | ListUnconsOperator
  | MaybeThenOperator
  | ListMaybeThenOperator
  | MultiplicationOperator
  | ExponentiationOperator
  | ConcatenationOperator
  | AccessOperator
  | SpecificationOperator
  | OverloadOperator
  | ReverseOverloadOperator
  | SafeOverloadOperator
  | ReverseSafeOverloadOperator
  | DependentIdentifierTypeOperator
  | AssignmentOperator
  deriving (Bounded, Enum, Eq, Show)

-- | Canonical notation used when rendering an AST.
operatorCanonicalSymbol :: Operator -> String
operatorCanonicalSymbol FunctionTypeOperator = "->"
operatorCanonicalSymbol SyntaxTypeOperator = "%"
operatorCanonicalSymbol ApplicationOperator = "apply-func"
operatorCanonicalSymbol DoOperator = "do"
operatorCanonicalSymbol ExternalOperator = "!~"
operatorCanonicalSymbol SequentialOperator = "<:>"
operatorCanonicalSymbol ExpansionOperator = "<+>"
operatorCanonicalSymbol RangeOperator = "<..>"
operatorCanonicalSymbol RangePlusOperator = "..+"
operatorCanonicalSymbol RangeMinusOperator = "..-"
operatorCanonicalSymbol AdditionOperator = "+"
operatorCanonicalSymbol SubtractionOperator = "-"
operatorCanonicalSymbol MinusOperator = "-"
operatorCanonicalSymbol SubfederationOperator = "of"
operatorCanonicalSymbol EqualityOperator = "="
operatorCanonicalSymbol InequalityOperator = "=/="
operatorCanonicalSymbol LessThanOperator = "<"
operatorCanonicalSymbol LessThanOrEqualOperator = "<="
operatorCanonicalSymbol GreaterThanOperator = ">"
operatorCanonicalSymbol GreaterThanOrEqualOperator = ">="
operatorCanonicalSymbol BooleanAndOperator = "and"
operatorCanonicalSymbol BooleanOrOperator = "or"
operatorCanonicalSymbol BooleanNotOperator = "not"
operatorCanonicalSymbol CoalizationOperator = "><"
operatorCanonicalSymbol ValueOfOperator = "~"
operatorCanonicalSymbol AssertOperator = "assert"
operatorCanonicalSymbol BeginOperator = "begin"
operatorCanonicalSymbol LetOperator = "let"
operatorCanonicalSymbol EitherOperator = "|"
operatorCanonicalSymbol OptionalOperator = "?"
operatorCanonicalSymbol ListUnconsOperator = "un-cons"
operatorCanonicalSymbol MaybeThenOperator = "maybe-then"
operatorCanonicalSymbol ListMaybeThenOperator = "uncons-maybe-then"
operatorCanonicalSymbol MultiplicationOperator = "*"
operatorCanonicalSymbol ExponentiationOperator = "^"
operatorCanonicalSymbol ConcatenationOperator = "<.>"
operatorCanonicalSymbol AccessOperator = "<@>"
operatorCanonicalSymbol SpecificationOperator = "~>"
operatorCanonicalSymbol OverloadOperator = "<<"
operatorCanonicalSymbol ReverseOverloadOperator = ">>"
operatorCanonicalSymbol SafeOverloadOperator = "<<<"
operatorCanonicalSymbol ReverseSafeOverloadOperator = ">>>"
operatorCanonicalSymbol DependentIdentifierTypeOperator = ":"
operatorCanonicalSymbol AssignmentOperator = ":="

-- | Concrete source spelling, when an operator is represented by one token.
-- Sequential and expansion structure comes from map separators and nesting.
operatorSourceSymbol :: Operator -> Maybe String
operatorSourceSymbol FunctionTypeOperator = Just "->"
operatorSourceSymbol SyntaxTypeOperator = Just "%"
operatorSourceSymbol ApplicationOperator = Nothing
operatorSourceSymbol DoOperator = Just "do"
operatorSourceSymbol ExternalOperator = Just "!~"
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
operatorSourceSymbol InequalityOperator = Just "=/="
operatorSourceSymbol LessThanOperator = Just "<"
operatorSourceSymbol LessThanOrEqualOperator = Just "<="
operatorSourceSymbol GreaterThanOperator = Just ">"
operatorSourceSymbol GreaterThanOrEqualOperator = Just ">="
operatorSourceSymbol BooleanAndOperator = Just "and"
operatorSourceSymbol BooleanOrOperator = Just "or"
operatorSourceSymbol BooleanNotOperator = Just "not"
operatorSourceSymbol CoalizationOperator = Just "><"
operatorSourceSymbol ValueOfOperator = Just "~"
operatorSourceSymbol AssertOperator = Just "assert"
operatorSourceSymbol BeginOperator = Just "begin"
operatorSourceSymbol LetOperator = Just "let"
operatorSourceSymbol EitherOperator = Just "|"
operatorSourceSymbol OptionalOperator = Just "?"
operatorSourceSymbol ListUnconsOperator = Just "!"
operatorSourceSymbol MaybeThenOperator = Just "??"
operatorSourceSymbol ListMaybeThenOperator = Just "!?"
operatorSourceSymbol MultiplicationOperator = Just skipSourceSymbol
operatorSourceSymbol ExponentiationOperator = Just "^"
operatorSourceSymbol ConcatenationOperator = Just ","
operatorSourceSymbol AccessOperator = Just "@"
operatorSourceSymbol SpecificationOperator = Just "~>"
operatorSourceSymbol OverloadOperator = Just "<<"
operatorSourceSymbol ReverseOverloadOperator = Just ">>"
operatorSourceSymbol SafeOverloadOperator = Just "<<<"
operatorSourceSymbol ReverseSafeOverloadOperator = Just ">>>"
operatorSourceSymbol DependentIdentifierTypeOperator = Just ":"
operatorSourceSymbol AssignmentOperator = Just ":="

ellipsisSymbol :: String
ellipsisSymbol = "..."

-- | The skip atom deliberately shares its spelling with multiplication.
-- Keeping that spelling here lets parsing and rendering agree without making
-- skip pretend to be an operator of its own.
skipSourceSymbol :: String
skipSourceSymbol = "*"
