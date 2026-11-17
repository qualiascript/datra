-- | The complete operator vocabulary owned by Datra's abstract syntax.
module DatraLanguage.AST.Operator
  ( Operator (..)
  , SourceCharacterOperator (..)
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  , operatorPreferredSymbol
  , sourceOperatorCharacter
  , ellipsisSymbol
  , skipSourceSymbol
  ) where

data Operator
  = FunctionTypeOperator
  | ApplicationOperator
  | DoOperator
  | SequentialOperator
  | ScopeAccessOperator
  | GenericBoundOperator
  | GenericProductOperator
  | ExpansionOperator
  | RangeOperator
  | RangePlusOperator
  | RangeMinusOperator
  | AdditionOperator
  | SubtractionOperator
  | MinusOperator
  | EqualityOperator
  | InequalityOperator
  | LessThanOperator
  | LessThanOrEqualOperator
  | GreaterThanOperator
  | GreaterThanOrEqualOperator
  | CoalizationOperator
  | LookupOperator
  | IdentifierExpressionOperator
  | BeginOperator
  | LetOperator
  | DefOperator
  | ValOperator
  | EitherOperator
  | OptionalOperator
  | MaybeThenOperator
  | MultiplicationOperator
  | ExponentiationOperator
  | ConcatenationOperator
  | AccessOperator
  | SpecificationOperator
  | ReverseSpecificationOperator
  | OverloadOperator
  | ReverseOverloadOperator
  | SafeOverloadOperator
  | ReverseSafeOverloadOperator
  | DependentArgumentTypeOperator
  | AssignmentOperator
  deriving (Bounded, Enum, Eq, Show)

-- | A proof that an operator's concrete source spelling is exactly one
-- character. Consumers which require one character accept this type rather
-- than inspecting the partial source spelling of an arbitrary 'Operator'.
data SourceCharacterOperator
  = SequentialCharacterOperator
  | ScopeAccessCharacterOperator
  | GenericProductCharacterOperator
  | AdditionCharacterOperator
  | SubtractionCharacterOperator
  | MinusCharacterOperator
  | EqualityCharacterOperator
  | LessThanCharacterOperator
  | GreaterThanCharacterOperator
  | LookupCharacterOperator
  | IdentifierExpressionCharacterOperator
  | EitherCharacterOperator
  | OptionalCharacterOperator
  | MultiplicationCharacterOperator
  | ExponentiationCharacterOperator
  | ConcatenationCharacterOperator
  | AccessCharacterOperator
  | DependentArgumentTypeCharacterOperator
  deriving (Bounded, Enum, Eq, Show)

sourceOperatorCharacter :: SourceCharacterOperator -> Char
sourceOperatorCharacter characterOperator = case characterOperator of
  SequentialCharacterOperator -> ';'
  ScopeAccessCharacterOperator -> '.'
  GenericProductCharacterOperator -> '&'
  AdditionCharacterOperator -> '+'
  SubtractionCharacterOperator -> '-'
  MinusCharacterOperator -> '-'
  EqualityCharacterOperator -> '='
  LessThanCharacterOperator -> '<'
  GreaterThanCharacterOperator -> '>'
  LookupCharacterOperator -> '~'
  IdentifierExpressionCharacterOperator -> '$'
  EitherCharacterOperator -> '|'
  OptionalCharacterOperator -> '?'
  MultiplicationCharacterOperator -> '*'
  ExponentiationCharacterOperator -> '^'
  ConcatenationCharacterOperator -> ','
  AccessCharacterOperator -> '@'
  DependentArgumentTypeCharacterOperator -> ':'

-- | Canonical notation used when rendering an AST.
operatorCanonicalSymbol :: Operator -> String
operatorCanonicalSymbol FunctionTypeOperator = "->"
operatorCanonicalSymbol ApplicationOperator = "apply-func"
operatorCanonicalSymbol DoOperator = "do"
operatorCanonicalSymbol SequentialOperator = "<:>"
operatorCanonicalSymbol ScopeAccessOperator = "."
operatorCanonicalSymbol GenericBoundOperator = "::"
operatorCanonicalSymbol GenericProductOperator = "&"
operatorCanonicalSymbol ExpansionOperator = "<+>"
operatorCanonicalSymbol RangeOperator = "<..>"
operatorCanonicalSymbol RangePlusOperator = "..+"
operatorCanonicalSymbol RangeMinusOperator = "..-"
operatorCanonicalSymbol AdditionOperator = "+"
operatorCanonicalSymbol SubtractionOperator = "-"
operatorCanonicalSymbol MinusOperator = "-"
operatorCanonicalSymbol EqualityOperator = "="
operatorCanonicalSymbol InequalityOperator = "=/="
operatorCanonicalSymbol LessThanOperator = "<"
operatorCanonicalSymbol LessThanOrEqualOperator = "<="
operatorCanonicalSymbol GreaterThanOperator = ">"
operatorCanonicalSymbol GreaterThanOrEqualOperator = ">="
operatorCanonicalSymbol CoalizationOperator = "><"
operatorCanonicalSymbol LookupOperator = "~"
operatorCanonicalSymbol IdentifierExpressionOperator = "$"
operatorCanonicalSymbol BeginOperator = "begin"
operatorCanonicalSymbol LetOperator = "let"
operatorCanonicalSymbol DefOperator = "def"
operatorCanonicalSymbol ValOperator = "val"
operatorCanonicalSymbol EitherOperator = "|"
operatorCanonicalSymbol OptionalOperator = "?"
operatorCanonicalSymbol MaybeThenOperator = "maybe-then"
operatorCanonicalSymbol MultiplicationOperator = "*"
operatorCanonicalSymbol ExponentiationOperator = "^"
operatorCanonicalSymbol ConcatenationOperator = "<.>"
operatorCanonicalSymbol AccessOperator = "<@>"
operatorCanonicalSymbol SpecificationOperator = "~>"
operatorCanonicalSymbol ReverseSpecificationOperator = "<~"
operatorCanonicalSymbol OverloadOperator = "<<"
operatorCanonicalSymbol ReverseOverloadOperator = ">>"
operatorCanonicalSymbol SafeOverloadOperator = "<<<"
operatorCanonicalSymbol ReverseSafeOverloadOperator = ">>>"
operatorCanonicalSymbol DependentArgumentTypeOperator = ":"
operatorCanonicalSymbol AssignmentOperator = ":="

-- | Concrete source spelling, when an operator is represented by one token.
-- Sequential and expansion structure comes from map separators and nesting.
operatorSourceSymbol :: Operator -> Maybe String
operatorSourceSymbol FunctionTypeOperator = canonicalSource FunctionTypeOperator
operatorSourceSymbol ApplicationOperator = Nothing
operatorSourceSymbol DoOperator = canonicalSource DoOperator
operatorSourceSymbol SequentialOperator = characterSource SequentialCharacterOperator
operatorSourceSymbol ScopeAccessOperator = characterSource ScopeAccessCharacterOperator
operatorSourceSymbol GenericBoundOperator = canonicalSource GenericBoundOperator
operatorSourceSymbol GenericProductOperator =
  characterSource GenericProductCharacterOperator
operatorSourceSymbol ExpansionOperator = Nothing
operatorSourceSymbol RangeOperator = Just ".."
operatorSourceSymbol RangePlusOperator = Just ".."
operatorSourceSymbol RangeMinusOperator = canonicalSource RangeMinusOperator
operatorSourceSymbol AdditionOperator = characterSource AdditionCharacterOperator
operatorSourceSymbol SubtractionOperator = characterSource SubtractionCharacterOperator
operatorSourceSymbol MinusOperator = characterSource MinusCharacterOperator
operatorSourceSymbol EqualityOperator = characterSource EqualityCharacterOperator
operatorSourceSymbol InequalityOperator = canonicalSource InequalityOperator
operatorSourceSymbol LessThanOperator = characterSource LessThanCharacterOperator
operatorSourceSymbol LessThanOrEqualOperator = canonicalSource LessThanOrEqualOperator
operatorSourceSymbol GreaterThanOperator = characterSource GreaterThanCharacterOperator
operatorSourceSymbol GreaterThanOrEqualOperator =
  canonicalSource GreaterThanOrEqualOperator
operatorSourceSymbol CoalizationOperator = canonicalSource CoalizationOperator
operatorSourceSymbol LookupOperator = characterSource LookupCharacterOperator
operatorSourceSymbol IdentifierExpressionOperator =
  characterSource IdentifierExpressionCharacterOperator
operatorSourceSymbol BeginOperator = canonicalSource BeginOperator
operatorSourceSymbol LetOperator = canonicalSource LetOperator
operatorSourceSymbol DefOperator = canonicalSource DefOperator
operatorSourceSymbol ValOperator = canonicalSource ValOperator
operatorSourceSymbol EitherOperator = characterSource EitherCharacterOperator
operatorSourceSymbol OptionalOperator = characterSource OptionalCharacterOperator
operatorSourceSymbol MaybeThenOperator = Just "!?"
operatorSourceSymbol MultiplicationOperator =
  characterSource MultiplicationCharacterOperator
operatorSourceSymbol ExponentiationOperator =
  characterSource ExponentiationCharacterOperator
operatorSourceSymbol ConcatenationOperator =
  characterSource ConcatenationCharacterOperator
operatorSourceSymbol AccessOperator = characterSource AccessCharacterOperator
operatorSourceSymbol SpecificationOperator = canonicalSource SpecificationOperator
operatorSourceSymbol ReverseSpecificationOperator =
  canonicalSource ReverseSpecificationOperator
operatorSourceSymbol OverloadOperator = canonicalSource OverloadOperator
operatorSourceSymbol ReverseOverloadOperator =
  canonicalSource ReverseOverloadOperator
operatorSourceSymbol SafeOverloadOperator = canonicalSource SafeOverloadOperator
operatorSourceSymbol ReverseSafeOverloadOperator =
  canonicalSource ReverseSafeOverloadOperator
operatorSourceSymbol DependentArgumentTypeOperator =
  characterSource DependentArgumentTypeCharacterOperator
operatorSourceSymbol AssignmentOperator = canonicalSource AssignmentOperator

canonicalSource :: Operator -> Maybe String
canonicalSource = Just . operatorCanonicalSymbol

characterSource :: SourceCharacterOperator -> Maybe String
characterSource = Just . pure . sourceOperatorCharacter

-- | The concrete spelling when one exists, otherwise canonical AST notation.
-- This is total for every operator; callers never need an impossible failure
-- branch merely because they need a printable spelling.
operatorPreferredSymbol :: Operator -> String
operatorPreferredSymbol operator =
  maybe (operatorCanonicalSymbol operator) id (operatorSourceSymbol operator)

ellipsisSymbol :: String
ellipsisSymbol = "..."

-- | The skip atom deliberately shares its spelling with multiplication.
-- Keeping that spelling here lets parsing and rendering agree without making
-- skip pretend to be an operator of its own.
skipSourceSymbol :: String
skipSourceSymbol = [sourceOperatorCharacter MultiplicationCharacterOperator]
