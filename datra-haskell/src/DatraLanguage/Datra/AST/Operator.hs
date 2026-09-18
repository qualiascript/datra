-- | The complete operator vocabulary owned by Datra's abstract syntax.
module Datra.AST.Operator
  ( Operator (..)
  , Associativity (..)
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  , operatorFixity
  , ellipsisSymbol
  ) where

data Operator
  = SequentialOperator
  | ExpansionOperator
  | RangeOperator
  | RangePlusOperator
  | RangeMinusOperator
  | AdditionOperator
  | MultiplicationOperator
  | ExponentiationOperator
  | ConcatenationOperator
  | AccessOperator
  deriving (Eq, Show)

data Associativity = AssociateLeft | AssociateRight | AssociateNone
  deriving (Eq, Show)

-- | Canonical notation used when rendering an AST.
operatorCanonicalSymbol :: Operator -> String
operatorCanonicalSymbol SequentialOperator = "<:>"
operatorCanonicalSymbol ExpansionOperator = "<+>"
operatorCanonicalSymbol RangeOperator = "<..>"
operatorCanonicalSymbol RangePlusOperator = "..+"
operatorCanonicalSymbol RangeMinusOperator = "..-"
operatorCanonicalSymbol AdditionOperator = "+"
operatorCanonicalSymbol MultiplicationOperator = "*"
operatorCanonicalSymbol ExponentiationOperator = "^"
operatorCanonicalSymbol ConcatenationOperator = "<.>"
operatorCanonicalSymbol AccessOperator = "<@>"

-- | Concrete source spelling, when an operator is represented by one token.
-- Sequential and expansion structure comes from map separators and nesting.
operatorSourceSymbol :: Operator -> Maybe String
operatorSourceSymbol SequentialOperator = Nothing
operatorSourceSymbol ExpansionOperator = Nothing
operatorSourceSymbol RangeOperator = Just ".."
operatorSourceSymbol RangePlusOperator = Just ".."
operatorSourceSymbol RangeMinusOperator = Just "..-"
operatorSourceSymbol AdditionOperator = Just "+"
operatorSourceSymbol MultiplicationOperator = Just "*"
operatorSourceSymbol ExponentiationOperator = Just "^"
operatorSourceSymbol ConcatenationOperator = Just ","
operatorSourceSymbol AccessOperator = Just "@"

operatorFixity :: Operator -> (Int, Associativity)
operatorFixity SequentialOperator = (7, AssociateRight)
operatorFixity ExpansionOperator = (6, AssociateNone)
operatorFixity RangeOperator = (5, AssociateNone)
operatorFixity RangePlusOperator = (5, AssociateLeft)
operatorFixity RangeMinusOperator = (5, AssociateLeft)
operatorFixity AdditionOperator = (6, AssociateLeft)
operatorFixity MultiplicationOperator = (7, AssociateLeft)
operatorFixity ExponentiationOperator = (8, AssociateRight)
operatorFixity ConcatenationOperator = (7, AssociateRight)
operatorFixity AccessOperator = (8, AssociateLeft)

ellipsisSymbol :: String
ellipsisSymbol = "..."
