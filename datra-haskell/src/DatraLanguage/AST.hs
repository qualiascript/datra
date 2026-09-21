{-# LANGUAGE OverloadedStrings #-}

module DatraLanguage.AST
  ( Expression (..)
  , OperatorExpression (..)
  , toOperatorExpression
  , renderExpression
  , renderOperatorExpression
  , renderAsciiStringLiteral
  ) where

import Data.Char (ord, toUpper)
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  )
import Numeric.Natural (Natural)
import Numeric (showHex)
import Prettyprinter
  ( Doc
  , hsep
  , layoutCompact
  , parens
  , pretty
  )
import Prettyprinter.Render.String (renderString)

-- | Unevaluated Datra syntax. Capabilities and silent coercions are resolved
-- later by the type checker and interpreter, not while constructing the AST.
data Expression
  = EllipsisNatural Natural
  | EllipsisLiteral
  | AsciiStringLiteral String
  | AtlasMap [Expression]
  | MapSequence [Expression]
  | MapExpansion Expression Expression
  | SuperEllipsisRange Expression Expression
  | SuperEllipsisRangePlus Expression
  | SuperEllipsisRangeMinus Expression
  | NaturalRange Natural Natural
  | NaturalRangeUpwards Natural
  | Addition Expression Expression
  | Multiplication Expression Expression
  | Exponentiation Expression Expression
  | MapConcatenation Expression Expression
  | MapAccess Expression Expression
  | MapSpecification Expression Expression
  deriving (Eq, Show)

-- | Lower map notation and render the unevaluated AST using canonical AST
-- operator notation.
renderExpression :: Expression -> String
renderExpression =
  renderOperatorExpression . toOperatorExpression . normalizeExpression

data OperatorExpression
  = NaturalValue Natural
  | EllipsisValue
  | AsciiStringValue String
  | EmptyMap
  | Sequential [OperatorExpression]
  | Expansion OperatorExpression OperatorExpression
  | Range OperatorExpression OperatorExpression
  | RangePlus OperatorExpression
  | RangeMinus OperatorExpression
  | InclusiveNaturalRange Natural Natural
  | InclusiveNaturalRangeUpwards Natural
  | Add OperatorExpression OperatorExpression
  | Multiply OperatorExpression OperatorExpression
  | Power OperatorExpression OperatorExpression
  | Concatenate OperatorExpression OperatorExpression
  | Access OperatorExpression OperatorExpression
  | Specify OperatorExpression OperatorExpression
  deriving (Eq, Show)

toOperatorExpression :: Expression -> OperatorExpression
toOperatorExpression = lower

renderOperatorExpression :: OperatorExpression -> String
renderOperatorExpression =
  renderString . layoutCompact . prettyOperator

normalizeExpression :: Expression -> Expression
normalizeExpression (EllipsisNatural value) = EllipsisNatural value
normalizeExpression EllipsisLiteral = EllipsisLiteral
normalizeExpression (AsciiStringLiteral value) = AsciiStringLiteral value
normalizeExpression (AtlasMap expressions) =
  AtlasMap
    (filter (not . isEmptyMap) (map normalizeExpression expressions))
normalizeExpression (MapSequence expressions) =
  MapSequence
    (filter (not . isEmptyMap) (map normalizeExpression expressions))
normalizeExpression (MapExpansion left right) =
  MapExpansion (normalizeExpression left) (normalizeExpression right)
normalizeExpression (SuperEllipsisRange lowerBound upperBound) =
  SuperEllipsisRange
    (normalizeExpression lowerBound)
    (normalizeExpression upperBound)
normalizeExpression (SuperEllipsisRangePlus lowerBound) =
  SuperEllipsisRangePlus (normalizeExpression lowerBound)
normalizeExpression (SuperEllipsisRangeMinus upperBound) =
  SuperEllipsisRangeMinus (normalizeExpression upperBound)
normalizeExpression (NaturalRange origin target) = NaturalRange origin target
normalizeExpression (NaturalRangeUpwards origin) = NaturalRangeUpwards origin
normalizeExpression (Addition left right) =
  Addition (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Multiplication left right) =
  Multiplication (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Exponentiation left right) =
  Exponentiation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapConcatenation left right) =
  MapConcatenation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapAccess left right) =
  MapAccess (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapSpecification left right) =
  MapSpecification (normalizeExpression left) (normalizeExpression right)

isEmptyMap :: Expression -> Bool
isEmptyMap (AtlasMap []) = True
isEmptyMap (MapSequence []) = True
isEmptyMap _ = False

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower EllipsisLiteral = EllipsisValue
lower (AsciiStringLiteral value) = AsciiStringValue value
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))
lower (MapSequence expressions) = Sequential (map lower expressions)
lower (MapExpansion left right) = Expansion (lower left) (lower right)
lower (SuperEllipsisRange lowerBound upperBound) =
  Range (lower lowerBound) (lower upperBound)
lower (SuperEllipsisRangePlus lowerBound) = RangePlus (lower lowerBound)
lower (SuperEllipsisRangeMinus upperBound) = RangeMinus (lower upperBound)
lower (NaturalRange origin target) = InclusiveNaturalRange origin target
lower (NaturalRangeUpwards origin) = InclusiveNaturalRangeUpwards origin
lower (Addition left right) = Add (lower left) (lower right)
lower (Multiplication left right) = Multiply (lower left) (lower right)
lower (Exponentiation left right) = Power (lower left) (lower right)
lower (MapConcatenation left right) =
  Concatenate (lower left) (lower right)
lower (MapAccess left right) = Access (lower left) (lower right)
lower (MapSpecification left right) = Specify (lower left) (lower right)

data Segment
  = ExpressionSegment [Expression]
  | MapSegment Expression

-- Consecutive expressions occupy one level. Each directly nested map
-- delimits another level, even when that map contains only one expression.
segments :: [Expression] -> [Segment]
segments = go []
  where
    go expressions [] = finishExpressions expressions
    go expressions (nested@(AtlasMap _) : rest) =
      finishExpressions expressions <> (MapSegment nested : go [] rest)
    go expressions (next : rest) = go (next : expressions) rest

    finishExpressions [] = []
    finishExpressions values = [ExpressionSegment (reverse values)]

lowerSegment :: Segment -> OperatorExpression
lowerSegment (ExpressionSegment values) =
  case map lower values of
    [value] -> value
    expressions -> Sequential expressions
lowerSegment (MapSegment expressionValue) = lower expressionValue

combineExpansions :: [OperatorExpression] -> OperatorExpression
combineExpansions [] = EmptyMap
combineExpansions [expressionValue] = expressionValue
combineExpansions (firstExpression : rest) =
  Expansion firstExpression (combineExpansions rest)

prettyOperator :: OperatorExpression -> Doc annotation
prettyOperator (NaturalValue value) = pretty value
prettyOperator EllipsisValue = pretty ellipsisSymbol
prettyOperator (AsciiStringValue value) = pretty (renderAsciiStringLiteral value)
prettyOperator EmptyMap = "[]"
prettyOperator (Sequential []) = "[]"
prettyOperator (Sequential [expressionValue]) = prettyOperator expressionValue
prettyOperator (Sequential expressions) =
  prettyFormFor SequentialOperator (map prettyOperator expressions)
prettyOperator (Expansion left right) =
  prettyBinary ExpansionOperator left right
prettyOperator (Range lowerBound upperBound) =
  prettyBinary RangeOperator lowerBound upperBound
prettyOperator (RangePlus lowerBound) =
  prettyUnary RangePlusOperator lowerBound
prettyOperator (RangeMinus upperBound) =
  prettyUnary RangeMinusOperator upperBound
prettyOperator (InclusiveNaturalRange origin target) =
  prettyForm "from" [pretty origin, "to", pretty target]
prettyOperator (InclusiveNaturalRangeUpwards origin) =
  prettyForm "from" [pretty origin, "upwards"]
prettyOperator (Add left right) =
  prettyBinary AdditionOperator left right
prettyOperator (Multiply left right) =
  prettyBinary MultiplicationOperator left right
prettyOperator (Power left right) =
  prettyBinary ExponentiationOperator left right
prettyOperator (Concatenate left right) =
  prettyBinary ConcatenationOperator left right
prettyOperator (Access left right) =
  prettyBinary AccessOperator left right
prettyOperator (Specify left right) =
  prettyBinary SpecificationOperator left right

prettyUnary
  :: Operator
  -> OperatorExpression
  -> Doc annotation
prettyUnary operator operand =
  prettyFormFor operator [prettyOperator operand]

prettyBinary
  :: Operator
  -> OperatorExpression
  -> OperatorExpression
  -> Doc annotation
prettyBinary operator left right =
  prettyFormFor operator [prettyOperator left, prettyOperator right]

prettyFormFor :: Operator -> [Doc annotation] -> Doc annotation
prettyFormFor operator = prettyForm (operatorCanonicalSymbol operator)

prettyForm :: String -> [Doc annotation] -> Doc annotation
prettyForm headName operands =
  parens (hsep (pretty headName : operands))

-- | Render an identifier string when possible, otherwise use the standard
-- quoted spelling. Standard strings leave the keyboard-visible ASCII range
-- literal and use hexadecimal escapes for every other byte except newline.
renderAsciiStringLiteral :: String -> String
renderAsciiStringLiteral value@(first : rest)
  | isLeadingCanonicalCharacter first
      && all isCanonicalCharacter rest = '$' : value
renderAsciiStringLiteral value = '"' : foldr escape "\"" value
  where
    escape '\n' rest = '\\' : 'n' : rest
    escape '"' rest = '\\' : '"' : rest
    escape '\\' rest = '\\' : '\\' : rest
    escape '#' rest = '\\' : '#' : rest
    escape character rest
      | isAsciiByte character && not (isKeyboardCharacter character) =
          '\\' : hexadecimalByte character <> rest
    escape character rest = character : rest

    hexadecimalByte character =
      case map toUpper (showHex (ord character) "") of
        [digit] -> ['0', digit]
        digits -> digits

    isAsciiByte character = ord character < 256
    isKeyboardCharacter character =
      0x20 <= ord character && ord character <= 0x7e

isLeadingCanonicalCharacter :: Char -> Bool
isLeadingCanonicalCharacter character =
  isAsciiLetter character || character == '_'

isCanonicalCharacter :: Char -> Bool
isCanonicalCharacter character =
  isLeadingCanonicalCharacter character
    || ('0' <= character && character <= '9')
    || character == '\''

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')
