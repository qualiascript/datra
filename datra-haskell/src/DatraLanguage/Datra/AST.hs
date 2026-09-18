module Datra.AST
  ( Expression (..)
  , OperatorExpression (..)
  , toOperatorExpression
  , renderExpression
  , renderOperatorExpression
  ) where

import Data.List (intercalate)
import Datra.AST.Operator
  ( Associativity (..)
  , Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorFixity
  )
import Numeric.Natural (Natural)

-- | Unevaluated Datra syntax. Capabilities and silent coercions are resolved
-- later by the type checker and interpreter, not while constructing the AST.
data Expression
  = EllipsisNatural Natural
  | EllipsisLiteral
  | AtlasMap [Expression]
  | MapSequence [Expression]
  | MapExpansion Expression Expression
  | SuperEllipsisRange Expression Expression
  | SuperEllipsisRangePlus Expression
  | SuperEllipsisRangeMinus Expression
  | Addition Expression Expression
  | Multiplication Expression Expression
  | Exponentiation Expression Expression
  | MapConcatenation Expression Expression
  | MapAccess Expression Expression
  deriving (Eq, Show)

-- | Lower map notation and render the unevaluated AST using canonical AST
-- operator notation.
renderExpression :: Expression -> String
renderExpression =
  renderOperatorExpression . toOperatorExpression . normalizeExpression

data OperatorExpression
  = NaturalValue Natural
  | EllipsisValue
  | EmptyMap
  | Sequential [OperatorExpression]
  | Expansion OperatorExpression OperatorExpression
  | Range OperatorExpression OperatorExpression
  | RangePlus OperatorExpression
  | RangeMinus OperatorExpression
  | Add OperatorExpression OperatorExpression
  | Multiply OperatorExpression OperatorExpression
  | Power OperatorExpression OperatorExpression
  | Concatenate OperatorExpression OperatorExpression
  | Access OperatorExpression OperatorExpression
  deriving (Eq, Show)

toOperatorExpression :: Expression -> OperatorExpression
toOperatorExpression = lower

renderOperatorExpression :: OperatorExpression -> String
renderOperatorExpression = renderOperator TopLevel

normalizeExpression :: Expression -> Expression
normalizeExpression (EllipsisNatural value) = EllipsisNatural value
normalizeExpression EllipsisLiteral = EllipsisLiteral
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

isEmptyMap :: Expression -> Bool
isEmptyMap (AtlasMap []) = True
isEmptyMap (MapSequence []) = True
isEmptyMap _ = False

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower EllipsisLiteral = EllipsisValue
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))
lower (MapSequence expressions) = Sequential (map lower expressions)
lower (MapExpansion left right) = Expansion (lower left) (lower right)
lower (SuperEllipsisRange lowerBound upperBound) =
  Range (lower lowerBound) (lower upperBound)
lower (SuperEllipsisRangePlus lowerBound) = RangePlus (lower lowerBound)
lower (SuperEllipsisRangeMinus upperBound) = RangeMinus (lower upperBound)
lower (Addition left right) = Add (lower left) (lower right)
lower (Multiplication left right) = Multiply (lower left) (lower right)
lower (Exponentiation left right) = Power (lower left) (lower right)
lower (MapConcatenation left right) =
  Concatenate (lower left) (lower right)
lower (MapAccess left right) = Access (lower left) (lower right)

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

data OperandSide = LeftOperand | RightOperand
  deriving (Eq)

data RenderContext
  = TopLevel
  | OperatorOperand Operator OperandSide

renderOperator :: RenderContext -> OperatorExpression -> String
renderOperator context expressionValue =
  parenthesizeWhen (requiresParentheses context expressionValue)
    (renderWithoutParentheses expressionValue)

renderWithoutParentheses :: OperatorExpression -> String
renderWithoutParentheses (NaturalValue value) = show value
renderWithoutParentheses EllipsisValue = ellipsisSymbol
renderWithoutParentheses EmptyMap = "[]"
renderWithoutParentheses (Sequential expressions) =
  renderRightAssociativeChain SequentialOperator expressions
renderWithoutParentheses (Expansion left right) =
  renderBinary ExpansionOperator left right
renderWithoutParentheses (Range lowerBound upperBound) =
  renderBinary RangeOperator lowerBound upperBound
renderWithoutParentheses (RangePlus lowerBound) =
  renderOperator
    (OperatorOperand RangePlusOperator LeftOperand)
    lowerBound
    <> " " <> operatorCanonicalSymbol RangePlusOperator
renderWithoutParentheses (RangeMinus upperBound) =
  renderOperator
    (OperatorOperand RangeMinusOperator LeftOperand)
    upperBound
    <> " " <> operatorCanonicalSymbol RangeMinusOperator
renderWithoutParentheses (Add left right) =
  renderBinary AdditionOperator left right
renderWithoutParentheses (Multiply left right) =
  renderBinary MultiplicationOperator left right
renderWithoutParentheses (Power left right) =
  renderBinary ExponentiationOperator left right
renderWithoutParentheses (Concatenate left right) =
  renderBinary ConcatenationOperator left right
renderWithoutParentheses (Access left right) =
  renderBinary AccessOperator left right

renderBinary
  :: Operator
  -> OperatorExpression
  -> OperatorExpression
  -> String
renderBinary operator left right =
  renderOperator (OperatorOperand operator LeftOperand) left
    <> " " <> operatorCanonicalSymbol operator <> " "
    <> renderOperator (OperatorOperand operator RightOperand) right

renderRightAssociativeChain
  :: Operator
  -> [OperatorExpression]
  -> String
renderRightAssociativeChain _ [] = "[]"
renderRightAssociativeChain _ [expressionValue] =
  renderOperator TopLevel expressionValue
renderRightAssociativeChain operator expressions =
  intercalate (" " <> operatorCanonicalSymbol operator <> " ")
    ( map
        (renderOperator (OperatorOperand operator LeftOperand))
        (init expressions)
        <> [ renderOperator
               (OperatorOperand operator RightOperand)
               (last expressions)
           ]
    )

requiresParentheses :: RenderContext -> OperatorExpression -> Bool
requiresParentheses TopLevel _ = False
requiresParentheses (OperatorOperand parent side) child =
  case operatorKind child of
    Nothing -> False
    Just childOperator ->
      let (parentPrecedence, parentAssociativity) = operatorFixity parent
          (childPrecedence, childAssociativity) =
            operatorFixity childOperator
      in case compare childPrecedence parentPrecedence of
          LT -> True
          GT -> False
          EQ
            | parentAssociativity /= childAssociativity -> True
            | otherwise ->
                case parentAssociativity of
                  AssociateLeft -> side == RightOperand
                  AssociateRight -> side == LeftOperand
                  AssociateNone -> True

operatorKind :: OperatorExpression -> Maybe Operator
operatorKind (NaturalValue _) = Nothing
operatorKind EllipsisValue = Nothing
operatorKind EmptyMap = Nothing
operatorKind (Sequential _) = Just SequentialOperator
operatorKind (Expansion _ _) = Just ExpansionOperator
operatorKind (Range _ _) = Just RangeOperator
operatorKind (RangePlus _) = Just RangePlusOperator
operatorKind (RangeMinus _) = Just RangeMinusOperator
operatorKind (Add _ _) = Just AdditionOperator
operatorKind (Multiply _ _) = Just MultiplicationOperator
operatorKind (Power _ _) = Just ExponentiationOperator
operatorKind (Concatenate _ _) = Just ConcatenationOperator
operatorKind (Access _ _) = Just AccessOperator

parenthesizeWhen :: Bool -> String -> String
parenthesizeWhen True value = "(" <> value <> ")"
parenthesizeWhen False value = value
