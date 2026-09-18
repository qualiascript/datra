module Datra.AST
  ( Expression (..)
  , renderExpression
  ) where

import Data.List (intercalate)
import Numeric.Natural (Natural)

-- | Unevaluated Datra syntax. Capabilities and silent coercions are resolved
-- later by the type checker and interpreter, not while constructing the AST.
data Expression
  = EllipsisNatural Natural
  | EllipsisLiteral
  | AtlasMap [Expression]
  | SuperEllipsisRange Expression Expression
  | SuperEllipsisRangePlus Expression
  | SuperEllipsisRangeMinus Expression
  | Addition Expression Expression
  | Multiplication Expression Expression
  | Exponentiation Expression Expression
  | MapConcatenation Expression Expression
  | MapAccess Expression Expression
  deriving (Eq, Show)

-- | Lower map notation and render the unevaluated AST using the operators
-- exported by the Datra libraries.
renderExpression :: Expression -> String
renderExpression = renderOperator TopLevel . lower . normalizeExpression

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

normalizeExpression :: Expression -> Expression
normalizeExpression (EllipsisNatural value) = EllipsisNatural value
normalizeExpression EllipsisLiteral = EllipsisLiteral
normalizeExpression (AtlasMap expressions) =
  AtlasMap
    (filter (not . isEmptyMap) (map normalizeExpression expressions))
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
isEmptyMap _ = False

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower EllipsisLiteral = EllipsisValue
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))
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

data Associativity = AssociateLeft | AssociateRight | AssociateNone
  deriving (Eq)

data OperatorKind
  = SequentialOperator
  | ExpansionOperator
  | RangeOperator
  | RangePostfixOperator
  | AdditionOperator
  | MultiplicationOperator
  | ExponentiationOperator
  | ConcatenationOperator
  | AccessOperator

data OperandSide = LeftOperand | RightOperand
  deriving (Eq)

data RenderContext
  = TopLevel
  | OperatorOperand OperatorKind OperandSide

renderOperator :: RenderContext -> OperatorExpression -> String
renderOperator context expressionValue =
  parenthesizeWhen (requiresParentheses context expressionValue)
    (renderWithoutParentheses expressionValue)

renderWithoutParentheses :: OperatorExpression -> String
renderWithoutParentheses (NaturalValue value) = show value
renderWithoutParentheses EllipsisValue = "..."
renderWithoutParentheses EmptyMap = "[]"
renderWithoutParentheses (Sequential expressions) =
  renderRightAssociativeChain SequentialOperator " <:> " expressions
renderWithoutParentheses (Expansion left right) =
  renderBinary ExpansionOperator " <+> " left right
renderWithoutParentheses (Range lowerBound upperBound) =
  renderBinary RangeOperator " <..> " lowerBound upperBound
renderWithoutParentheses (RangePlus lowerBound) =
  renderOperator
    (OperatorOperand RangePostfixOperator LeftOperand)
    lowerBound
    <> " ..+"
renderWithoutParentheses (RangeMinus upperBound) =
  renderOperator
    (OperatorOperand RangePostfixOperator LeftOperand)
    upperBound
    <> " ..-"
renderWithoutParentheses (Add left right) =
  renderBinary AdditionOperator " + " left right
renderWithoutParentheses (Multiply left right) =
  renderBinary MultiplicationOperator " * " left right
renderWithoutParentheses (Power left right) =
  renderBinary ExponentiationOperator " ^ " left right
renderWithoutParentheses (Concatenate left right) =
  renderBinary ConcatenationOperator " <.> " left right
renderWithoutParentheses (Access left right) =
  renderBinary AccessOperator " <@> " left right

renderBinary
  :: OperatorKind
  -> String
  -> OperatorExpression
  -> OperatorExpression
  -> String
renderBinary operator symbolText left right =
  renderOperator (OperatorOperand operator LeftOperand) left
    <> symbolText
    <> renderOperator (OperatorOperand operator RightOperand) right

renderRightAssociativeChain
  :: OperatorKind
  -> String
  -> [OperatorExpression]
  -> String
renderRightAssociativeChain _ _ [] = "[]"
renderRightAssociativeChain _ _ [expressionValue] =
  renderOperator TopLevel expressionValue
renderRightAssociativeChain operator symbolText expressions =
  intercalate symbolText
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

operatorKind :: OperatorExpression -> Maybe OperatorKind
operatorKind (NaturalValue _) = Nothing
operatorKind EllipsisValue = Nothing
operatorKind EmptyMap = Nothing
operatorKind (Sequential _) = Just SequentialOperator
operatorKind (Expansion _ _) = Just ExpansionOperator
operatorKind (Range _ _) = Just RangeOperator
operatorKind (RangePlus _) = Just RangePostfixOperator
operatorKind (RangeMinus _) = Just RangePostfixOperator
operatorKind (Add _ _) = Just AdditionOperator
operatorKind (Multiply _ _) = Just MultiplicationOperator
operatorKind (Power _ _) = Just ExponentiationOperator
operatorKind (Concatenate _ _) = Just ConcatenationOperator
operatorKind (Access _ _) = Just AccessOperator

operatorFixity :: OperatorKind -> (Int, Associativity)
operatorFixity SequentialOperator = (7, AssociateRight)
operatorFixity ExpansionOperator = (6, AssociateNone)
operatorFixity RangeOperator = (5, AssociateNone)
operatorFixity RangePostfixOperator = (5, AssociateLeft)
operatorFixity AdditionOperator = (6, AssociateLeft)
operatorFixity MultiplicationOperator = (7, AssociateLeft)
operatorFixity ExponentiationOperator = (8, AssociateRight)
operatorFixity ConcatenationOperator = (7, AssociateRight)
operatorFixity AccessOperator = (8, AssociateLeft)

parenthesizeWhen :: Bool -> String -> String
parenthesizeWhen True value = "(" <> value <> ")"
parenthesizeWhen False value = value
