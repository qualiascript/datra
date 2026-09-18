-- | Language-neutral rendering shared by diagnostic locales.
module DatraLanguage.Diagnostics.Locales.Rendering
  ( renderOrdinal
  , renderRangeBounds
  , renderRangeDescription
  ) where

import Data.List (intercalate)
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  )
import DatraOrdinal (Ordinal, ordinalCoefficients)
import SuperEllipsisRange
  ( SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeTarget (..)
  )

renderRangeDescription :: SuperEllipsisRangeDescription -> String
renderRangeDescription description =
  renderOrdinal (describedRangeStart description)
    <> case describedRangeTarget description of
      GivenTarget target ->
        sourceSymbol RangeOperator <> renderOrdinal target
      PlusSign -> sourceSymbol RangePlusOperator
      MinusSign -> sourceSymbol RangeMinusOperator

renderRangeBounds :: Ordinal -> Ordinal -> String
renderRangeBounds lower upper =
  renderOrdinal lower <> sourceSymbol RangeOperator <> renderOrdinal upper

renderOrdinal :: Ordinal -> String
renderOrdinal value =
  case ordinalCoefficients value of
    [] -> "0"
    coefficients ->
      intercalate (spacedSourceSymbol AdditionOperator)
        [ renderTerm power coefficient
        | (power, coefficient) <- zip [degree, degree - 1 .. 0] coefficients
        , coefficient /= 0
        ]
      where
        degree = length coefficients - 1
        renderTerm 0 coefficient = show coefficient
        renderTerm 1 1 = parenthesizedEllipsis
        renderTerm 1 coefficient =
          parenthesizedEllipsis
            <> spacedSourceSymbol MultiplicationOperator
            <> show coefficient
        renderTerm power 1 =
          parenthesizedEllipsis
            <> sourceSymbol ExponentiationOperator
            <> show power
        renderTerm power coefficient =
          parenthesizedEllipsis
            <> sourceSymbol ExponentiationOperator
            <> show power
            <> spacedSourceSymbol MultiplicationOperator
            <> show coefficient

parenthesizedEllipsis :: String
parenthesizedEllipsis = "(" <> ellipsisSymbol <> ")"

sourceSymbol :: Operator -> String
sourceSymbol operator =
  case operatorSourceSymbol operator of
    Just value -> value
    Nothing -> operatorCanonicalSymbol operator

spacedSourceSymbol :: Operator -> String
spacedSourceSymbol operator = " " <> sourceSymbol operator <> " "
