{-# LANGUAGE OverloadedStrings #-}

-- | Language-neutral rendering shared by diagnostic locales.
module DatraLanguage.Diagnostics.Locales.Rendering
  ( renderOrdinal
  , renderRangeBounds
  , renderRangeDescription
  ) where

import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  )
import DatraOrdinal (Ordinal, ordinalCoefficients)
import Prettyprinter
  ( Doc
  , concatWith
  , layoutCompact
  , parens
  , pretty
  )
import Prettyprinter.Render.String (renderString)
import SuperEllipsisRange
  ( SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeTarget (..)
  )

renderRangeDescription :: SuperEllipsisRangeDescription -> String
renderRangeDescription = renderCompact . prettyRangeDescription

prettyRangeDescription
  :: SuperEllipsisRangeDescription
  -> Doc annotation
prettyRangeDescription description =
  prettyOrdinal (describedRangeStart description)
    <> case describedRangeTarget description of
      GivenTarget target ->
        prettySourceSymbol RangeOperator <> prettyOrdinal target
      PlusSign -> prettySourceSymbol RangePlusOperator
      MinusSign -> prettySourceSymbol RangeMinusOperator

renderRangeBounds :: Ordinal -> Ordinal -> String
renderRangeBounds lower upper =
  renderCompact
    (prettyOrdinal lower
      <> prettySourceSymbol RangeOperator
      <> prettyOrdinal upper)

renderOrdinal :: Ordinal -> String
renderOrdinal = renderCompact . prettyOrdinal

prettyOrdinal :: Ordinal -> Doc annotation
prettyOrdinal value =
  case ordinalCoefficients value of
    [] -> "0"
    coefficients ->
      concatWith
        (\left right ->
          left <> prettySpacedSourceSymbol AdditionOperator <> right)
        [ renderTerm power coefficient
        | (power, coefficient) <- zip [degree, degree - 1 .. 0] coefficients
        , coefficient /= 0
        ]
      where
        degree = length coefficients - 1
        renderTerm 0 coefficient = pretty coefficient
        renderTerm 1 1 = parenthesizedEllipsis
        renderTerm 1 coefficient =
          parenthesizedEllipsis
            <> prettySpacedSourceSymbol MultiplicationOperator
            <> pretty coefficient
        renderTerm power 1 =
          parenthesizedEllipsis
            <> prettySpacedSourceSymbol ExponentiationOperator
            <> pretty power
        renderTerm power coefficient =
          parenthesizedEllipsis
            <> prettySpacedSourceSymbol ExponentiationOperator
            <> pretty power
            <> prettySpacedSourceSymbol MultiplicationOperator
            <> pretty coefficient

parenthesizedEllipsis :: Doc annotation
parenthesizedEllipsis = parens (pretty ellipsisSymbol)

prettySourceSymbol :: Operator -> Doc annotation
prettySourceSymbol = pretty . sourceSymbol

sourceSymbol :: Operator -> String
sourceSymbol operator =
  case operatorSourceSymbol operator of
    Just value -> value
    Nothing -> operatorCanonicalSymbol operator

prettySpacedSourceSymbol :: Operator -> Doc annotation
prettySpacedSourceSymbol operator =
  " " <> prettySourceSymbol operator <> " "

renderCompact :: Doc annotation -> String
renderCompact = renderString . layoutCompact
