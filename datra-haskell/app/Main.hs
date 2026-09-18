{-# LANGUAGE OverloadedStrings #-}

module Main
  ( Expression (..)
  , interpretDatra
  , main
  , parseDatra
  , renderExpression
  ) where

import Control.Applicative (empty)
import Data.Bifunctor (first)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import Numeric.Natural (Natural)
import Text.Megaparsec
  ( Parsec
  , between
  , choice
  , eof
  , errorBundlePretty
  , many
  , parse
  , sepEndBy
  )
import Text.Megaparsec.Char (space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

-- | The source language supported by the first interpreter version.
data Expression
  = EllipsisNatural Natural
  | AtlasMap [Expression]
  deriving (Eq, Show)

-- | Parse and lower a Datra resource directly to its textual operator AST.
-- This pure entry point is also used by the interpreter test suite.
interpretDatra :: String -> Either String String
interpretDatra source = renderExpression <$> parseDatra source

-- | Parse one top-level map, allowing whitespace and Python-style comments
-- wherever whitespace is accepted.
parseDatra :: String -> Either String Expression
parseDatra source =
  first errorBundlePretty
    (parse resource "input.datra" (Text.pack source))

type Parser = Parsec Void Text

resource :: Parser Expression
resource = spaceConsumer *> atlasMap <* eof

atlasMap :: Parser Expression
atlasMap = AtlasMap <$> between (symbol "[") (symbol "]") elements
  where
    elements = do
      expressions <- expression `sepEndBy` semicolon
      _ <- many semicolon
      pure expressions

expression :: Parser Expression
expression = choice [atlasMap, ellipsisNatural]

ellipsisNatural :: Parser Expression
ellipsisNatural = EllipsisNatural <$> lexeme Lexer.decimal

spaceConsumer :: Parser ()
spaceConsumer = Lexer.space space1 (Lexer.skipLineComment "#") empty

lexeme :: Parser value -> Parser value
lexeme = Lexer.lexeme spaceConsumer

symbol :: Text -> Parser Text
symbol = Lexer.symbol spaceConsumer

semicolon :: Parser Text
semicolon = symbol ";"

-- | Render map structure using the operators from "MapOperators". Direct
-- natural-number neighbours form a flattened '<:>' sequence. A bracketed
-- child starts a new group, and neighbouring groups are joined with '<+>'.
renderExpression :: Expression -> String
renderExpression = renderOperator 0 . lower . trimRoot

data OperatorExpression
  = NaturalValue Natural
  | EmptyMap
  | Sequential [OperatorExpression]
  | Expansion OperatorExpression OperatorExpression

trimRoot :: Expression -> Expression
trimRoot (EllipsisNatural value) = EllipsisNatural value
trimRoot (AtlasMap expressions) = AtlasMap (mapMaybe trimNested expressions)

trimNested :: Expression -> Maybe Expression
trimNested (EllipsisNatural value) = Just (EllipsisNatural value)
trimNested (AtlasMap expressions) =
  case mapMaybe trimNested expressions of
    [] -> Nothing
    trimmed -> Just (AtlasMap trimmed)

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))

data Segment
  = NaturalSegment [Natural]
  | MapSegment Expression

-- Consecutive naturals occupy one level. Each nested map delimits another
-- level, even when that nested map contains only one value.
segments :: [Expression] -> [Segment]
segments = go []
  where
    go naturals [] = finishNaturals naturals
    go naturals (EllipsisNatural value : rest) =
      go (value : naturals) rest
    go naturals (nested@(AtlasMap _) : rest) =
      finishNaturals naturals <> (MapSegment nested : go [] rest)

    finishNaturals [] = []
    finishNaturals values = [NaturalSegment (reverse values)]

lowerSegment :: Segment -> OperatorExpression
lowerSegment (NaturalSegment values) =
  case map NaturalValue values of
    [value] -> value
    expressions -> Sequential expressions
lowerSegment (MapSegment expressionValue) = lower expressionValue

combineExpansions :: [OperatorExpression] -> OperatorExpression
combineExpansions [] = EmptyMap
combineExpansions [expressionValue] = expressionValue
combineExpansions (firstExpression : rest) =
  Expansion firstExpression (combineExpansions rest)

renderOperator :: Int -> OperatorExpression -> String
renderOperator _ (NaturalValue value) = show value
renderOperator _ EmptyMap = "[]"
renderOperator enclosingPrecedence (Sequential expressions) =
  parenthesizeWhen (enclosingPrecedence > sequentialPrecedence)
    (intercalate " <:> " (map (renderOperator sequentialPrecedence) expressions))
renderOperator enclosingPrecedence (Expansion left right) =
  parenthesizeWhen (enclosingPrecedence >= expansionPrecedence)
    ( renderOperator (expansionPrecedence + 1) left
        <> " <+> "
        <> renderOperator (expansionPrecedence + 1) right
    )

sequentialPrecedence :: Int
sequentialPrecedence = 7

expansionPrecedence :: Int
expansionPrecedence = 6

parenthesizeWhen :: Bool -> String -> String
parenthesizeWhen True value = "(" <> value <> ")"
parenthesizeWhen False value = value

main :: IO ()
main = do
  source <- readFile "input.datra"
  case interpretDatra source of
    Left message -> ioError (userError ("input.datra: " <> message))
    Right ast -> writeFile "output.datra.ast" (ast <> "\n")
