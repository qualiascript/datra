module Main
  ( Expression (..)
  , interpretDatra
  , main
  , parseDatra
  , renderExpression
  ) where

import Data.Char (isSpace)
import Data.List (intercalate)
import Data.Maybe (mapMaybe)
import Numeric.Natural (Natural)
import Text.ParserCombinators.ReadP
  ( ReadP
  , char
  , eof
  , look
  , munch
  , munch1
  , pfail
  , readP_to_S
  , (<++)
  )

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
  case [expressionValue | (expressionValue, "") <- readP_to_S resource source] of
    [] -> Left "expected a map made from natural numbers, '[', ']', and ';'"
    expressions -> Right (last expressions)
  where
    resource = skipTrivia *> atlasMap <* skipTrivia <* eof

atlasMap :: ReadP Expression
atlasMap = do
  _ <- char '['
  skipTrivia
  expressions <- emptyMap <++ nonEmptyMap
  pure (AtlasMap expressions)
  where
    emptyMap = char ']' *> skipTrivia *> pure []
    nonEmptyMap = do
      first <- expression
      rest <- remainingExpressions
      _ <- char ']'
      skipTrivia
      pure (first : rest)

    remainingExpressions =
      (do
        _ <- char ';'
        skipTrivia
        trailingSeparators <++ moreExpressions)
      <++ pure []

    moreExpressions = do
      next <- expression
      remaining <- remainingExpressions
      pure (next : remaining)

    trailingSeparators = do
      remainingInput <- look
      case remainingInput of
        ']' : _ -> pure []
        ';' : _ -> char ';' *> skipTrivia *> trailingSeparators
        _ -> pfail

expression :: ReadP Expression
expression = atlasMap <++ ellipsisNatural

ellipsisNatural :: ReadP Expression
ellipsisNatural = do
  digits <- munch1 isAsciiDigit
  skipTrivia
  pure (EllipsisNatural (read digits))
  where
    isAsciiDigit character = character >= '0' && character <= '9'

skipTrivia :: ReadP ()
skipTrivia = do
  _ <- munch isSpace
  (do
      _ <- char '#'
      _ <- munch (/= '\n')
      skipTrivia)
    <++ pure ()

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
combineExpansions (first : rest) = Expansion first (combineExpansions rest)

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
