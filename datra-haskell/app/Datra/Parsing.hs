{-# LANGUAGE OverloadedStrings #-}

module Datra.Parsing
  ( parseDatra
  ) where

import Control.Applicative (empty)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixN, InfixR, Postfix)
  , makeExprParser
  )
import Data.Bifunctor (first)
import Data.Char (isSpace)
import Data.List (isSuffixOf)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import Datra.AST
  ( Expression
      ( Addition
      , AtlasMap
      , EllipsisLiteral
      , EllipsisNatural
      , Exponentiation
      , MapAccess
      , MapConcatenation
      , Multiplication
      , SuperEllipsisRange
      , SuperEllipsisRangeMinus
      , SuperEllipsisRangePlus
      )
  )
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

-- | Parse one top-level map, allowing whitespace and Python-style comments
-- wherever whitespace is accepted.
parseDatra :: String -> Either String Expression
parseDatra = parseResource . inferMapLayout . ensureOuterMap

parseResource :: String -> Either String Expression
parseResource source =
  first errorBundlePretty
    (parse resource "input.datra" (Text.pack source))

-- The outer brackets are optional. Comments and whitespace are trivia for the
-- purpose of deciding whether the first and last significant characters are
-- already an enclosing pair.
ensureOuterMap :: String -> String
ensureOuterMap source =
  case significantCharacters source of
    '[' : rest
      | not (null rest) && last rest == ']' -> source
    _ -> "[" <> source <> "]"

significantCharacters :: String -> String
significantCharacters = go False
  where
    go _ [] = []
    go _ ('\n' : rest) = go False rest
    go True (_ : rest) = go True rest
    go False ('#' : rest) = go True rest
    go False (character : rest)
      | isSpace character = go False rest
      | otherwise = character : go False rest

data LayoutContext
  = MapContext Bool String
  | ParenthesisContext

-- A completed physical line ends an expression whenever the current
-- delimiter is a map. Each nested map owns its own line state, so a newline
-- immediately after '[' does not create an empty entry in that map.
inferMapLayout :: String -> String
inferMapLayout = go [] False
  where
    go :: [LayoutContext] -> Bool -> String -> String
    go _ _ [] = []
    go contexts inComment (character : rest)
      | character == '\n' =
          let (separator, nextContexts) = endLine contexts
          in character : separator <> go nextContexts False rest
      | inComment = character : go contexts True rest
      | character == '#' = character : go contexts True rest
      | character == '[' =
          character : go (MapContext False "" : contexts) False rest
      | character == ']' =
          character : go (closeMap contexts) False rest
      | character == '(' =
          character : go (ParenthesisContext : contexts) False rest
      | character == ')' =
          character : go (closeParenthesis contexts) False rest
      | isSpace character = character : go contexts False rest
      | otherwise =
          character : go (rememberInMap character contexts) False rest

    endLine (MapContext lineHasSyntax recent : contexts)
      | lineHasSyntax && not (continuationExpected recent) =
          (";", MapContext False "" : contexts)
      | otherwise =
          ("", MapContext False recent : contexts)
    endLine contexts = ("", contexts)

    closeMap (MapContext _ _ : contexts) = rememberInMap ']' contexts
    closeMap contexts = contexts

    closeParenthesis (ParenthesisContext : contexts) =
      rememberInMap ')' contexts
    closeParenthesis contexts = contexts

    rememberInMap character (MapContext _ recent : contexts) =
      MapContext True (remember character recent) : contexts
    rememberInMap _ contexts = contexts

    remember character recent =
      reverse (take 4 (character : reverse recent))

continuationExpected :: String -> Bool
continuationExpected recent
  | "..+" `isSuffixOf` recent = False
  | "..-" `isSuffixOf` recent = False
  | "..." `isSuffixOf` recent = False
  | ".." `isSuffixOf` recent = True
  | otherwise =
      case reverse recent of
        character : _ -> character `elem` ("+*^,@;" :: String)
        [] -> False

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
expression = makeExprParser term operatorTable

term :: Parser Expression
term =
  choice
    [ between (symbol "(") (symbol ")") expression
    , atlasMap
    , EllipsisLiteral <$ symbol "..."
    , ellipsisNatural
    ]

-- Arithmetic follows Haskell. Ranges bind after arithmetic, concatenation
-- combines completed map/range expressions, and access is the final map
-- operation. This lets a map access consume a concatenated range insertion.
operatorTable :: [[Operator Parser Expression]]
operatorTable =
  [ [InfixR (Exponentiation <$ symbol "^")]
  , [InfixL (Multiplication <$ symbol "*")]
  , [InfixL (Addition <$ symbol "+")]
  , [ Postfix (SuperEllipsisRangePlus <$ symbol "..+")
    , Postfix (SuperEllipsisRangeMinus <$ symbol "..-")
    , InfixN (SuperEllipsisRange <$ symbol "..")
    ]
  , [InfixR (MapConcatenation <$ symbol ",")]
  , [InfixL (MapAccess <$ symbol "@")]
  ]

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
