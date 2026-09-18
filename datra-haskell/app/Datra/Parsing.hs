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
