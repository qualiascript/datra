{-# LANGUAGE OverloadedStrings #-}

module Datra.Parsing
  ( parseDatra
  ) where

import Control.Applicative (empty, some, (<|>))
import Control.Monad (void)
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
  , anySingle
  , between
  , choice
  , eof
  , errorBundlePretty
  , lookAhead
  , many
  , manyTill
  , parse
  , sepEndBy
  , try
  )
import Text.Megaparsec.Char (char, eol, hspace1, space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

type Parser = Parsec Void Text

-- | Parse one top-level map. If the first and last significant characters
-- are not '[' and ']', the top-level brackets are implicit.
parseDatra :: String -> Either String Expression
parseDatra source =
  first errorBundlePretty
    (parse resource "input.datra" (Text.pack source))

resource :: Parser Expression
resource = do
  fullSpaceConsumer
  result <-
    (try (lookAhead outerMapEnvelope) *> atlasMap)
      <|> (AtlasMap <$> elements)
  fullSpaceConsumer
  eof
  pure result

-- This lookahead expresses the outer-bracket rule without rewriting the
-- source. Comments are consumed as a unit so a ']' inside one cannot be
-- mistaken for the final significant character.
outerMapEnvelope :: Parser ()
outerMapEnvelope =
  void
    ( char '['
        *> manyTill envelopeCharacter
          (try (char ']' *> fullSpaceConsumer <* eof))
    )
  where
    envelopeCharacter = lineComment <|> void anySingle

atlasMap :: Parser Expression
atlasMap =
  AtlasMap
    <$> between
      (symbol "[" <* lineSpaceConsumer)
      (symbol "]")
      elements

elements :: Parser [Expression]
elements = do
  expressions <- expression `sepEndBy` mapSeparator
  _ <- many (semicolon <* lineSpaceConsumer)
  pure expressions

-- A newline is a separator only while parsing map elements. Newlines after
-- an infix operator are consumed by 'continuedSymbol' before this parser can
-- see them.
mapSeparator :: Parser ()
mapSeparator =
  void (semicolon <* lineSpaceConsumer)
    <|> void (some lineBreak)

expression :: Parser Expression
expression = makeExprParser term operatorTable

term :: Parser Expression
term =
  choice
    [ between
        (symbol "(" <* lineSpaceConsumer)
        (lineSpaceConsumer *> symbol ")")
        expression
    , atlasMap
    , EllipsisLiteral <$ symbol "..."
    , ellipsisNatural
    ]

-- Arithmetic follows Haskell. Ranges bind after arithmetic, concatenation
-- combines completed map/range expressions, and access is the final map
-- operation. This lets a map access consume a concatenated range insertion.
operatorTable :: [[Operator Parser Expression]]
operatorTable =
  [ [InfixR (Exponentiation <$ continuedSymbol "^")]
  , [InfixL (Multiplication <$ continuedSymbol "*")]
  , [InfixL (Addition <$ continuedSymbol "+")]
  , [ Postfix (SuperEllipsisRangePlus <$ symbol "..+")
    , Postfix (SuperEllipsisRangeMinus <$ symbol "..-")
    , InfixN (SuperEllipsisRange <$ continuedSymbol "..")
    ]
  , [InfixR (MapConcatenation <$ continuedSymbol ",")]
  , [InfixL (MapAccess <$ continuedSymbol "@")]
  ]

ellipsisNatural :: Parser Expression
ellipsisNatural = EllipsisNatural <$> lexeme Lexer.decimal

-- Horizontal trivia belongs to the preceding token. Keeping line breaks out
-- of the ordinary lexeme consumer lets the grammar decide whether each one
-- is a map separator or expression continuation.
horizontalSpaceConsumer :: Parser ()
horizontalSpaceConsumer = Lexer.space hspace1 lineComment empty

fullSpaceConsumer :: Parser ()
fullSpaceConsumer = Lexer.space space1 lineComment empty

lineComment :: Parser ()
lineComment = Lexer.skipLineComment "#"

lineSpaceConsumer :: Parser ()
lineSpaceConsumer = horizontalSpaceConsumer *> void (many lineBreak)

lineBreak :: Parser ()
lineBreak = void (eol <* horizontalSpaceConsumer)

lexeme :: Parser value -> Parser value
lexeme = Lexer.lexeme horizontalSpaceConsumer

symbol :: Text -> Parser Text
symbol = Lexer.symbol horizontalSpaceConsumer

continuedSymbol :: Text -> Parser Text
continuedSymbol value = symbol value <* lineSpaceConsumer

semicolon :: Parser Text
semicolon = symbol ";"
