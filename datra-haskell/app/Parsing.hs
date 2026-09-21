{-# LANGUAGE OverloadedStrings #-}

module Parsing
  ( parseDatra
  , parseDatraWithSourceName
  , parseDatraLocated
  , parseDatraLocatedWithSourceName
  , parseDatraAst
  , parseDatraAstWithSourceName
  , parseDatraAstLocated
  , parseDatraAstLocatedWithSourceName
  ) where

import Control.Applicative (empty, optional, some, (<|>))
import Control.Monad (void)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixR, Postfix)
  , makeExprParser
  )
import Data.Bifunctor (first)
import Data.Char (chr, digitToInt, isHexDigit, ord)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
  ( Expression
      ( Addition
      , AsciiStringLiteral
      , AtlasMap
      , EllipsisLiteral
      , EllipsisNatural
      , Exponentiation
      , MapAccess
      , MapConcatenation
      , MapExpansion
      , MapSequence
      , Multiplication
      , SuperEllipsisRange
      , SuperEllipsisRangeMinus
      , SuperEllipsisRangePlus
      )
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.Diagnostics
  ( Located (Located, locatedValue)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import Text.Megaparsec
  ( Parsec
  , anySingle
  , between
  , choice
  , eof
  , errorBundlePretty
  , getOffset
  , getSourcePos
  , lookAhead
  , many
  , manyTill
  , notFollowedBy
  , parse
  , sepEndBy
  , sourceColumn
  , sourceLine
  , sourceName
  , satisfy
  , try
  , unPos
  )
import Text.Megaparsec.Char (char, eol, hspace1, space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

type Parser = Parsec Void Text

-- | Parse an in-memory Datra resource without associating it with a real
-- filesystem path. This is the entry point used by tests and other callers
-- that already have the source contents.
parseDatra :: String -> Either String Expression
parseDatra = parseDatraWithSourceName "<input>"

-- | Parse one top-level map with a source name used only in diagnostics. If
-- the first and last significant characters are not '[' and ']', the
-- top-level brackets are implicit.
parseDatraWithSourceName :: FilePath -> String -> Either String Expression
parseDatraWithSourceName sourceName source =
  locatedValue <$> parseDatraLocatedWithSourceName sourceName source

parseDatraLocated :: String -> Either String (Located Expression)
parseDatraLocated = parseDatraLocatedWithSourceName "<input>"

parseDatraLocatedWithSourceName
  :: FilePath
  -> String
  -> Either String (Located Expression)
parseDatraLocatedWithSourceName resourceName source =
  first errorBundlePretty
    (parse locatedResource resourceName (Text.pack source))

-- | Parse the canonical symbolic S-expression emitted by 'renderExpression'.
parseDatraAst :: String -> Either String Expression
parseDatraAst = parseDatraAstWithSourceName "<ast-input>"

parseDatraAstWithSourceName
  :: FilePath
  -> String
  -> Either String Expression
parseDatraAstWithSourceName sourceName source =
  locatedValue <$> parseDatraAstLocatedWithSourceName sourceName source

parseDatraAstLocated :: String -> Either String (Located Expression)
parseDatraAstLocated =
  parseDatraAstLocatedWithSourceName "<ast-input>"

parseDatraAstLocatedWithSourceName
  :: FilePath
  -> String
  -> Either String (Located Expression)
parseDatraAstLocatedWithSourceName resourceName source =
  first errorBundlePretty
    (parse locatedAstResource resourceName (Text.pack source))

locatedResource :: Parser (Located Expression)
locatedResource = located resource

locatedAstResource :: Parser (Located Expression)
locatedAstResource = located astResource

located :: Parser Expression -> Parser (Located Expression)
located parser = do
  startOffset <- getOffset
  start <- getSourcePos
  expressionValue <- parser
  endOffset <- getOffset
  end <- getSourcePos
  pure
    (Located
      (SourceSpan
        (sourceName start)
        (SourcePosition
          (fromIntegral startOffset)
          (fromIntegral (unPos (sourceLine start)))
          (fromIntegral (unPos (sourceColumn start))))
        (SourcePosition
          (fromIntegral endOffset)
          (fromIntegral (unPos (sourceLine end)))
          (fromIntegral (unPos (sourceColumn end)))))
      expressionValue)

astResource :: Parser Expression
astResource = astSpaceConsumer *> astExpression <* eof

astExpression :: Parser Expression
astExpression = astForm <|> astAtom

astAtom :: Parser Expression
astAtom =
  choice
    [ AtlasMap [] <$ astSymbol "[]"
    , EllipsisLiteral <$ astSymbol (Text.pack AST.ellipsisSymbol)
    , AsciiStringLiteral <$> astIdentifierString
    , AsciiStringLiteral <$> astStandardString
    , EllipsisNatural <$> astLexeme Lexer.decimal
    ]

astForm :: Parser Expression
astForm =
  between (astSymbol "(") (astSymbol ")")
    (choice
      [ astSequence
      , astBinary AST.ExpansionOperator MapExpansion
      , astBinary AST.RangeOperator SuperEllipsisRange
      , astUnary AST.RangePlusOperator SuperEllipsisRangePlus
      , astUnary AST.RangeMinusOperator SuperEllipsisRangeMinus
      , astBinary AST.AdditionOperator Addition
      , astBinary AST.MultiplicationOperator Multiplication
      , astBinary AST.ExponentiationOperator Exponentiation
      , astBinary AST.ConcatenationOperator MapConcatenation
      , astBinary AST.AccessOperator MapAccess
      ])

astSequence :: Parser Expression
astSequence = do
  _ <- astOperatorToken AST.SequentialOperator
  firstExpression <- astExpression
  secondExpression <- astExpression
  remainingExpressions <- many astExpression
  pure
    (MapSequence
      (firstExpression : secondExpression : remainingExpressions))

astUnary
  :: AST.Operator
  -> (Expression -> Expression)
  -> Parser Expression
astUnary operator constructor = do
  _ <- astOperatorToken operator
  constructor <$> astExpression

astBinary
  :: AST.Operator
  -> (Expression -> Expression -> Expression)
  -> Parser Expression
astBinary operator constructor = do
  _ <- astOperatorToken operator
  constructor <$> astExpression <*> astExpression

astSpaceConsumer :: Parser ()
astSpaceConsumer = Lexer.space space1 lineComment empty

astLexeme :: Parser value -> Parser value
astLexeme = Lexer.lexeme astSpaceConsumer

astSymbol :: Text -> Parser Text
astSymbol = Lexer.symbol astSpaceConsumer

astOperatorToken :: AST.Operator -> Parser Text
astOperatorToken = astSymbol . Text.pack . AST.operatorCanonicalSymbol

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
    envelopeCharacter =
      lineComment
        <|> try (void standardStringToken)
        <|> void anySingle

atlasMap :: Parser Expression
atlasMap =
  AtlasMap
    <$> between
      (symbol "[" <* lineSpaceConsumer)
      (symbol "]")
      elements

elements :: Parser [Expression]
elements = expression `sepEndBy` mapSeparator

-- A newline is a separator only while parsing map elements. Newlines after
-- an infix operator are consumed by 'continuedSymbol' before this parser can
-- see them.
mapSeparator :: Parser ()
mapSeparator =
  void (semicolon <* lineSpaceConsumer)
    <|> void (some lineBreak)

expression :: Parser Expression
expression = makeExprParser rangeExpression mapOperatorTable

-- Ranges have a small dedicated grammar so exactly one unparenthesized '..'
-- is permitted at this precedence level. Each explicit endpoint is a complete
-- arithmetic expression; nested ranges therefore require parentheses.
rangeExpression :: Parser Expression
rangeExpression =
  try prefixRange
    <|> try explicitRange
    <|> arithmeticExpression

prefixRange :: Parser Expression
prefixRange = do
  _ <- continuedOperator AST.RangeOperator
  SuperEllipsisRange (EllipsisNatural 0) <$> rangeEndpoint

explicitRange :: Parser Expression
explicitRange = do
  lowerBound <- rangeEndpoint
  rangeSuffix lowerBound

rangeSuffix :: Expression -> Parser Expression
rangeSuffix lowerBound =
  choice
    [ SuperEllipsisRangeMinus lowerBound
        <$ operatorToken AST.RangeMinusOperator
    , try $ do
        _ <- continuedOperator AST.RangeOperator
        SuperEllipsisRange lowerBound <$> rangeEndpoint
    , do
        _ <- continuedOperator AST.RangePlusOperator
        _ <- lookAhead postfixRangeEnd
        pure (SuperEllipsisRangePlus lowerBound)
    ]

arithmeticExpression :: Parser Expression
arithmeticExpression = makeExprParser term arithmeticOperatorTable

-- A bare Ellipsis value cannot be a range endpoint. Parentheses deliberately
-- return to the complete expression grammar, making forms such as '(...)..'
-- explicit while keeping grouping out of the AST.
rangeEndpoint :: Parser Expression
rangeEndpoint = makeExprParser rangeEndpointTerm arithmeticOperatorTable

term :: Parser Expression
term =
  choice
    [ parenthesizedExpression
    , atlasMap
    , EllipsisLiteral <$ symbol (Text.pack AST.ellipsisSymbol)
    , AsciiStringLiteral <$> identifierString
    , AsciiStringLiteral <$> standardString
    , ellipsisNatural
    ]

rangeEndpointTerm :: Parser Expression
rangeEndpointTerm =
  choice
    [ parenthesizedExpression
    , atlasMap
    , AsciiStringLiteral <$> identifierString
    , AsciiStringLiteral <$> standardString
    , ellipsisNatural
    ]

parenthesizedExpression :: Parser Expression
parenthesizedExpression =
  between
    (symbol "(" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol ")")
    expression

-- Arithmetic follows Haskell and binds more tightly than range construction.
arithmeticOperatorTable :: [[Operator Parser Expression]]
arithmeticOperatorTable =
  [ [InfixR (Exponentiation <$ continuedOperator AST.ExponentiationOperator)]
  , [InfixL (Multiplication <$ continuedOperator AST.MultiplicationOperator)]
  , [InfixL (Addition <$ continuedOperator AST.AdditionOperator)]
  ]

-- Concatenation binds after ranges, while access is the final map operation.
-- This lets a map access consume a concatenated range insertion.
mapOperatorTable :: [[Operator Parser Expression]]
mapOperatorTable =
  [ [InfixR (MapConcatenation <$ infixComma)]
  , [Postfix (finishConcatenation <$ trailingComma)]
  , [InfixL (MapAccess <$ continuedOperator AST.AccessOperator)]
  ]

finishConcatenation :: Expression -> Expression
finishConcatenation expressionValue@(MapConcatenation _ _) =
  expressionValue
finishConcatenation expressionValue =
  MapConcatenation expressionValue (AtlasMap [])

infixComma :: Parser Text
infixComma =
  try
    (continuedOperator AST.ConcatenationOperator
      <* notFollowedBy expressionEnd)

-- A comma is postfix only when no right operand occurs before the current
-- expression closes. Otherwise the infix parser consumes the same comma and
-- any intervening newlines as ordinary concatenation.
trailingComma :: Parser Text
trailingComma =
  try
    (continuedOperator AST.ConcatenationOperator
      <* lookAhead expressionEnd)

expressionEnd :: Parser ()
expressionEnd =
  void (choice [char ']', char ')', char ';']) <|> eof

-- A postfix range also ends before an operator from the lower-precedence map
-- layer. Keeping these boundaries separate from 'expressionEnd' avoids
-- changing how trailing concatenation is classified after its comma.
postfixRangeEnd :: Parser ()
postfixRangeEnd =
  expressionEnd
    <|> void
      (choice
        [ operatorToken AST.ConcatenationOperator
        , operatorToken AST.AccessOperator
        ])

ellipsisNatural :: Parser Expression
ellipsisNatural = EllipsisNatural <$> lexeme Lexer.decimal

-- | The compact identifier spelling: a dollar sign, one leading canonical
-- character, then any number of canonical characters.
identifierString :: Parser String
identifierString = lexeme identifierStringToken

astIdentifierString :: Parser String
astIdentifierString = astLexeme identifierStringToken

identifierStringToken :: Parser String
identifierStringToken =
  char '$'
    *> ((:)
      <$> satisfy isLeadingCanonicalCharacter
      <*> many (satisfy isCanonicalCharacter))

-- | The standard quoted spelling. It is multiline by default and retains all
-- non-comment contents exactly. A hash begins a line comment, while newline,
-- quote, backslash, and a literal hash have named escaped spellings. Any byte
-- can also be written using one or two hexadecimal digits.
standardString :: Parser String
standardString = lexeme standardStringToken

astStandardString :: Parser String
astStandardString = astLexeme standardStringToken

standardStringToken :: Parser String
standardStringToken =
  between (char '"') (char '"')
    (catMaybes <$> many standardStringPart)

standardStringPart :: Parser (Maybe Char)
standardStringPart =
  choice
    [ Nothing <$ standardStringComment
    , Just <$> standardStringCharacter
    ]

-- Unlike an ordinary line comment, a comment within a string also ends at the
-- string's closing quote. The terminator is left for the surrounding parser,
-- preserving a newline as string content or allowing the quote to close it.
standardStringComment :: Parser ()
standardStringComment =
  char '#'
    *> void
      (manyTill anySingle
        (lookAhead
          ( void (char '"')
            <|> void (char '\n')
            <|> eof
          )))

standardStringCharacter :: Parser Char
standardStringCharacter =
  (char '\\'
    *> choice
      [ '"' <$ char '"'
      , '\\' <$ char '\\'
      , '#' <$ char '#'
      , '\n' <$ char 'n'
      , hexadecimalAsciiCharacter
      ])
    <|> satisfy
      (\character ->
        character /= '"'
          && character /= '\\'
          && character /= '#'
          && isAsciiCharacter character)

hexadecimalAsciiCharacter :: Parser Char
hexadecimalAsciiCharacter = do
  firstDigit <- satisfy isHexDigit
  secondDigit <- optional (satisfy isHexDigit)
  let byteValue =
        case secondDigit of
          Nothing -> digitToInt firstDigit
          Just digit -> 16 * digitToInt firstDigit + digitToInt digit
  pure (chr byteValue)

isLeadingCanonicalCharacter :: Char -> Bool
isLeadingCanonicalCharacter character =
  isAsciiLetter character || character == '_'

isCanonicalCharacter :: Char -> Bool
isCanonicalCharacter character =
  isLeadingCanonicalCharacter character
    || isAsciiDigit character
    || character == '\''

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'

isAsciiCharacter :: Char -> Bool
isAsciiCharacter character = ord character < 256

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

operatorSourceText :: AST.Operator -> Text
operatorSourceText operator =
  case AST.operatorSourceSymbol operator of
    Just value -> Text.pack value
    Nothing -> error "operator has no concrete source token"

operatorToken :: AST.Operator -> Parser Text
operatorToken = symbol . operatorSourceText

continuedOperator :: AST.Operator -> Parser Text
continuedOperator = continuedSymbol . operatorSourceText

semicolon :: Parser Text
semicolon = symbol ";"
