-- | Shared quoted-string grammar. Source and canonical AST notation use the
-- same string language, without sharing either surrounding expression parser.
module StringParsing
  ( standardStringToken
  , stringTemplateToken
  ) where

import Control.Applicative (empty, optional, (<|>))
import Control.Monad (void)
import Data.Char (chr, digitToInt, isHexDigit)
import Data.Text (Text)
import Data.Void (Void)
import DatraLanguage.AST
  ( Expression (..), StringTemplateInterpolation (..) )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (CloseParenthesis, OpenParenthesis)
  , commentCharacter, delimiterCharacter, escapeCharacter, interpolationCharacter
  , lineFeedEscapeCharacter, sourceLineFeedCharacter, stringQuoteCharacter )
import DatraLanguage.Identifier (isAsciiCharacter)
import Text.Megaparsec
  ( Parsec, anySingle, between, choice, eof, lookAhead, many, manyTill
  , satisfy )
import Text.Megaparsec.Char (char, space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

type Parser = Parsec Void Text

data ParsedStringTemplatePart
  = ParsedStringTemplateCharacter Char
  | ParsedStringTemplateInterpolation
      (StringTemplateInterpolation Expression)

standardStringToken :: Parser String
standardStringToken = parsedLiteralText <$> quotedStringParts Nothing

stringTemplateToken
  :: Parser Expression
  -> Parser Expression
  -> Parser Expression
stringTemplateToken compoundInterpolation simpleInterpolation =
  buildStringTemplate <$> quotedStringParts (Just stringInterpolation)
  where
    stringInterpolation = do
      _ <- char interpolationCharacter
      ParsedStringTemplateInterpolation . StringTemplateInterpolation
        <$> (parenthesizedInterpolation <|> simpleInterpolation)
    parenthesizedInterpolation = do
      _ <- char (delimiterCharacter OpenParenthesis)
      spaceConsumer *> compoundInterpolation <* spaceConsumer
        <* char (delimiterCharacter CloseParenthesis)
    spaceConsumer = Lexer.space space1 empty empty

quotedStringParts
  :: Maybe (Parser ParsedStringTemplatePart)
  -> Parser [ParsedStringTemplatePart]
quotedStringParts interpolation =
  between (char stringQuoteCharacter) (char stringQuoteCharacter)
    (concat <$> many quotedPart)
  where
    quotedPart = choice
      ( maybe [] (\parser -> [(: []) <$> parser]) interpolation
          <> [ [] <$ standardStringComment
             , (: []) . ParsedStringTemplateCharacter
                <$> standardStringCharacter
             ]
      )

buildStringTemplate :: [ParsedStringTemplatePart] -> Expression
buildStringTemplate parsedParts =
  case foldr collect ([], False) parsedParts of
    (parts, False) -> AsciiStringLiteral
      (concat
        [ value
        | StringTemplateInterpolation (AsciiStringLiteral value) <- parts
        ])
    (parts, True) -> StringTemplate parts
  where
    collect (ParsedStringTemplateCharacter character) (parts, hasHole) =
      case parts of
        StringTemplateInterpolation (AsciiStringLiteral value) : remaining ->
          ( StringTemplateInterpolation
              (AsciiStringLiteral (character : value)) : remaining
          , hasHole
          )
        _ ->
          ( StringTemplateInterpolation
              (AsciiStringLiteral [character]) : parts
          , hasHole
          )
    collect (ParsedStringTemplateInterpolation interpolation) (parts, _) =
      (interpolation : parts, True)

parsedLiteralText :: [ParsedStringTemplatePart] -> String
parsedLiteralText parts =
  [ character
  | ParsedStringTemplateCharacter character <- parts
  ]

standardStringComment :: Parser ()
standardStringComment =
  char commentCharacter *> void
    (manyTill anySingle
      (lookAhead
        ( void (char stringQuoteCharacter)
          <|> void (char sourceLineFeedCharacter)
          <|> eof
        )))

standardStringCharacter :: Parser Char
standardStringCharacter =
  (char escapeCharacter *>
    choice
      [ stringQuoteCharacter <$ char stringQuoteCharacter
      , escapeCharacter <$ char escapeCharacter
      , commentCharacter <$ char commentCharacter
      , interpolationCharacter <$ char interpolationCharacter
      , AST.sourceOperatorCharacter AST.OptionalCharacterOperator
          <$ char (AST.sourceOperatorCharacter AST.OptionalCharacterOperator)
      , sourceLineFeedCharacter <$ char lineFeedEscapeCharacter
      , hexadecimalAsciiCharacter
      ])
    <|> satisfy
      (\character ->
        character /= stringQuoteCharacter
          && character /= escapeCharacter
          && character /= commentCharacter
          && character /= interpolationCharacter
          && isAsciiCharacter character)

hexadecimalAsciiCharacter :: Parser Char
hexadecimalAsciiCharacter = do
  firstDigit <- satisfy isHexDigit
  secondDigit <- optional (satisfy isHexDigit)
  let byteValue = case secondDigit of
        Nothing -> digitToInt firstDigit
        Just digit -> 16 * digitToInt firstDigit + digitToInt digit
  pure (chr byteValue)
