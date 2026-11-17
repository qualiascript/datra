{-# LANGUAGE RankNTypes #-}

-- | Shared parsing for interpolated source forms. Quoted strings and literal
-- templates use the same interpolation and escape grammar while supplying
-- different delimiter, layout, literal, and semantic policies.
module StringParsing
  ( InterpolationParsers (..)
  , LiteralTemplateParsers (..)
  , interpolationToken
  , standardStringToken
  , stringTemplateToken
  , literalTemplateToken
  ) where

import Control.Applicative (empty, optional, (<|>))
import Control.Monad (void, when)
import Control.Monad.Combinators.Expr
  ( Operator (InfixR, Postfix)
  , makeExprParser
  )
import Data.Char (chr, digitToInt, isHexDigit, isSpace)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text (Text)
import Data.Text qualified as Text
import DatraLanguage.AST
  ( IdentifierExpressionComposition (..)
  , Expression (..)
  , LiteralTemplate (..)
  , LiteralTemplateAtom (..)
  , LiteralTemplateLiteral (..)
  , LiteralTemplateSequence (..)
  , literalTemplateNullable
  , SimpleIdentifierString (..)
  , StringTemplateInterpolation (..)
  , SymbolLiteral (..)
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (CloseParenthesis, OpenParenthesis)
  , commentCharacter
  , delimiterCharacter
  , escapeCharacter
  , interpolationCharacter
  , isSourceLineBreakCharacter
  , lineFeedEscapeCharacter
  , literalTemplateDelimiterCharacter
  , sourceLineFeedCharacter
  , sourceSpaceCharacter
  , stringQuoteCharacter
  )
import DatraLanguage.Diagnostics.Application
  ( LiteralTemplateParseFailure (..))
import DatraLanguage.Identifier
  ( isAsciiCharacter, isIdentifierCharacter )
import Text.Megaparsec
  ( Parsec
  , anySingle
  , between
  , choice
  , chunk
  , eof
  , lookAhead
  , many
  , manyTill
  , match
  , notFollowedBy
  , satisfy
  , some
  , try
  )
import Text.Megaparsec.Char (char, space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

type Parser error = Parsec error Text

data InterpolationParsers error expression = InterpolationParsers
  { compoundInterpolationParser :: Parser error expression
  , simpleInterpolationParser :: Parser error expression
  , interpolationLayoutParser :: Parser error ()
  }

data LiteralTemplateParsers error = LiteralTemplateParsers
  { literalTemplateInterpolation :: InterpolationParsers error Expression
  , rejectLiteralTemplate
      :: forall value. LiteralTemplateParseFailure -> Parser error value
  }

data ParsedStringTemplatePart
  = ParsedStringTemplateCharacter Char
  | ParsedStringTemplateInterpolation
      (StringTemplateInterpolation Expression)

standardStringToken :: Ord error => Parser error String
standardStringToken = parsedLiteralText <$> quotedStringParts Nothing

stringTemplateToken
  :: Ord error
  => Parser error Expression
  -> Parser error Expression
  -> Parser error Expression
stringTemplateToken compoundInterpolation simpleInterpolation =
  buildStringTemplate <$> quotedStringParts (Just stringInterpolation)
  where
    stringInterpolation =
      ParsedStringTemplateInterpolation . StringTemplateInterpolation
        <$> interpolationToken InterpolationParsers
          { compoundInterpolationParser = compoundInterpolation
          , simpleInterpolationParser = simpleInterpolation
          , interpolationLayoutParser =
              Lexer.space space1 empty empty
          }

-- | Parse one interpolation with a mode-selected expression grammar and
-- layout policy. This is the sole parser for the shared @%@, simple, and
-- parenthesized interpolation structure.
interpolationToken
  :: Ord error
  => InterpolationParsers error expression
  -> Parser error expression
interpolationToken parsers = do
  _ <- char interpolationCharacter
  parenthesizedInterpolation <|> simpleInterpolationParser parsers
  where
    parenthesizedInterpolation = between
      (char (delimiterCharacter OpenParenthesis)
        <* interpolationLayoutParser parsers)
      (interpolationLayoutParser parsers
        *> char (delimiterCharacter CloseParenthesis))
      (compoundInterpolationParser parsers)

literalTemplateToken
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error Expression
literalTemplateToken parsers = between
  (char literalTemplateDelimiterCharacter)
  (char literalTemplateDelimiterCharacter)
  (do
    template <- literalTemplateBody parsers
    when (literalTemplateNullable template)
      (rejectLiteralTemplate parsers NullableLiteralTemplate)
    pure (LiteralTemplateExpression template))

literalTemplateBody
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error (LiteralTemplate Expression)
literalTemplateBody parsers = LiteralTemplate <$> makeExprParser
  (literalTemplateSequence parsers)
  [[InfixR (EitherExpression <$ literalTemplateEitherOperator)]]

literalTemplateEitherOperator :: Ord error => Parser error ()
literalTemplateEitherOperator = void $ do
  _ <- char sourceSpaceCharacter
  _ <- char (AST.sourceOperatorCharacter AST.EitherCharacterOperator)
  _ <- char sourceSpaceCharacter
  pure ()

literalTemplateSequence
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error
      (IdentifierExpressionComposition (LiteralTemplateSequence Expression))
literalTemplateSequence parsers = do
  first <- literalTemplateComponent parsers
  remaining <- continue
  pure (IdentifierComposition
    (LiteralTemplateSequence (first :| remaining)))
  where
    continue = choice
      [ [] <$ try (lookAhead literalTemplateEitherOperator)
      , [] <$ lookAhead literalTemplateEnd
      , do
          literalTemplateSeparator parsers
          component <- literalTemplateComponent parsers
          (component :) <$> continue
      , do
          next <- lookAhead anySingle
          if isSpace next
            || next == AST.sourceOperatorCharacter AST.EitherCharacterOperator
            || literalTemplatePartCanStart next
            then rejectLiteralTemplate parsers InvalidLiteralTemplateSpacing
            else pure []
      ]

literalTemplateEnd :: Ord error => Parser error Char
literalTemplateEnd = choice
  [ char literalTemplateDelimiterCharacter
  , char (delimiterCharacter CloseParenthesis)
  ]

literalTemplateComponent
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error
      (IdentifierExpressionComposition (LiteralTemplateAtom Expression))
literalTemplateComponent parsers = do
  next <- lookAhead anySingle
  when (isSpace next)
    (rejectLiteralTemplate parsers InvalidLiteralTemplateSpacing)
  literalTemplatePart parsers

literalTemplateSeparator
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error ()
literalTemplateSeparator parsers = do
  _ <- char sourceSpaceCharacter
  next <- lookAhead anySingle
  when (not (literalTemplatePartCanStart next))
    (rejectLiteralTemplate parsers InvalidLiteralTemplateSpacing)

literalTemplatePart
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error
      (IdentifierExpressionComposition (LiteralTemplateAtom Expression))
literalTemplatePart parsers = makeExprParser
  (literalTemplateAtom parsers)
  [[Postfix
      (OptionalExpression
        <$ char (AST.sourceOperatorCharacter AST.OptionalCharacterOperator))]]

literalTemplateAtom
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error
      (IdentifierExpressionComposition (LiteralTemplateAtom Expression))
literalTemplateAtom parsers = choice
  [ IdentifierComposition <$> literalTemplateCapture parsers
  , IdentifierComposition . LiteralTemplateGroupAtom <$> between
      (char (delimiterCharacter OpenParenthesis))
      (char (delimiterCharacter CloseParenthesis))
      (literalTemplateBody parsers)
  , IdentifierComposition <$> literalTemplateLiteral parsers
  ]

literalTemplateCapture
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error (LiteralTemplateAtom Expression)
literalTemplateCapture parsers = do
  (sourceText, captured) <- match
    (interpolationToken (literalTemplateInterpolation parsers))
  when (Text.any isSourceLineBreakCharacter sourceText)
    (rejectLiteralTemplate parsers InvalidLiteralTemplateSpacing)
  pure (LiteralTemplateCaptureAtom captured)

literalTemplateLiteral
  :: Ord error
  => LiteralTemplateParsers error
  -> Parser error (LiteralTemplateAtom Expression)
literalTemplateLiteral parsers = do
  characters <- some literalTemplateCharacter
  when (any isSpace characters)
    (rejectLiteralTemplate parsers InvalidLiteralTemplateSpacing)
  literal <-
    if all isIdentifierCharacter characters
      then pure
        (IdentifierTemplateLiteral (SimpleIdentifierString characters))
      else if all isTemplateSymbolCharacter characters
        then pure (SymbolTemplateLiteral (SymbolLiteral characters))
        else rejectLiteralTemplate parsers MixedTemplateLiteral
  pure (LiteralTemplateLiteralAtom literal)

literalTemplateCharacter :: Ord error => Parser error Char
literalTemplateCharacter =
  escapedStringCharacter [literalTemplateDelimiterCharacter]
    <|> satisfy literalTemplateRawCharacter

literalTemplateRawCharacter :: Char -> Bool
literalTemplateRawCharacter character =
  not (isSpace character)
    && character `notElem` literalTemplateStructuralCharacters

literalTemplateStructuralCharacters :: [Char]
literalTemplateStructuralCharacters =
  [ interpolationCharacter
  , delimiterCharacter OpenParenthesis
  , delimiterCharacter CloseParenthesis
  , AST.sourceOperatorCharacter AST.OptionalCharacterOperator
  , AST.sourceOperatorCharacter AST.EitherCharacterOperator
  , literalTemplateDelimiterCharacter
  , escapeCharacter
  ]

literalTemplatePartCanStart :: Char -> Bool
literalTemplatePartCanStart character =
  character == interpolationCharacter
    || character == delimiterCharacter OpenParenthesis
    || literalTemplateRawCharacter character
    || character == escapeCharacter

isTemplateSymbolCharacter :: Char -> Bool
isTemplateSymbolCharacter character =
  isAsciiCharacter character
    && not (isIdentifierCharacter character)
    && not (isSpace character)

quotedStringParts
  :: Ord error
  => Maybe (Parser error ParsedStringTemplatePart)
  -> Parser error [ParsedStringTemplatePart]
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

standardStringComment :: Ord error => Parser error ()
standardStringComment =
  char commentCharacter *> void
    (manyTill anySingle
      (lookAhead
        ( void (char stringQuoteCharacter)
          <|> void (char sourceLineFeedCharacter)
          <|> eof
        )))

standardStringCharacter :: Ord error => Parser error Char
standardStringCharacter =
  escapedStringCharacter []
    <|> satisfy
      (\character ->
        character /= stringQuoteCharacter
          && character /= escapeCharacter
          && character /= commentCharacter
          && character /= interpolationCharacter
          && isAsciiCharacter character)

escapedStringCharacter
  :: Ord error
  => [Char]
  -> Parser error Char
escapedStringCharacter additional = char escapeCharacter *>
  choice
    ( map (\character -> character <$ char character) additional
        <> [ stringQuoteCharacter <$ char stringQuoteCharacter
           , escapeCharacter <$ char escapeCharacter
           , commentCharacter <$ char commentCharacter
           , interpolationCharacter <$ char interpolationCharacter
           , AST.sourceOperatorCharacter AST.OptionalCharacterOperator
               <$ char (AST.sourceOperatorCharacter AST.OptionalCharacterOperator)
           , sourceLineFeedCharacter <$ char lineFeedEscapeCharacter
           , hexadecimalAsciiCharacter
           ]
    )

hexadecimalAsciiCharacter :: Ord error => Parser error Char
hexadecimalAsciiCharacter = do
  firstDigit <- satisfy isHexDigit
  secondDigit <- optional (satisfy isHexDigit)
  let byteValue = case secondDigit of
        Nothing -> digitToInt firstDigit
        Just digit -> 16 * digitToInt firstDigit + digitToInt digit
  pure (chr byteValue)
