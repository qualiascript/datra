{-# LANGUAGE OverloadedStrings #-}

module Parsing
  ( ResourceEnvelope (..)
  , parseDatra
  , parseDatraWithSourceName
  , parseDatraLocated
  , parseDatraLocatedWithSourceName
  , parseDatraLocatedResourceWithSourceName
  , parseDatraAst
  , parseDatraAstWithSourceName
  , parseDatraAstLocated
  , parseDatraAstLocatedWithSourceName
  ) where

import Control.Applicative (empty, optional, some, (<|>))
import Control.Monad (void)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixR, Postfix, Prefix)
  , makeExprParser
  )
import Data.Bifunctor (first)
import Data.Char (chr, digitToInt, isHexDigit, ord)
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
  ( IdentifierString (IdentifierString)
  , Expression
      ( Addition
      , AsciiStringLiteral
      , StringType
      , AtlasMap
      , EllipsisLiteral
      , EllipsisNatural
      , Exponentiation
      , MapAccess
      , MapConcatenation
      , MapExpansion
      , MapSequence
      , MapSpecification
      , IdentifierOperation
      , Multiplication
      , Subtraction
      , Minus
      , NaturalType
      , NaturalRange
      , NaturalRangeUpwards
      , SuperEllipsisRange
      , SuperEllipsisRangeMinus
      , SuperEllipsisRangePlus
      , ValuedNaturalRange
      , ValuedNaturalRangeUpwards
      , IntegerRange
      , IntegerRangeUpwards
      , IntegerRangeDownwards
      , ValuedIntegerRange
      , ValuedIntegerRangeUpwards
      , ValuedIntegerRangeDownwards
      , IntegerType
      , BooleanLiteral
      , BooleanType
      , EitherType
      , OptionalType
      , Conditional
      , Subfederation
      , Equality
      , BooleanAnd
      , BooleanOr
      , BooleanNot
      )
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
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
  , chunk
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

data ResourceEnvelope
  = ExplicitMapEnvelope
  | ImplicitMapEnvelope
  deriving (Eq, Show)

-- | Parse an in-memory Datra resource without associating it with a real
-- filesystem path. This is the entry point used by tests and other callers
-- that already have the source contents.
parseDatra :: String -> Either String Expression
parseDatra = parseDatraWithSourceName "<input>"

-- | Parse one top-level map with a source name used only in diagnostics. A
-- parenthesized expression consuming the whole resource is explicit; otherwise
-- the top-level map is implicit.
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

-- | Parse a source resource while retaining whether its outer map parentheses
-- were explicit. This is presentation metadata only; both cases produce the
-- same located expression and evaluation semantics.
parseDatraLocatedResourceWithSourceName
  :: FilePath
  -> String
  -> Either String (ResourceEnvelope, Located Expression)
parseDatraLocatedResourceWithSourceName resourceName source =
  first errorBundlePretty
    (parse locatedResourceWithEnvelope resourceName (Text.pack source))

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

locatedResourceWithEnvelope
  :: Parser (ResourceEnvelope, Located Expression)
locatedResourceWithEnvelope = do
  (sourceSpan, (envelope, expressionValue)) <-
    spanned resourceWithEnvelope
  pure (envelope, Located sourceSpan expressionValue)

locatedAstResource :: Parser (Located Expression)
locatedAstResource = located astResource

located :: Parser Expression -> Parser (Located Expression)
located parser = do
  (sourceSpan, expressionValue) <- spanned parser
  pure (Located sourceSpan expressionValue)

spanned :: Parser value -> Parser (SourceSpan, value)
spanned parser = do
  startOffset <- getOffset
  start <- getSourcePos
  value <- parser
  endOffset <- getOffset
  end <- getSourcePos
  pure
    ( SourceSpan
        (sourceName start)
        (SourcePosition
          (fromIntegral startOffset)
          (fromIntegral (unPos (sourceLine start)))
          (fromIntegral (unPos (sourceColumn start))))
        (SourcePosition
          (fromIntegral endOffset)
          (fromIntegral (unPos (sourceLine end)))
          (fromIntegral (unPos (sourceColumn end))))
    , value
    )

astResource :: Parser Expression
astResource = astSpaceConsumer *> astExpression <* eof

astExpression :: Parser Expression
astExpression = try astEmptyMap <|> astForm <|> astAtom

astEmptyMap :: Parser Expression
astEmptyMap = AtlasMap [] <$ astSymbol "()"

astAtom :: Parser Expression
astAtom =
  choice
    [ BooleanLiteral False <$ astReservedWord Reserved.FalseWord
    , BooleanLiteral True <$ astReservedWord Reserved.TrueWord
    , AsciiStringLiteral "Nothing" <$ astReservedWord Reserved.NothingWord
    , BooleanLiteral False <$ astBuiltInIdentifier Reserved.FalseIdentifier
    , BooleanLiteral True <$ astBuiltInIdentifier Reserved.TrueIdentifier
    , BooleanType <$ astReservedWord Reserved.BooleanTypeWord
    , StringType <$ astReservedWord Reserved.StringTypeWord
    , IntegerType <$ astReservedWord Reserved.IntegerTypeWord
    , NaturalType <$ astReservedWord Reserved.NaturalTypeWord
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
      , astNaturalRangeExpression
      , astIdentifierOperation AST.AssignmentOperator (Just ())
      , astIdentifierOperation AST.IdentifierTypeOperator Nothing
      , astBinary AST.ExpansionOperator MapExpansion
      , astBinary AST.RangeOperator SuperEllipsisRange
      , astUnary AST.RangePlusOperator SuperEllipsisRangePlus
      , astUnary AST.RangeMinusOperator SuperEllipsisRangeMinus
      , astBinary AST.AdditionOperator Addition
      , astBinary AST.SubtractionOperator Subtraction
      , astUnary AST.MinusOperator Minus
      , astBinary AST.SubfederationOperator Subfederation
      , astBinary AST.EqualityOperator Equality
      , astBinary AST.BooleanAndOperator BooleanAnd
      , astBinary AST.BooleanOrOperator BooleanOr
      , astUnary AST.BooleanNotOperator BooleanNot
      , astBinary AST.EitherOperator EitherType
      , astUnary AST.OptionalOperator OptionalType
      , astConditional
      , astBinary AST.MultiplicationOperator Multiplication
      , astBinary AST.ExponentiationOperator Exponentiation
      , astBinary AST.ConcatenationOperator MapConcatenation
      , astBinary AST.AccessOperator MapAccess
      , astBinary AST.SpecificationOperator MapSpecification
      ])

astIdentifierOperation
  :: AST.Operator
  -> Maybe ()
  -> Parser Expression
astIdentifierOperation operator assignmentMarker = do
  _ <- astOperatorToken operator
  identifierSpelling <- astIdentifierExpression
  operationIdentifierString <-
    IdentifierString <$> validateIdentifierSpelling identifierSpelling
  typeAnnotation <- astExpression
  case assignmentMarker of
    Nothing ->
      pure
        (IdentifierOperation operationIdentifierString typeAnnotation Nothing)
    Just () -> do
      givenValue <- optional astExpression
      pure
        (case givenValue of
          Nothing ->
            IdentifierOperation
              operationIdentifierString
              typeAnnotation
              (Just typeAnnotation)
          Just given ->
            IdentifierOperation
              operationIdentifierString typeAnnotation (Just given))

astConditional :: Parser Expression
astConditional = do
  _ <- astReservedWord Reserved.IfWord
  condition <- astExpression
  consequent <- astExpression
  alternative <- astExpression
  pure (Conditional condition consequent alternative)

astSequence :: Parser Expression
astSequence = do
  _ <- astOperatorToken AST.SequentialOperator
  firstExpression <- astExpression
  secondExpression <- astExpression
  remainingExpressions <- many astExpression
  pure
    (MapSequence
      (firstExpression : secondExpression : remainingExpressions))

data NaturalRangePrefix = RangePrefix | FromPrefix

data NaturalRangeBounds
  = NaturalRangeTo Integer Integer
  | NaturalRangeFromUpwards Integer
  | IntegerRangeFromDownwards Integer

astNaturalRangeExpression :: Parser Expression
astNaturalRangeExpression = do
  prefix <- choice
    [ RangePrefix <$ astReservedWord Reserved.RangeWord
    , FromPrefix <$ astReservedWord Reserved.FromWord
    ]
  bounds <- astNaturalRangeBounds
  pure (naturalRangeExpressionFor prefix bounds)

-- The shared @a to b@ / @a upwards@ grammar is intentionally reachable only
-- after a @range@ or @from@ prefix.
astNaturalRangeBounds :: Parser NaturalRangeBounds
astNaturalRangeBounds = do
  origin <- astSignedInteger
  choice
    [ NaturalRangeTo origin
        <$> (astReservedWord Reserved.ToWord *> astSignedInteger)
    , NaturalRangeFromUpwards origin <$ astReservedWord Reserved.UpwardsWord
    , IntegerRangeFromDownwards origin <$ astReservedWord Reserved.DownwardsWord
    ]

astSignedInteger :: Parser Integer
astSignedInteger =
  astLexeme
    (try (char '-' *> (negate <$> Lexer.decimal))
      <|> Lexer.decimal)

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

astReservedWord :: Reserved.ReservedWord -> Parser Text
astReservedWord = astSymbol . Text.pack . Reserved.reservedWordText

astBuiltInIdentifier :: Reserved.BuiltInIdentifier -> Parser Text
astBuiltInIdentifier =
  astSymbol . Text.pack . Reserved.builtInIdentifierText

astOperatorToken :: AST.Operator -> Parser Text
astOperatorToken = astSymbol . Text.pack . AST.operatorCanonicalSymbol

resource :: Parser Expression
resource = snd <$> resourceWithEnvelope

resourceWithEnvelope :: Parser (ResourceEnvelope, Expression)
resourceWithEnvelope = do
  fullSpaceConsumer
  result <- explicitResource <|> implicitResource
  fullSpaceConsumer
  eof
  pure result
  where
    explicitResource = do
      _ <- try (lookAhead outerMapEnvelope)
      (,) ExplicitMapEnvelope <$> parenthesizedExpression
    implicitResource =
      (,) ImplicitMapEnvelope <$> implicitOuterMap

-- Parse the parenthesized expression itself in lookahead so the closing
-- parenthesis must enclose the whole resource. This distinguishes an explicit
-- map from an implicit sequence such as @(a); (b)@.
outerMapEnvelope :: Parser ()
outerMapEnvelope =
  void (parenthesizedExpression <* fullSpaceConsumer <* eof)

implicitOuterMap :: Parser Expression
implicitOuterMap = do
  expressions <- elements
  pure (sequenceExpression expressions)

sequenceExpression :: [Expression] -> Expression
sequenceExpression [] = AtlasMap []
sequenceExpression [expressionValue] = expressionValue
sequenceExpression expressions = AtlasMap expressions

elements :: Parser [Expression]
elements = expression `sepEndBy` mapSeparator

-- A newline is a separator only while parsing map elements. Newlines after
-- an infix operator are consumed by 'continuedSymbol' before this parser can
-- see them.
mapSeparator :: Parser ()
mapSeparator =
  void (semicolon <* lineSpaceConsumer)
    <|> void (some lineBreak)

-- Reverse specification is the outermost expression layer. Keeping it
-- outside 'mapExpression' lets identifier operations occupy either side of
-- @<~@ without making bare identifiers valid general-purpose operands.
expression :: Parser Expression
expression = do
  target <- eitherExpression
  maybeSource <-
    optional (continuedSymbol reverseSpecificationSymbol *> expression)
  pure
    (case maybeSource of
      Nothing -> target
      Just source -> MapSpecification source target)

eitherExpression :: Parser Expression
eitherExpression =
  makeExprParser
    mapExpression
    [ [InfixR (EitherType <$ continuedOperator AST.EitherOperator)]
    , [InfixL
        (Subfederation <$ continuedWordOperator AST.SubfederationOperator)]
    , [InfixL (Equality <$ continuedOperator AST.EqualityOperator)]
    , [InfixL (BooleanAnd <$ continuedWordOperator AST.BooleanAndOperator)]
    , [InfixL (BooleanOr <$ continuedWordOperator AST.BooleanOrOperator)]
    ]

mapExpression :: Parser Expression
mapExpression =
  makeExprParser (try identifierOperation <|> rangeExpression) mapOperatorTable

-- Identifier operations are the only operands that begin with an unprefixed
-- identifier. Requiring @:@ or @:=@ here keeps bare identifiers invalid while
-- allowing a complete identifier operation in any map-operand position.
identifierOperation :: Parser Expression
identifierOperation = do
  identifierSpelling <- try identifierExpression
  isOptional <-
    maybe False (const True)
      <$> optional (operatorToken AST.OptionalOperator)
  choice
    [ do
        _ <- continuedOperator AST.AssignmentOperator
        operationIdentifierString <-
          IdentifierString
            <$> validateIdentifierSpelling identifierSpelling
        givenValue <- identifierValueExpression
        let operation =
              IdentifierOperation
                operationIdentifierString
                givenValue
                (Just givenValue)
        pure (optionalIdentifier isOptional operation givenValue)
    , do
        _ <- continuedOperator AST.IdentifierTypeOperator
        operationIdentifierString <-
          IdentifierString
            <$> validateIdentifierSpelling identifierSpelling
        typeAnnotation <- identifierValueExpression
        givenValue <-
          optional
            (continuedOperator AST.AssignmentOperator *>
              identifierValueExpression)
        let operation =
              IdentifierOperation
                operationIdentifierString typeAnnotation givenValue
        pure (optionalIdentifier isOptional operation typeAnnotation)
    ]

optionalIdentifier :: Bool -> Expression -> Expression -> Expression
optionalIdentifier False operation _ = operation
optionalIdentifier True operation missingValue =
  EitherType operation missingValue

-- Identifier annotations and assigned values may use range, arithmetic, and
-- access operators directly. Concatenation and specification are deliberately
-- excluded at this level so @,@ and @~>@ terminate the identifier operand;
-- explicit parentheses remain available when either belongs to the
-- identifier's own value.
identifierValueExpression :: Parser Expression
identifierValueExpression =
  makeExprParser rangeExpression identifierValueOperatorTable

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
term = accessedTerm termAtom

termAtom :: Parser Expression
termAtom =
  choice
    [ try parenthesizedReverseSpecification
    , parenthesizedExpression
    , try conditionalExpression
    , try naturalRangeExpression
    , BooleanLiteral False <$ reservedWord Reserved.FalseWord
    , BooleanLiteral True <$ reservedWord Reserved.TrueWord
    , AsciiStringLiteral "Nothing" <$ reservedWord Reserved.NothingWord
    , BooleanLiteral False <$ builtInIdentifier Reserved.FalseIdentifier
    , BooleanLiteral True <$ builtInIdentifier Reserved.TrueIdentifier
    , BooleanType <$ reservedWord Reserved.BooleanTypeWord
    , StringType <$ reservedWord Reserved.StringTypeWord
    , IntegerType <$ reservedWord Reserved.IntegerTypeWord
    , NaturalType <$ reservedWord Reserved.NaturalTypeWord
    , EllipsisLiteral <$ symbol (Text.pack AST.ellipsisSymbol)
    , AsciiStringLiteral <$> identifierString
    , AsciiStringLiteral <$> standardString
    , ellipsisNatural
    ]

-- Explicitly parenthesizing both operands makes a reverse specification a
-- self-contained map operand. This lets @x, (target) <~ (source)@ retain the
-- specification in the second concatenation slot, while unparenthesized
-- reverse specification remains the outermost expression layer.
parenthesizedReverseSpecification :: Parser Expression
parenthesizedReverseSpecification = do
  target <- parenthesizedExpression
  _ <- continuedSymbol reverseSpecificationSymbol
  source <- parenthesizedExpression
  _ <- notFollowedBy (try (continuedSymbol reverseSpecificationSymbol))
  pure (MapSpecification source target)

conditionalExpression :: Parser Expression
conditionalExpression = do
  _ <- continuedReservedWord Reserved.IfWord
  condition <- expression
  _ <- continuedReservedWord Reserved.ThenWord
  consequent <- expression
  alternative <-
    maybe (AtlasMap []) id
      <$> optional (continuedReservedWord Reserved.ElseWord *> expression)
  pure (Conditional condition consequent alternative)

rangeEndpointTerm :: Parser Expression
rangeEndpointTerm = accessedTerm rangeEndpointAtom

rangeEndpointAtom :: Parser Expression
rangeEndpointAtom =
  choice
    [ parenthesizedExpression
    , AsciiStringLiteral <$> identifierString
    , AsciiStringLiteral <$> standardString
    , ellipsisNatural
    ]

-- Bracket access is a postfix part of the primary expression, so it binds
-- before arithmetic and every map-level operator. Repetition associates left:
-- @source[first][second]@ accesses the first result at @second@.
accessedTerm :: Parser Expression -> Parser Expression
accessedTerm atom = do
  source <- atom
  insertions <- many bracketedInsertion
  pure (foldl MapAccess source insertions)

bracketedInsertion :: Parser Expression
bracketedInsertion =
  between
    (symbol "[" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol "]")
    expression

naturalRangeExpression :: Parser Expression
naturalRangeExpression = do
  prefix <- choice
    [ RangePrefix <$ continuedReservedWord Reserved.RangeWord
    , FromPrefix <$ continuedReservedWord Reserved.FromWord
    ]
  bounds <- naturalRangeBounds
  pure (naturalRangeExpressionFor prefix bounds)

-- The shared @a to b@ / @a upwards@ grammar is intentionally reachable only
-- after a @range@ or @from@ prefix.
naturalRangeBounds :: Parser NaturalRangeBounds
naturalRangeBounds = do
  origin <- signedIntegerToken <* keywordSeparator
  choice
    [ NaturalRangeTo origin
        <$> (continuedReservedWord Reserved.ToWord *> lexeme signedIntegerToken)
    , NaturalRangeFromUpwards origin <$ reservedWord Reserved.UpwardsWord
    , IntegerRangeFromDownwards origin <$ reservedWord Reserved.DownwardsWord
    ]

signedIntegerToken :: Parser Integer
signedIntegerToken =
  try (char '-' *> (negate <$> Lexer.decimal))
    <|> try
      (keywordToken
        (Text.pack (AST.operatorCanonicalSymbol AST.MinusOperator))
        *> keywordSeparator
        *> (negate <$> Lexer.decimal))
    <|> Lexer.decimal

naturalRangeExpressionFor
  :: NaturalRangePrefix
  -> NaturalRangeBounds
  -> Expression
naturalRangeExpressionFor RangePrefix (NaturalRangeTo origin target) =
  if origin >= 0 && target >= 0
    then NaturalRange (fromInteger origin) (fromInteger target)
    else IntegerRange origin target
naturalRangeExpressionFor RangePrefix (NaturalRangeFromUpwards origin) =
  if origin >= 0
    then NaturalRangeUpwards (fromInteger origin)
    else IntegerRangeUpwards origin
naturalRangeExpressionFor RangePrefix (IntegerRangeFromDownwards origin) =
  IntegerRangeDownwards origin
naturalRangeExpressionFor FromPrefix (NaturalRangeTo origin target) =
  if origin >= 0 && target >= 0
    then ValuedNaturalRange (fromInteger origin) (fromInteger target)
    else ValuedIntegerRange origin target
naturalRangeExpressionFor FromPrefix (NaturalRangeFromUpwards origin) =
  if origin >= 0
    then ValuedNaturalRangeUpwards (fromInteger origin)
    else ValuedIntegerRangeUpwards origin
naturalRangeExpressionFor FromPrefix (IntegerRangeFromDownwards origin) =
  ValuedIntegerRangeDownwards origin

keyword :: Text -> Parser Text
keyword value = lexeme (keywordToken value)

reservedWord :: Reserved.ReservedWord -> Parser Text
reservedWord = keyword . Text.pack . Reserved.reservedWordText

builtInIdentifier :: Reserved.BuiltInIdentifier -> Parser Text
builtInIdentifier = keyword . Text.pack . Reserved.builtInIdentifierText

continuedKeyword :: Text -> Parser Text
continuedKeyword value = keywordToken value <* keywordSeparator

continuedReservedWord :: Reserved.ReservedWord -> Parser Text
continuedReservedWord =
  continuedKeyword . Text.pack . Reserved.reservedWordText

continuedWordOperator :: AST.Operator -> Parser Text
continuedWordOperator =
  continuedKeyword . Text.pack . AST.operatorCanonicalSymbol

keywordToken :: Text -> Parser Text
keywordToken value =
  try
    (value <$ chunk value
      <* notFollowedBy (satisfy isCanonicalCharacter))

keywordSeparator :: Parser ()
keywordSeparator =
  void (some (void space1 <|> lineComment))

parenthesizedExpression :: Parser Expression
parenthesizedExpression =
  between
    (symbol "(" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol ")")
    (sequenceExpression <$> elements)

-- Arithmetic follows Haskell and binds more tightly than range construction.
arithmeticOperatorTable :: [[Operator Parser Expression]]
arithmeticOperatorTable =
  [ [Postfix (OptionalType <$ operatorToken AST.OptionalOperator)]
  , [InfixR (Exponentiation <$ continuedOperator AST.ExponentiationOperator)]
  , [ Prefix (Minus <$ operatorToken AST.MinusOperator)
    , Prefix (Minus <$ continuedWordOperator AST.MinusOperator)
    , Prefix (BooleanNot <$ continuedWordOperator AST.BooleanNotOperator)
    ]
  , [InfixL (Multiplication <$ continuedOperator AST.MultiplicationOperator)]
  , [ InfixL (Addition <$ continuedOperator AST.AdditionOperator)
    , InfixL (Subtraction <$ continuedOperator AST.SubtractionOperator)
    ]
  ]

-- Concatenation binds after ranges. Access and forward specification share a
-- left-associative level so their written order determines composition:
-- @source ~> target @ insertion@ accesses the resulting specification, while
-- @source @ insertion ~> target@ specifies the accessed value. Reverse
-- specification is parsed by the outer 'expression' layer so identifier
-- operations can occur on either side of a reversed chain.
mapOperatorTable :: [[Operator Parser Expression]]
mapOperatorTable =
  [ [InfixR (MapConcatenation <$ infixComma)]
  , [Postfix (finishConcatenation <$ trailingComma)]
  , mapAccessAndSpecificationOperators
  ]

identifierValueOperatorTable :: [[Operator Parser Expression]]
identifierValueOperatorTable =
  [[InfixL (MapAccess <$ continuedOperator AST.AccessOperator)]]

mapAccessAndSpecificationOperators :: [Operator Parser Expression]
mapAccessAndSpecificationOperators =
  [ InfixL (MapAccess <$ continuedOperator AST.AccessOperator)
  , InfixL
      (MapSpecification <$ continuedOperator AST.SpecificationOperator)
  ]

reverseSpecificationSymbol :: Text
reverseSpecificationSymbol = "<~"

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
  void (choice [char ')', char ']', char ';']) <|> eof

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
        , operatorToken AST.SpecificationOperator
        , operatorToken AST.AssignmentOperator
        , symbol reverseSpecificationSymbol
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

bareIdentifier :: Parser String
bareIdentifier = lexeme bareIdentifierToken

astBareIdentifier :: Parser String
astBareIdentifier = astLexeme bareIdentifierToken

data IdentifierSpelling
  = BareIdentifier String
  | FullStringIdentifier String

identifierExpression :: Parser IdentifierSpelling
identifierExpression =
  FullStringIdentifier <$> standardString
    <|> BareIdentifier <$> bareIdentifier

astIdentifierExpression :: Parser IdentifierSpelling
astIdentifierExpression =
  FullStringIdentifier <$> astStandardString
    <|> BareIdentifier <$> astBareIdentifier

validateIdentifierSpelling :: IdentifierSpelling -> Parser String
validateIdentifierSpelling (FullStringIdentifier value) = pure value
validateIdentifierSpelling (BareIdentifier value)
  | not (Reserved.isReservedIdentifierString value) = pure value
  | otherwise = empty

bareIdentifierToken :: Parser String
bareIdentifierToken =
  (:)
    <$> satisfy isLeadingCanonicalCharacter
    <*> many (satisfy isCanonicalCharacter)

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
      , '$' <$ char '$'
      , '\n' <$ char 'n'
      , hexadecimalAsciiCharacter
      ])
    <|> satisfy
      (\character ->
        character /= '"'
          && character /= '\\'
          && character /= '#'
          && character /= '$'
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
