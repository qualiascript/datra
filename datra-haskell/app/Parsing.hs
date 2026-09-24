{-# LANGUAGE OverloadedStrings #-}

module Parsing
  ( ResourceEnvelope (..)
  , parseDatra
  , sourceImports
  , parseDatraLocatedWithSyntaxImports
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
import Control.Monad (guard, void)
import Control.Monad.Trans.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixR, Postfix, Prefix)
  , makeExprParser
  )
import Data.Bifunctor qualified as Bifunctor
import Data.List (nubBy)
import Data.Maybe (catMaybes)
import Data.Char (chr, digitToInt, isHexDigit, ord)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
  ( IdentifierString (IdentifierString)
  , Expression
      ( Addition
      , AsciiStringLiteral
      , StringTemplate
      , AtlasMap
      , ArgumentMap
      , EllipsisLiteral
      , EllipsisNatural
      , Exponentiation
      , NamedAccess
      , MapAccess
      , MapConcatenation
      , MapExpansion
      , MapSequence
      , MapSpecification
      , Overload
      , IdentifierOperation
      , Multiplication
      , Subtraction
      , Minus
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
      , EitherType
      , OptionalType
      , Conditional
      , Subfederation
      , Equality
      , BooleanAnd
      , BooleanOr
      , BooleanNot
      , Extract
      , Eval
      , Assert
      , Begin
      , Program
      , FunctionType
      , SyntaxType
      , This
      , InModule
      , Import
      , FunctionBody
      , FunctionApplication
      , External
      , Let
      , IdentifierReference
      )
  , StringTemplatePart
      ( StringTemplateInterpolation
      , StringTemplateLiteral
      , StringTemplateWeakInterpolation
      )
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
import ModuleNames (isPrivateIdentifier, moduleIdentifier)
import StandardLibrary (standardLibrarySource)
import SyntaxDefinitions
import DatraLanguage.AST.Reserved.Bootstrap
  ( reservedSymbolReplacements
  )
import DatraLanguage.Diagnostics
  ( Located (Located, locatedValue)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import IdentifierValueType
  ( isIdentifierValue
  , isIdentifierValueCharacter
  )
import Text.Megaparsec
  ( Parsec
  , ParseErrorBundle
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
  , runParser
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

-- Lexical parser context is scoped with ReaderT, so backtracking cannot leak
-- block references or interpolation comment boundaries into surrounding code.
data ParserContext = ParserContext
  { interpolationDepth :: Int
  , referencesAllowed :: Bool
  , syntaxRules :: [SyntaxRule]
  , syntaxStops :: [Text]
  , syntaxImports :: [(String, [SyntaxRule])]
  }

type Parser = ReaderT ParserContext (Parsec Void Text)

data ResourceEnvelope
  = ExplicitMapEnvelope
  | ImplicitBlockEnvelope
  deriving (Eq, Show)

-- | Parse an in-memory Datra resource without associating it with a real
-- filesystem path. This is the entry point used by tests and other callers
-- that already have the source contents.
parseDatra :: String -> Either String Expression
parseDatra = parseDatraWithSourceName "<input>"

-- | Outer parentheses select expression mode; every other resource is an
-- implicit begin/yield program, with an optional begin and default yield ().
parseDatraWithSourceName :: FilePath -> String -> Either String Expression
parseDatraWithSourceName sourceName source =
  locatedValue <$> parseDatraLocatedWithSourceName sourceName source

parseDatraLocated :: String -> Either String (Located Expression)
parseDatraLocated = parseDatraLocatedWithSourceName "<input>"

parseDatraLocatedWithSourceName
  :: FilePath
  -> String
  -> Either String (Located Expression)
parseDatraLocatedWithSourceName = parseDatraLocatedWithSyntaxImports []

parseDatraLocatedWithSyntaxImports :: [(String, [SyntaxRule])] -> FilePath -> String -> Either String (Located Expression)
parseDatraLocatedWithSyntaxImports imports resourceName source =
  Bifunctor.first errorBundlePretty (runParser
    (runReaderT locatedResource (ParserContext 0 False libraryRules [] imports))
    resourceName (Text.pack source))

-- | Parse a source resource and retain its expression/program envelope.
parseDatraLocatedResourceWithSourceName
  :: FilePath
  -> String
  -> Either String (ResourceEnvelope, Located Expression)
parseDatraLocatedResourceWithSourceName resourceName source =
  Bifunctor.first errorBundlePretty
    (runDatraParser
      locatedResourceWithEnvelope resourceName (Text.pack source))

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
  Bifunctor.first errorBundlePretty
    (runDatraParser locatedAstResource resourceName (Text.pack source))

runDatraParser
  :: Parser value
  -> FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) value
runDatraParser parser resourceName source =
  runParser (runReaderT parser (ParserContext 0 False libraryRules [] [])) resourceName source

libraryDeclarations :: [Expression]
libraryDeclarations = case runParser (runReaderT resource (ParserContext 0 False [] [] []))
    "standard_library.datra" (Text.pack standardLibrarySource) of
  Right (Program declarations _) -> declarations
  _ -> []

libraryRules :: [SyntaxRule]
libraryRules = rules <> [rule { syntaxName = "StandardLibrary." <> syntaxName rule } | rule <- rules]
  where
    rules =
      [ rule { syntaxModule = Just "standard_library" }
      | rule <- concatMap declarationRules libraryDeclarations
      , not (isPrivateIdentifier (syntaxName rule))
      ]

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
astAtom = astLexeme (This <$ keywordToken "this" <|> choice
  [ replacement <$ keywordToken (Text.pack (Reserved.reservedSymbolIdentifierString reserved))
  | (reserved, replacement) <- reservedSymbolReplacements
  ] <|> atomicExpressionToken astStringTemplateToken)

atomicExpressionToken :: Parser Expression -> Parser Expression
atomicExpressionToken nestedStringTemplate =
  choice
    [ EllipsisLiteral <$ chunk (Text.pack AST.ellipsisSymbol)
    , AsciiStringLiteral <$> identifierStringToken
    , nestedStringTemplate
    , EllipsisNatural <$> Lexer.decimal
    ]

astForm :: Parser Expression
astForm =
  between (astSymbol "(") (astSymbol ")")
    (choice
      [ InModule <$> (astSymbol "in-module" *> astString) <*> astExpression
      , Import True <$> (astSymbol "import-all" *> astString)
      , Import False <$> (astSymbol "import" *> astString)
      , Assert True <$> (astSymbol "assert-hard" *> astExpression)
      , astUnary AST.AssertOperator (Assert False)
      , SyntaxType <$> (astSymbol "as?" *> astString) <*> pure True <*> astExpression
      , SyntaxType <$> (astSymbol "as" *> astString) <*> pure False <*> astExpression
      , astBinary AST.FunctionTypeOperator FunctionType
      , astBinary AST.ApplicationOperator FunctionApplication
      , astUnary AST.ExternalOperator External
      , astBlock "do" FunctionBody
      , astSequence
      , ArgumentMap <$> (astSymbol "{}" *> many astExpression)
      , astNaturalRangeExpression
      , astIdentifierOperation AST.AssignmentOperator (Just ())
      , astIdentifierOperation AST.DependentIdentifierTypeOperator Nothing
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
      , astUnary AST.ExtractOperator Extract
      , astBinary AST.EvalOperator Eval
      , astBlock "begin" Begin
      , astBlock "program" Program
      , astUnary AST.LetOperator Let
      , IdentifierReference . IdentifierString <$>
          (astSymbol "ref" *> astString)
      , astBinary AST.EitherOperator EitherType
      , astUnary AST.OptionalOperator OptionalType
      , astConditional
      , astBinary AST.MultiplicationOperator Multiplication
      , astBinary AST.ExponentiationOperator Exponentiation
      , astBinary AST.ConcatenationOperator MapConcatenation
      , NamedAccess <$> (astSymbol "." *> astExpression) <*> (IdentifierString <$> astString)
      , astBinary AST.AccessOperator MapAccess
      , astBinary AST.SpecificationOperator MapSpecification
      , astBinary AST.OverloadOperator Overload
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
  _ <- astReservedSymbol Reserved.IfSymbol
  condition <- astExpression
  consequent <- astExpression
  alternative <- astExpression
  pure (Conditional condition consequent alternative)

astBlock :: Text -> ([Expression] -> Expression -> Expression) -> Parser Expression
astBlock blockKeyword construct = do
  _ <- astSymbol blockKeyword
  bindings <- between (astSymbol "(") (astSymbol ")")
    (astSymbol "bindings" *> many astExpression)
  construct bindings <$> astExpression

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
    [ RangePrefix <$ astReservedSymbol Reserved.RangeSymbol
    , FromPrefix <$ astReservedSymbol Reserved.FromSymbol
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

astReservedSymbol :: Reserved.ReservedSymbol -> Parser Text
astReservedSymbol =
  astSymbol . Text.pack . Reserved.reservedSymbolIdentifierString

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
      (,) ImplicitBlockEnvelope <$> implicitProgram

-- Parse the parenthesized expression itself in lookahead so the closing
-- parenthesis must enclose the whole resource. This distinguishes an explicit
-- map from an implicit sequence such as @(a); (b)@.
outerMapEnvelope :: Parser ()
outerMapEnvelope =
  void (withReferences parenthesizedExpression <* fullSpaceConsumer <* eof)

implicitProgram :: Parser Expression
implicitProgram = withReferences $ do
  _ <- optional (continuedWordOperator AST.BeginOperator)
  bindings <- elements
  result <- withDeclarations bindings $ optional (continuedReservedWord Reserved.YieldWord *> expression)
  pure (Program bindings (maybe (AtlasMap []) id result))

withReferences :: Parser value -> Parser value
withReferences = local (\context -> context { referencesAllowed = True })

sequenceExpression :: [Expression] -> Expression
sequenceExpression [] = AtlasMap []
sequenceExpression [expressionValue] = expressionValue
sequenceExpression expressions = AtlasMap expressions

withDeclarations :: [Expression] -> Parser a -> Parser a
withDeclarations entries = local $ \context -> context
  { syntaxRules = concatMap (rulesFor context) entries <> syntaxRules context }
  where
    rulesFor context (Import allNames path) =
      let rules = maybe [] id (lookup path (syntaxImports context))
          qualified = [rule { syntaxName = moduleIdentifier path <> "." <> syntaxName rule } | rule <- rules]
      in qualified <> if allNames then rules else []
    rulesFor _ entry = declarationRules entry

elements :: Parser [Expression]
elements = do
  first <- optional expression
  case first of
    Nothing -> pure []
    Just entry -> withDeclarations [entry] $ do
      more <- optional mapSeparator
      rest <- case more of Nothing -> pure []; Just _ -> elements
      pure (entry : rest)

-- A newline is a separator only while parsing map elements. Newlines after
-- an infix operator are consumed by 'continuedSymbol' before this parser can
-- see them.
mapSeparator :: Parser ()
mapSeparator =
  void (semicolon <* lineSpaceConsumer)
    <|> void (some lineBreak)

-- Reverse specification is the outermost expression layer, so either side
-- can contain identifier operations, concatenation, and function applications.
expression :: Parser Expression
expression = assertExpression <|> expressionWith mapExpression

assertExpression :: Parser Expression
assertExpression = do
  _ <- continuedWordOperator AST.AssertOperator
  hard <- maybe False (const True) <$> optional (try (continuedKeyword "hard"))
  Assert hard <$> expression

expressionWith :: Parser Expression -> Parser Expression
expressionWith operand = do
  target <- functionExpressionWith operand
  maybeSource <-
    optional (continuedSymbol reverseSpecificationSymbol *> expressionWith operand)
  pure
    (case maybeSource of
      Nothing -> target
      Just source -> MapSpecification source target)

functionExpressionWith :: Parser Expression -> Parser Expression
functionExpressionWith operand = do
  signature <- arrowExpressionWith operand
  implementation <- optional (functionImplementation signature)
  pure (maybe signature (`MapSpecification` signature) implementation)

-- A bare @yield@ is a function implementation only after an actual function
-- type.  Without this guard it can consume the yield belonging to the
-- surrounding resource or begin block after any preceding expression.
functionImplementation :: Expression -> Parser Expression
functionImplementation signature =
  functionBody
    <|> bareFunctionYield
    <|> externalExpression
  where
    bareFunctionYield = case signature of
      FunctionType {} ->
        FunctionBody []
          <$> (sameLineReservedWord Reserved.YieldWord *> expression)
      _ -> empty

-- The compact function form is deliberately line-bound: a newline otherwise
-- makes @yield@ indistinguishable from the enclosing block's result.  The
-- explicit @do@/optional @begin@ forms are the multiline escape hatch.
sameLineReservedWord :: Reserved.ReservedWord -> Parser Text
sameLineReservedWord reserved =
  keywordToken (Text.pack (Reserved.reservedWordText reserved)) <* hspace1

arrowExpressionWith :: Parser Expression -> Parser Expression
arrowExpressionWith operand = do
  rawInput <- eitherExpressionWith operand
  input <- syntaxTypeSuffix rawInput operand
  output <- optional (continuedOperator AST.FunctionTypeOperator *> arrowExpressionWith operand)
  pure (maybe input (FunctionType input) output)

syntaxTypeSuffix :: Expression -> Parser Expression -> Parser Expression
syntaxTypeSuffix input operand = case input of
  AsciiStringLiteral patternText -> do
    signature <- optional $ do
      _ <- keywordToken "as"
      ordinary <- maybe False (const True) <$> optional (char '?')
      lineSpaceConsumer
      SyntaxType patternText ordinary <$> arrowExpressionWith operand
    pure (maybe input id signature)
  _ -> pure input

eitherExpressionWith :: Parser Expression -> Parser Expression
eitherExpressionWith operand =
  makeExprParser
    operand
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

-- A colon distinguishes a declaration from a bare lexical reference or call.
identifierOperation :: Parser Expression
identifierOperation = do
  identifierSpelling <- try identifierExpression
  isOptional <-
    maybe False (const True)
      <$> optional (operatorToken AST.OptionalOperator)
  guard
    (not
      (isOptional
        && isPrivateIdentifier
          (case identifierSpelling of
            BareIdentifier name -> name
            FullStringIdentifier name -> name)))
  choice
    [ do
        _ <- continuedOperator AST.AssignmentOperator
        let name = case identifierSpelling of BareIdentifier value -> value; FullStringIdentifier value -> value
            operationIdentifierString = IdentifierString name
        givenValue <- identifierValueExpression
        let proposed = IdentifierOperation operationIdentifierString givenValue (Just givenValue)
        if null (declarationRules proposed) then void (validateIdentifierSpelling identifierSpelling) else pure ()
        let operation =
              IdentifierOperation
                operationIdentifierString
                givenValue
                (Just givenValue)
        pure (optionalIdentifier isOptional operation givenValue)
    , do
        _ <- continuedOperator AST.DependentIdentifierTypeOperator
        operationIdentifierString <-
          IdentifierString
            <$> pure (case identifierSpelling of BareIdentifier name -> name; FullStringIdentifier name -> name)
        typeAnnotation <- identifierValueExpression
        case typeAnnotation of
          SyntaxType {} -> pure ()
          _ -> void (validateIdentifierSpelling identifierSpelling)
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
identifierValueExpression = do
  rawInput <- makeExprParser rangeExpression identifierValueOperatorTable
  input <- syntaxTypeSuffix rawInput (makeExprParser rangeExpression identifierValueOperatorTable)
  output <- optional (continuedOperator AST.FunctionTypeOperator *> arrowExpressionWith
    (makeExprParser rangeExpression identifierValueOperatorTable))
  let signature = maybe input (FunctionType input) output
  implementation <- optional (functionImplementation signature)
  pure (maybe signature (`MapSpecification` signature) implementation)

-- An arithmetic operator followed by another identifier operation belongs to
-- the surrounding expression. Otherwise it remains part of this identifier's
-- annotation or assigned value, preserving forms such as @x : 2 + 3@.
boundaryAwareArithmeticExpression :: Parser Expression
boundaryAwareArithmeticExpression =
  makeExprParser term boundaryAwareArithmeticOperatorTable

-- Ranges have a small dedicated grammar so exactly one unparenthesized '..'
-- is permitted at this precedence level. Each explicit endpoint is a complete
-- arithmetic expression; nested ranges therefore require parentheses.
rangeExpression :: Parser Expression
rangeExpression =
  try prefixRange
    <|> try explicitRange
    <|> boundaryAwareArithmeticExpression

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

-- A bare Ellipsis value cannot be a range endpoint. Parentheses deliberately
-- return to the complete expression grammar, making forms such as '(...)..'
-- explicit while keeping grouping out of the AST.
rangeEndpoint :: Parser Expression
rangeEndpoint = makeExprParser rangeEndpointTerm arithmeticOperatorTable

term :: Parser Expression
term = do
  function <- accessedTerm extractedTermAtom
  arguments <- many (try (notFollowedBy (try identifierOperationStart) *> applicationArgument))
  pure (foldl FunctionApplication function arguments)
  where
    -- Horizontal whitespace has already been consumed by lexemes. A newline
    -- remains a block boundary; operator and syntax words cannot be arguments.
    applicationArgument = accessedTerm (choice
      [ argumentMap
      , parenthesizedExpression
      , lexeme (atomicExpressionToken sourceStringTemplateToken)
      , identifierReference
      ])

-- Extract binds to its primary operand before bracket access, so @%a[x]@
-- means @(%a)[x]@. A larger specification operand remains available through
-- ordinary parentheses.
extractedTermAtom :: Parser Expression
extractedTermAtom =
  (Extract <$> (operatorToken AST.ExtractOperator *> extractedTermAtom))
    <|> termAtom

termAtom :: Parser Expression
termAtom =
  choice
    [ This <$ keyword "this"
    , importExpression
    , syntaxApplication
    , bootstrapLet
    , externalExpression
    , argumentMap
    , try parenthesizedReverseSpecification
    , parenthesizedExpression
    , lexeme (atomicExpressionToken sourceStringTemplateToken)
    , identifierReference
    ]

importExpression :: Parser Expression
importExpression = do
  _ <- continuedKeyword "import"
  allNames <- maybe False (const True) <$> optional (continuedKeyword "all")
  Import allNames <$> standardString

-- Scan import literals without interpreting strings as syntax. This allows the
-- loader to resolve dependencies before parsing expressions using their names.
sourceImports :: String -> Either String [String]
sourceImports source = Bifunctor.first errorBundlePretty $
  runParser (runReaderT scan (ParserContext 0 False libraryRules [] [])) "<imports>" (Text.pack source)
  where
    paths (Import _ path) = [path]
    paths _ = []
    scan = concat <$> many item <* eof
    item = try (paths <$> importExpression)
      <|> ([] <$ sourceStringTemplateToken)
      <|> ([] <$ lineComment)
      <|> ([] <$ anySingle)

syntaxApplication :: Parser Expression
syntaxApplication = do
  name <- lookAhead $ do
    first <- bareIdentifierToken
    rest <- many (try (char '.' <* notFollowedBy (char '.') *> bareIdentifierToken))
    pure (foldl (\left right -> left <> "." <> right) first rest)
  rules <- filter ((== name) . syntaxName) . syntaxRules <$> ask
  candidates <- catMaybes <$> traverse (\rule -> optional $ try $ lookAhead $ do
    value <- parseRule rule
    end <- getOffset
    pure (rule, value, end)) rules
  case candidates of
    [] -> empty
    _ -> do
      let furthest = maximum [end | (_,_,end) <- candidates]
          best = nubBy (\(_,a,_) (_,b,_) -> a == b)
            [candidate | candidate@(_,_,end) <- candidates, end == furthest]
      case best of
        [(rule,_,_)] -> parseRule rule
        _ -> fail ("ambiguous AST pattern for " <> name)
  where
    parseRule rule = do
      _ <- continuedKeyword (Text.pack (syntaxName rule))
      captures <- parsePieces (syntaxPieces rule)
      expanded <- either fail pure (expandSyntax rule captures)
      case expanded of
        Let _ -> ask >>= guard . referencesAllowed
        _ -> pure ()
      pure expanded
    obviouslyNumeric (EllipsisNatural _) = True
    obviouslyNumeric (Minus value) = obviouslyNumeric value
    obviouslyNumeric _ = False
    parsePieces [] = pure []
    parsePieces (SyntaxLiteral token : rest) = do
      lineSpaceConsumer
      _ <- if all (`elem` (",;" :: String)) token
        then continuedSymbol (Text.pack token) else keyword (Text.pack token) <* lineSpaceConsumer
      parsePieces rest
    parsePieces (SyntaxHole kind : rest) = do
      lineSpaceConsumer
      let stops = case take 1 rest of
            [SyntaxLiteral token] -> [Text.pack token]
            [SyntaxHole nextType] -> map Text.pack (declarationLiterals libraryDeclarations nextType)
            _ -> []
          literal = choice [AsciiStringLiteral value <$ (keyword (Text.pack value) <* lineSpaceConsumer)
            | value <- declarationLiterals libraryDeclarations kind]
      value <- local (\context -> context { syntaxStops = stops <> syntaxStops context }) $
        if kind `elem` ["Block", "Pages"] then do
          entries <- withReferences elements
          guard (kind == "Block" || not (null entries))
          pure (AtlasMap entries)
        else literal <|> (if kind /= "Expr" then boundaryAwareArithmeticExpression
          else if "," `elem` stops then nonConcatenatedExpression else expression)
      let enums = declarationLiterals libraryDeclarations kind
      guard (null enums || not (obviouslyNumeric value))
      let continue = (value :) <$> parsePieces rest
      case value of
        AtlasMap entries | kind == "Block" -> withDeclarations entries continue
        _ -> continue

functionBody :: Parser Expression
functionBody = try $ do
  body <- syntaxApplication
  case body of
    FunctionBody {} -> pure body
    Begin bindings result -> pure (FunctionBody bindings result)
    _ -> empty

externalExpression :: Parser Expression
externalExpression = External <$> (continuedWordOperator AST.ExternalOperator *> (stringExpression <|> parenthesizedExpression))

-- Bootstrap only the declaration prefix needed to read the library itself.
bootstrapLet :: Parser Expression
bootstrapLet = do
  rules <- syntaxRules <$> ask
  guard (null rules)
  _ <- continuedWordOperator AST.LetOperator
  Let <$> expression

identifierReference :: Parser Expression
identifierReference = try $ do
  stops <- syntaxStops <$> ask
  mapM_ (notFollowedBy . keywordToken) stops
  first <- bareIdentifierToken
  horizontalSpaceConsumer
  name <- validateIdentifierSpelling (BareIdentifier first)
  pure (IdentifierReference (IdentifierString name))

-- Argument maps have the same member separators and empty/unary arity as
-- parenthesized maps, but admit every permutation of their members.
argumentMap :: Parser Expression
argumentMap =
  ArgumentMap <$>
    between (symbol "{" <* lineSpaceConsumer)
      (lineSpaceConsumer *> symbol "}")
      (argumentExpression `sepEndBy` argumentSeparator)
  where
    -- At the brace level commas separate arguments. Parsing a parenthesized
    -- expression restores ordinary concatenation, preserving nested maps.
    argumentExpression = nonConcatenatedExpression
    argumentSeparator =
      void (continuedOperator AST.ConcatenationOperator)
        <|> mapSeparator

-- Shared operand grammar where an unparenthesized comma is a delimiter.
nonConcatenatedExpression :: Parser Expression
nonConcatenatedExpression = expressionWith
  (makeExprParser (try identifierOperation <|> rangeExpression)
    (arithmeticOperatorTable <> [mapAccessAndSpecificationOperators]))

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

rangeEndpointTerm :: Parser Expression
rangeEndpointTerm = accessedTerm rangeEndpointAtom

rangeEndpointAtom :: Parser Expression
rangeEndpointAtom =
  choice
    [ parenthesizedExpression
    , AsciiStringLiteral <$> identifierString
    , stringExpression
    , ellipsisNatural
    ]

-- Bracket access is a postfix part of the primary expression, so it binds
-- before arithmetic and every map-level operator. Repetition associates left:
-- @source[first][second]@ accesses the first result at @second@.
accessedTerm :: Parser Expression -> Parser Expression
accessedTerm atom = do
  source <- atom
  selections <- many (choice
    [ (\insertion value -> MapAccess value insertion) <$> bracketedInsertion
    , do
        _ <- try (char '.' <* notFollowedBy (char '.'))
        horizontalSpaceConsumer
        name <- IdentifierString <$> (bareIdentifierToken <|> standardStringToken)
        horizontalSpaceConsumer
        pure (`NamedAccess` name)
    ])
  pure (foldl (\value select -> select value) source selections)

bracketedInsertion :: Parser Expression
bracketedInsertion =
  between
    (symbol "[" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol "]")
    expression

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
  arithmeticOperatorTableWith continuedOperator

boundaryAwareArithmeticOperatorTable :: [[Operator Parser Expression]]
boundaryAwareArithmeticOperatorTable =
  arithmeticOperatorTableWith operatorBeforeIdentifierBoundary

arithmeticOperatorTableWith
  :: (AST.Operator -> Parser Text)
  -> [[Operator Parser Expression]]
arithmeticOperatorTableWith infixOperator =
  [ [Postfix (OptionalType <$ operatorToken AST.OptionalOperator)]
  , [InfixR (Exponentiation <$ infixOperator AST.ExponentiationOperator)]
  , [ Prefix (Minus <$ operatorToken AST.MinusOperator)
    , Prefix (Minus <$ continuedWordOperator AST.MinusOperator)
    , Prefix (BooleanNot <$ continuedWordOperator AST.BooleanNotOperator)
    ]
  , [InfixL (Multiplication <$ infixOperator AST.MultiplicationOperator)]
  , [ InfixL (Addition <$ infixOperator AST.AdditionOperator)
    , InfixL (Subtraction <$ infixOperator AST.SubtractionOperator)
    ]
  ]

operatorBeforeIdentifierBoundary :: AST.Operator -> Parser Text
operatorBeforeIdentifierBoundary operator =
  try
    (continuedOperator operator
      <* notFollowedBy (try identifierOperationStart))

identifierOperationStart :: Parser ()
identifierOperationStart = do
  identifierSpelling <- identifierExpression
  _ <- validateIdentifierSpelling identifierSpelling
  _ <- optional (operatorToken AST.OptionalOperator)
  void
    (operatorToken AST.AssignmentOperator
      <|> operatorToken AST.DependentIdentifierTypeOperator)

-- Concatenation binds after ranges. Access and forward specification share a
-- left-associative level so their written order determines composition:
-- @source ~> target @ insertion@ accesses the resulting specification, while
-- @source @ insertion ~> target@ specifies the accessed value. Reverse
-- specification is parsed by the outer 'expression' layer so identifier
-- operations can occur on either side of a reversed chain.
mapOperatorTable :: [[Operator Parser Expression]]
mapOperatorTable =
  arithmeticOperatorTable
    <> [ [InfixR (MapConcatenation <$ infixComma)]
       , [Postfix (finishConcatenation <$ trailingComma)]
       , mapAccessAndSpecificationOperators
       ]

identifierValueOperatorTable :: [[Operator Parser Expression]]
identifierValueOperatorTable =
  [[InfixL (MapAccess <$ continuedOperator AST.AccessOperator)]]

mapAccessAndSpecificationOperators :: [Operator Parser Expression]
mapAccessAndSpecificationOperators =
  [ InfixL (MapAccess <$ continuedOperator AST.AccessOperator)
  , InfixL (Overload <$ continuedOperator AST.OverloadOperator)
  , InfixL (flip Overload <$ continuedOperator AST.ReverseOverloadOperator)
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
  void (choice [char ')', char ']', char '}', char ';']) <|> eof

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
        , operatorToken AST.OverloadOperator
        , operatorToken AST.ReverseOverloadOperator
        , operatorToken AST.AssignmentOperator
        , symbol reverseSpecificationSymbol
        ])

ellipsisNatural :: Parser Expression
ellipsisNatural = EllipsisNatural <$> lexeme Lexer.decimal

-- | The compact identifier spelling. Consume the whole identifier-character
-- run before validation so @$345abc@ is one token rather than two expressions.
identifierString :: Parser String
identifierString = lexeme identifierStringToken

identifierStringToken :: Parser String
identifierStringToken = do
  _ <- char '$'
  value <- some (satisfy isIdentifierValueCharacter)
  if isIdentifierValue value then pure value else empty

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

astString :: Parser String
astString = astLexeme identifierStringToken <|> astStandardString

standardStringToken :: Parser String
standardStringToken =
  parsedLiteralText <$> quotedStringParts Nothing

-- | Every quoted source expression is parsed as a template. The common case
-- with no interpolation is collapsed back to the existing string literal AST.
stringExpression :: Parser Expression
stringExpression = lexeme sourceStringTemplateToken

sourceStringTemplateToken :: Parser Expression
sourceStringTemplateToken =
  stringTemplateToken expression sourceSimpleInterpolation

astStringTemplateToken :: Parser Expression
astStringTemplateToken =
  stringTemplateToken astExpression astSimpleInterpolation

data ParsedStringTemplatePart
  = ParsedStringTemplateCharacter Char
  | ParsedStringTemplateInterpolation (StringTemplatePart Expression)

stringTemplateToken
  :: Parser Expression
  -> Parser Expression
  -> Parser Expression
stringTemplateToken compoundInterpolation simpleInterpolation =
  buildStringTemplate
    <$> quotedStringParts (Just stringInterpolation)
  where
    stringInterpolation = do
      _ <- char '%'
      interpolationConstructor <-
        maybe
          StringTemplateInterpolation
          (const StringTemplateWeakInterpolation)
          <$> optional (char '!')
      ParsedStringTemplateInterpolation . interpolationConstructor
        <$> (parenthesizedInterpolation <|> simpleInterpolation)

    parenthesizedInterpolation = do
      _ <- char '('
      withInterpolationComments
        (fullSpaceConsumer
          *> compoundInterpolation
          <* fullSpaceConsumer
          <* char ')')

quotedStringParts
  :: Maybe (Parser ParsedStringTemplatePart)
  -> Parser [ParsedStringTemplatePart]
quotedStringParts interpolation =
  between (char '"') (char '"')
    (concat <$> many quotedPart)
  where
    quotedPart =
      choice
        ( maybe
            []
            (\parser -> [(: []) <$> parser])
            interpolation
          <> [ [] <$ standardStringComment
             , (: []) . ParsedStringTemplateCharacter
                <$> standardStringCharacter
             ]
        )

withInterpolationComments :: Parser value -> Parser value
withInterpolationComments parser = do
  local (\context -> context { interpolationDepth = interpolationDepth context + 1 }) parser

sourceSimpleInterpolation :: Parser Expression
sourceSimpleInterpolation = simpleInterpolationWith
  (atomicExpressionToken sourceStringTemplateToken <|> (IdentifierReference . IdentifierString <$> bareIdentifierToken))

astSimpleInterpolation :: Parser Expression
astSimpleInterpolation = simpleInterpolationWith astAtom

simpleInterpolationWith :: Parser Expression -> Parser Expression
simpleInterpolationWith atomParser = do
  expressionValue <- atomParser
  isOptional <- maybe False (const True) <$> optional (char '?')
  pure
    (if isOptional
      then OptionalType expressionValue
      else expressionValue)

buildStringTemplate :: [ParsedStringTemplatePart] -> Expression
buildStringTemplate parsedParts =
  case foldr collect ([], False) parsedParts of
    (parts, False) ->
      AsciiStringLiteral
        (concat
          [ value
          | StringTemplateLiteral value <- parts
          ])
    (parts, True) -> StringTemplate parts
  where
    collect (ParsedStringTemplateCharacter character) (parts, hasHole) =
      case parts of
        StringTemplateLiteral value : remaining ->
          (StringTemplateLiteral (character : value) : remaining, hasHole)
        _ -> (StringTemplateLiteral [character] : parts, hasHole)
    collect (ParsedStringTemplateInterpolation interpolation)
        (parts, _) =
      (interpolation : parts, True)

parsedLiteralText :: [ParsedStringTemplatePart] -> String
parsedLiteralText parts =
  [ character
  | ParsedStringTemplateCharacter character <- parts
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
      , '%' <$ char '%'
      , '?' <$ char '?'
      , '\n' <$ char 'n'
      , hexadecimalAsciiCharacter
      ])
    <|> satisfy
      (\character ->
        character /= '"'
          && character /= '\\'
          && character /= '#'
          && character /= '%'
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
lineComment = do
  depth <- interpolationDepth <$> ask
  _ <- char '#'
  void
    (manyTill anySingle
      (lookAhead
        ( void eol
          <|> if depth > 0
                then void (char ')')
                else empty
          <|> eof
        )))

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
operatorToken operator = lexeme $ try $ do
  token <- chunk (operatorSourceText operator)
  if operator `elem` [AST.MinusOperator, AST.SubtractionOperator]
    then notFollowedBy (char '>') else pure ()
  pure token

continuedOperator :: AST.Operator -> Parser Text
continuedOperator operator = operatorToken operator <* lineSpaceConsumer

semicolon :: Parser Text
semicolon = symbol ";"
