{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Parsing
  ( ResourceEnvelope (..)
  , parseSourceExpression
  , expressionParser
  , parseDatraRawLocatedWithSourceName
  ) where

import Control.Applicative (empty, optional, some, (<|>))
import Control.Monad (guard, void)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixR, Postfix, Prefix)
  , makeExprParser
  )
import Data.Bifunctor qualified as Bifunctor
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
  ( SimpleIdentifierString (..)
  , GenericPolarity (GenericProduct, GenericSum)
  , GenericArgument (..)
  , Expression
      ( Addition
      , IdentifierExpression
      , AtlasIdentifierExpression
      , AtlasMap
      , ArgumentativeMap
      , AnyType
      , Skip
      , EllipsisLiteral
      , Exponentiation
      , ScopeAccess
      , MapAccess
      , MapConcatenation
      , MapExpansion
      , MapSequence
      , SyntaxBoundary
      , MapSpecification
      , Overload
      , SafeOverload
      , ReverseMapSpecification
      , ReverseOverload
      , ReverseSafeOverload
      , Multiplication
      , Subtraction
      , Plus
      , Minus
      , SuperEllipsisRange
      , SuperEllipsisRangeMinus
      , SuperEllipsisRangePlus
      , EitherType
      , OptionalType
      , MaybeThen
      , Equality
      , Inequality
      , LessThan
      , LessThanOrEqual
      , GreaterThan
      , GreaterThanOrEqual
      , Coalization
      , GenericIntroductionExpression
      , FunctionTypeExpression
      , FunctionApplication
      , IdentifierReference
      , UnresolvedSyntaxLiteral
      , SyntaxRemainder
      , Lookup
      )
  , pattern FunctionType
  , literalIdentifierName
  , constructDependentArgument
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (..)
  , closingDelimiters
  , commentCharacter
  , delimiterCharacter
  , isSymbolicSourceCharacter
  )
import DatraLanguage.Application (presentedApplication)
import DatraLanguage.Identifier
  ( isPrivateIdentifier
  , isIdentifierCharacter
  )
import DatraLanguage.Diagnostics
  ( Located (Located)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (DatraSourceParseFailure) )
import StringInterpolation.Matching (ExpressionParser (..))
import StringParsing (standardStringToken, stringTemplateToken)
import DatraTypes.FunctionType (resolveGenericFunctionTypes)
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
  , match
  , many
  , manyTill
  , notFollowedBy
  , runParser
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
  | ImplicitBlockEnvelope
  deriving (Eq, Show)

-- | Parse exactly one declaration-independent source phrase.
parseSourceExpression :: String -> Either ParseFailure Expression
parseSourceExpression source =
  resolveGenericFunctionTypes <$> Bifunctor.first
    (DatraSourceParseFailure . errorBundlePretty)
    (runParser
      (fullSpaceConsumer *> expression <* fullSpaceConsumer <* eof)
      mempty
      (Text.pack source))

expressionParser :: ExpressionParser
expressionParser = ExpressionParser
  (either (const Nothing) Just . parseSourceExpression)

parseDatraRawLocatedWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure (ResourceEnvelope, Located Expression)
parseDatraRawLocatedWithSourceName resourceName source = do
  (envelope, Located sourceSpan expressionValue) <-
    Bifunctor.first (DatraSourceParseFailure . errorBundlePretty) (runParser
      locatedRawResourceWithEnvelope resourceName (Text.pack source))
  pure (envelope, Located sourceSpan
    (resolveGenericFunctionTypes expressionValue))

locatedRawResourceWithEnvelope
  :: Parser (ResourceEnvelope, Located Expression)
locatedRawResourceWithEnvelope = do
  (sourceSpan, (envelope, expressionValue)) <-
    spanned rawResourceWithEnvelope
  pure (envelope, Located sourceSpan expressionValue)


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

rawResourceWithEnvelope :: Parser (ResourceEnvelope, Expression)
rawResourceWithEnvelope = do
  fullSpaceConsumer
  entries <- elementsUntil eof
  fullSpaceConsumer
  eof
  pure (case entries of
    [explicit@SyntaxBoundary {}] -> (ExplicitMapEnvelope, explicit)
    _ -> (ImplicitBlockEnvelope, AtlasMap entries))

sequenceExpression :: [Expression] -> Expression
sequenceExpression [] = AtlasMap []
sequenceExpression [expressionValue] = expressionValue
sequenceExpression expressions = AtlasMap expressions

sourceAtomicExpressionToken :: Parser Expression
sourceAtomicExpressionToken = choice
  [ EllipsisLiteral <$ chunk (Text.pack AST.ellipsisSymbol)
  , sourceStringTemplateToken
  ]

elementsUntil :: Parser () -> Parser [Expression]
elementsUntil boundary = do
  first <- optional (commentExpression boundary <|> expression)
  case first of
    Nothing -> pure []
    Just entry -> continue entry
  where
    continue entry = do
      more <- optional elementSeparator
      case more of
        Nothing -> pure [entry]
        Just SemicolonSeparator ->
          (entry :) <$> elementsUntil boundary
        Just (CommentSeparator sourceText) -> do
          following <- commentExpression boundary
          continue (presentedApplication sourceText entry following)
        Just (LineSeparator sourceText) -> do
          next <- optional (commentExpression boundary <|> expression)
          case next of
            Nothing -> pure [entry]
            Just following -> continue
              (presentedApplication sourceText entry following)

-- Hash is the head of the first dependent declaration in every environment.
-- Its operand is concrete source remainder, delimited by the enclosing syntax
-- parser rather than interpreted by any later expression rule.
commentExpression :: Parser () -> Parser Expression
commentExpression boundary = do
  _ <- char commentCharacter
  sourceText <- manyTill anySingle
    (lookAhead (void eol <|> boundary <|> eof))
  pure (FunctionApplication
    (UnresolvedSyntaxLiteral [commentCharacter])
    (SyntaxRemainder sourceText))

-- A newline is a separator only while parsing map elements. Newlines after
-- an infix operator are consumed by 'continuedOperator' before this parser can
-- see them.
data ElementSeparator
  = SemicolonSeparator
  | LineSeparator String
  | CommentSeparator String

elementSeparator :: Parser ElementSeparator
elementSeparator =
  SemicolonSeparator
    <$ (operatorToken AST.SequentialOperator <* lineSpaceConsumer)
    <|> (LineSeparator <$> linePresentation)
    <|> (CommentSeparator <$>
      try ((maybe "" id <$> optional horizontalPresentation)
        <* lookAhead (char commentCharacter)))

linePresentation :: Parser String
linePresentation = Text.unpack . fst <$>
  match (some (eol <* horizontalSpaceConsumer))

horizontalPresentation :: Parser String
horizontalPresentation = Text.unpack . fst <$> match hspace1

-- Reverse specification is the outermost expression layer, so either side
-- can contain dependent arguments, concatenation, and function applications.
expression :: Parser Expression
expression = expressionWith mapExpression

expressionWith :: Parser Expression -> Parser Expression
expressionWith operand = do
  target <- maybeThenExpressionWith operand
  maybeSource <-
    optional
      (continuedOperator AST.ReverseSpecificationOperator *>
        expressionWith operand)
  pure
    (case maybeSource of
      Nothing -> target
      Just source -> ReverseMapSpecification
        target
        (SyntaxBoundary source))

-- Maybe sequencing is deliberately low-precedence and right-associative so
-- its lazy branch can contain a complete function or map expression.
maybeThenExpressionWith :: Parser Expression -> Parser Expression
maybeThenExpressionWith operand =
  maybeThenExpressionFrom (arrowExpressionWith operand)

maybeThenExpressionFrom :: Parser Expression -> Parser Expression
maybeThenExpressionFrom operand = do
  optionalValue <- operand
  continuation <- optional $ do
    constructor <- MaybeThen <$ continuedOperator AST.MaybeThenOperator
    branch <- maybeThenExpressionFrom operand
    pure (constructor, branch)
  pure (case continuation of
    Nothing -> optionalValue
    Just (constructor, branch) -> constructor optionalValue branch)

arrowExpressionWith :: Parser Expression -> Parser Expression
arrowExpressionWith operand =
  eitherExpressionWith (tightArrowExpressionWith operand)

tightArrowExpressionWith :: Parser Expression -> Parser Expression
tightArrowExpressionWith = arrowExpressionWithLayer id

arrowExpressionWithLayer
  :: (Parser Expression -> Parser Expression)
  -> Parser Expression
  -> Parser Expression
arrowExpressionWithLayer expressionLayer operand = do
  rawInput <- expressionLayer operand
  let signature = arrowExpressionWithLayer expressionLayer operand
  let input = rawInput
  output <- optional
    (continuedOperator AST.FunctionTypeOperator *> signature)
  pure (maybe input (applyAfter (applyFunctionType input)) output)

-- Function type construction binds before the unresolved application
-- spine on its right. Parentheses introduce a 'SyntaxBoundary', so an applied
-- codomain can still be written explicitly when that is what is intended.
applyAfter :: (Expression -> Expression) -> Expression -> Expression
applyAfter construct value = case value of
  FunctionApplication function argument ->
    FunctionApplication (applyAfter construct function) argument
  Coalization operand -> applyAfter (construct . Coalization) operand
  _ -> construct value

-- The arrow likewise owns only the final operand of an application phrase on
-- its left. Thus @f A -> B@ is @f (A -> B)@; parentheses are required when the
-- intended domain is the applied value @f A@.
applyFunctionType :: Expression -> Expression -> Expression
applyFunctionType input output = case input of
  FunctionApplication function argument ->
    FunctionApplication function (applyFunctionType argument output)
  _ -> FunctionType input output

eitherExpressionWith :: Parser Expression -> Parser Expression
eitherExpressionWith = eitherExpressionWithOperator
  (continuedOperator AST.EitherOperator)

eitherExpressionWithOperator
  :: Parser Text
  -> Parser Expression
  -> Parser Expression
eitherExpressionWithOperator eitherOperator operand =
  makeExprParser
    operand
    [ [InfixR (EitherType <$ eitherOperator)]
    , [ InfixL (Inequality <$ continuedOperator AST.InequalityOperator)
      , InfixL (Equality <$ continuedOperator AST.EqualityOperator)
      , InfixL (LessThanOrEqual <$ continuedOperator AST.LessThanOrEqualOperator)
      , InfixL (GreaterThanOrEqual <$ continuedOperator AST.GreaterThanOrEqualOperator)
      , InfixL (LessThan <$ continuedOperator AST.LessThanOperator)
      , InfixL (GreaterThan <$ continuedOperator AST.GreaterThanOperator)
      ]
    ]

mapExpression :: Parser Expression
mapExpression =
  makeExprParser
    ( try templateConcatenation
        <|> try dependentArgumentExpressionParser
        <|> rangeExpression
    )
    mapOperatorTable

-- Strings and identifier expressions use the ordinary comma expression.
templateConcatenation :: Parser Expression
templateConcatenation = do
  first <- templateConcatenationOperand
  _ <- infixComma
  second <- templateConcatenationOperand
  value <- continue second
  pure (MapConcatenation first value)
  where
    templateConcatenationOperand =
      try dollarIdentifierExpression <|> stringExpression
    continue left = do
      remaining <- optional (try
        (infixComma *> templateConcatenationOperand >>= continue))
      pure (maybe left (MapConcatenation left) remaining)

-- A literal-expression operator introduces a direct non-bare name, while
-- parentheses retain the existing syntax boundary and therefore evaluate the
-- enclosed expression before its string-family invariant is checked.
evaluatedDependentArgumentOrExpression :: Parser Expression
evaluatedDependentArgumentOrExpression =
  try dependentArgumentExpressionParser
    <|> try atlasIdentifierExpression
    <|> dollarIdentifierExpression
    <|> parenthesizedOrReverse
  where
    parenthesizedOrReverse = do
      evaluated <- parenthesizedExpression
      maybe evaluated id <$>
        optional (try (reverseSpecificationAfter evaluated))

reverseSpecificationAfter :: Expression -> Parser Expression
reverseSpecificationAfter target = do
  _ <- continuedOperator AST.ReverseSpecificationOperator
  source <- parenthesizedExpression
  pure (MapSpecification source target)

dependentArgumentExpressionParser :: Parser Expression
dependentArgumentExpressionParser = do
  dependentName <- dependentArgumentName
  isOptional <-
    maybe False (const True)
      <$> optional (operatorToken AST.OptionalOperator)
  guard (not (isOptional && privateDependentName dependentName))
  (annotation, given) <- dependentArgumentSuffix
  pure (constructDependentArgument
    dependentName isOptional annotation given)

dependentArgumentName :: Parser Expression
dependentArgumentName = choice
  [ try atlasIdentifierExpression
  , dollarIdentifierExpression
  , parenthesizedExpression
  , IdentifierExpression . IdentifierReference . SimpleIdentifierString
      <$> bareIdentifier
  ]

privateDependentName :: Expression -> Bool
privateDependentName name = case literalIdentifierName name of
  Just identifier -> isPrivateIdentifier (simpleIdentifierStringText identifier)
  Nothing -> False

dependentArgumentSuffix
  :: Parser (Maybe Expression, Maybe Expression)
dependentArgumentSuffix = choice
  [ do
      _ <- continuedOperator AST.AssignmentOperator
      given <- assignedValueExpression
      pure (Nothing, Just given)
  , do
      _ <- continuedOperator AST.DependentArgumentTypeOperator
      annotation <- identifierValueExpression
      given <- optional
        (continuedOperator AST.AssignmentOperator *> assignedValueExpression)
      pure (Just annotation, given)
  ]

-- Identifier annotations and assigned values may use range, arithmetic, and
-- access operators directly. Concatenation and specification are deliberately
-- excluded at this level so @,@ and @~>@ terminate the identifier operand;
-- explicit parentheses remain available when either belongs to the
-- identifier's own value.
identifierValueExpression :: Parser Expression
identifierValueExpression = do
  signature <- do
    rawInput <- makeExprParser rangeExpression identifierValueOperatorTable
    let input = rawInput
    output <- optional
      (continuedOperator AST.FunctionTypeOperator *> tightArrowExpressionWith
        (makeExprParser rangeExpression identifierValueOperatorTable))
    pure (maybe input (FunctionType input) output)
  pure signature

-- The value following @:=@ additionally admits an unparenthesized federation.
-- Type annotations keep the narrower grammar so @name : T | U@ continues to
-- mean a federation whose first member is a named type.
assignedValueExpression :: Parser Expression
assignedValueExpression =
  assignmentEitherExpressionWith
    (tightArrowExpressionWith
      (makeExprParser rangeExpression identifierValueOperatorTable))

-- Assignment has lower precedence than federation, except that a following
-- identifier declaration starts the next federation member. Thus
-- @Alias := Nat | Str@ assigns the complete federation while
-- @False := 0 | True := 1@ remains a federation of two declarations.
assignmentEitherExpressionWith :: Parser Expression -> Parser Expression
assignmentEitherExpressionWith = eitherExpressionWithOperator
  (continuedOperator AST.EitherOperator)

-- An arithmetic operator followed by another dependent argument belongs to
-- the surrounding expression. Otherwise it remains part of this identifier's
-- annotation or assigned value, preserving forms such as @x : 2 + 3@.
-- Ranges have a small dedicated grammar so exactly one unparenthesized '..'
-- is permitted at this precedence level. Each explicit endpoint is a complete
-- arithmetic expression; nested ranges therefore require parentheses.
rangeExpression :: Parser Expression
rangeExpression =
  try prefixRange
    <|> try explicitRange
    <|> makeExprParser term arithmeticOperatorTable

prefixRange :: Parser Expression
prefixRange = do
  _ <- continuedOperator AST.RangeOperator
  -- Preserve the implicit origin in the same unresolved form as a written
  -- numeral.  The NaturalLiteral declaration, not this parser, converts it.
  SuperEllipsisRange
    (IdentifierReference (SimpleIdentifierString "0"))
    <$> rangeEndpoint

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
        pure (SuperEllipsisRangePlus lowerBound)
    ]

-- A bare Ellipsis value cannot be a range endpoint. Parentheses deliberately
-- return to the complete expression grammar, making forms such as '(...)..'
-- explicit while keeping grouping out of the AST.
rangeEndpoint :: Parser Expression
rangeEndpoint = makeExprParser rangeEndpointTerm arithmeticOperatorTable

term :: Parser Expression
term = do
  function <- accessedTerm termAtom
  arguments <- applicationArguments
  pure (foldl applyPresentedArgument function arguments)
  where
    applicationArguments = do
      next <- optional (try $ do
        separator <- maybe "" id <$> optional horizontalPresentation
        argument <- applicationArgument
        pure (separator, argument))
      case next of
        Nothing -> pure []
        Just argument -> (argument :) <$> applicationArguments
    applyPresentedArgument left (separator, right) =
      presentedApplication separator left right
    -- A newline remains a block boundary; operator and syntax words cannot be
    -- arguments. Horizontal presentation is retained by 'applicationArguments'.
    applicationArgument = accessedTerm (choice
      [ evaluatedDependentArgumentOrExpression
      , try dependentArgumentExpressionParser
      , argumentativeMap
      , lookupExpression
      , trailingApplicationSkip
      , prefixedApplicationArgument
      , sourceAtomicExpressionToken
      , try (notFollowedBy (char commentCharacter) *> symbolicSyntaxLiteral)
      , identifierReference
      ])

-- At an expression boundary, a bare @*@ cannot be multiplication because it
-- has no right operand. Keep it in the unresolved application spine so declared
-- syntax such as @value of *@ can capture it as an expression hole. Ambiguous
-- arithmetic positions continue to require the grouped skip spelling @(*)@.
trailingApplicationSkip :: Parser Expression
trailingApplicationSkip = try $ do
  _ <- operatorToken AST.MultiplicationOperator
  lookAhead (expressionEnd <|> void eol)
  pure Skip

-- Prefix-only operators remain valid at the start of an application operand.
-- Reading them here preserves that structural boundary for later declarative
-- syntax matching; unlike @+@ and @-@, coalization has no competing infix
-- interpretation at this position.
prefixedApplicationArgument :: Parser Expression
prefixedApplicationArgument =
  Coalization
    <$> (operatorToken AST.CoalizationOperator *> term)

termAtom :: Parser Expression
termAtom =
  choice
    [ bareSkip
    , genericIntroduction
    , evaluatedDependentArgumentOrExpression
    , lookupExpression
    , argumentativeMap
    , sourceAtomicExpressionToken
    , symbolicSyntaxLiteral
    , identifierReference
    ]

genericIntroduction :: Parser Expression
genericIntroduction = do
  polarity <- choice
    [ GenericProduct <$ operatorToken AST.GenericProductOperator
    , GenericSum <$ operatorToken AST.ExponentiationOperator
    ]
  name <- identifierName
  optionalName <- maybe False (const True)
    <$> optional (operatorToken AST.OptionalOperator)
  guard (not (optionalName && isPrivateIdentifier name))
  bound <- maybe
    AnyType
    id
    <$> optional
      (try
        (continuedOperator AST.GenericBoundOperator *>
          identifierValueExpression))
  pure (GenericIntroductionExpression
    GenericArgument
      { genericArgumentPolarity = polarity
      , genericArgumentName = SimpleIdentifierString name
      , genericArgumentOptional = optionalName
      , genericArgumentBound = bound
      })

-- Declarative syntax is discovered only after the complete resource has been
-- read, so the source parser must retain symbolic words that are not core
-- operators when they follow an already-parsed operand. Maximal-munch keeps
-- an adjacent spelling such as @2++@ as the application phrase @2 ++@; the
-- later syntax pass alone decides whether a visible postfix/infix template
-- gives that phrase meaning. Exact core tokens remain owned by their ordinary
-- grammar paths, and unknown prefix symbols remain parse errors.
--
-- A deeper parser cleanup should move unresolved symbolic syntax beneath the
-- ordinary expression grammar. Then a successful core parse would naturally
-- win before an opaque symbolic literal, and this fallback would no longer
-- need to reserve compact core expressions explicitly.
symbolicSyntaxLiteral :: Parser Expression
symbolicSyntaxLiteral = try $ do
  literal <- some (satisfy isSymbolicSourceCharacter)
  guard (all
    ((/= Just literal) . AST.operatorSourceSymbol)
    [minBound .. maxBound])
  pure (UnresolvedSyntaxLiteral literal)

-- The skip atom and multiplication share @*@. A bare skip can participate in
-- every unambiguous expression position, but multiplication requires explicit
-- grouping on each skip side: @(*) * 7@ and @7 * (*)@.
bareSkip :: Parser Expression
bareSkip = Skip <$ operatorToken AST.MultiplicationOperator

identifierReference :: Parser Expression
identifierReference = try $ do
  first <- bareIdentifierToken
  pure (IdentifierReference (SimpleIdentifierString first))

-- Argumentative maps use the same expression operators and sequence separators as
-- parenthesized maps: comma concatenates within one expression, while a
-- semicolon or newline starts the next argumentative-map member.
argumentativeMap :: Parser Expression
argumentativeMap = do
  members <- between (sourceDelimiter OpenBrace <* lineSpaceConsumer)
    (lineSpaceConsumer *> sourceDelimiter CloseBrace)
    (elementsUntil (void (lookAhead (sourceDelimiter CloseBrace))))
  pure (ArgumentativeMap members)

rangeEndpointTerm :: Parser Expression
rangeEndpointTerm = accessedTerm rangeEndpointAtom

rangeEndpointAtom :: Parser Expression
rangeEndpointAtom =
  choice
    [ parenthesizedExpression
    , atlasIdentifierExpression
    , dollarIdentifierExpression
    , stringExpression
    , identifierReference
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
        _ <- operatorToken AST.ScopeAccessOperator
        body <- scopeAccessBody
        pure (\value -> ScopeAccess value body)
    , OptionalType <$ optionalTypeSuffix
    ])
  pure (foldl (\value select -> select value) source selections)

scopeAccessBody :: Parser Expression
scopeAccessBody =
  parenthesizedExpression
    <|> (IdentifierReference <$> namedAccessName)

optionalTypeSuffix :: Parser Text
optionalTypeSuffix = operatorToken AST.OptionalOperator

-- Lookup is a genuine tight prefix expression. Its operand is evaluated; in
-- particular, an identifier contributes its string value rather than its
-- source spelling. Postfix access is parsed by the enclosing 'accessedTerm'
-- and therefore applies to the lookup result.
lookupExpression :: Parser Expression
lookupExpression = do
  _ <- operatorToken AST.LookupOperator
  Lookup <$> lookupOperand
  where
    lookupOperand = choice
      [ lookupExpression
      , argumentativeMap
      , atlasIdentifierExpression
      , dollarIdentifierExpression
      , parenthesizedExpression
      , sourceAtomicExpressionToken
      , identifierReference
      ]

namedAccessName :: Parser SimpleIdentifierString
namedAccessName =
  SimpleIdentifierString <$> (bareIdentifierToken <|> standardStringToken)

bracketedInsertion :: Parser Expression
bracketedInsertion =
  between
    (sourceDelimiter OpenBracket <* lineSpaceConsumer)
    (lineSpaceConsumer *> sourceDelimiter CloseBracket)
    (do
      selections <- elementsUntil
        (void (lookAhead (sourceDelimiter CloseBracket)))
      guard (not (null selections))
      pure (sequenceExpression selections))

parenthesizedExpression :: Parser Expression
parenthesizedExpression =
  between
    (sourceDelimiter OpenParenthesis <* lineSpaceConsumer)
    (lineSpaceConsumer *> sourceDelimiter CloseParenthesis)
    (SyntaxBoundary . parenthesizedSequenceExpression <$>
      elementsUntil (void (lookAhead (sourceDelimiter CloseParenthesis))))

-- Scalar identifier conversion accepts literal names and parenthesized string
-- expressions. Atlas templates use the distinct @$!@ operator below.
dollarIdentifierExpression :: Parser Expression
dollarIdentifierExpression = try $ do
  _ <- sourceOperatorToken AST.IdentifierExpressionOperator
  IdentifierExpression <$> choice
    [ IdentifierReference . SimpleIdentifierString <$> bareIdentifierToken
    , sourceStringTemplateToken
    , try $ do
        body <- parenthesizedExpression
        guard (not (isAtlasIdentifierOperand body))
        pure body
    ]

-- Atlas identifier conversion is intentionally syntax-directed: parentheses
-- establish an Atlas literal, including empty and singleton literals. The
-- dedicated AST node preserves that choice even when a singleton's body has
-- no sequence node of its own.
atlasIdentifierExpression :: Parser Expression
atlasIdentifierExpression = try $ do
  _ <- sourceOperatorToken AST.AtlasIdentifierExpressionOperator
  body <- parenthesizedExpression
  pure (AtlasIdentifierExpression body)

isAtlasIdentifierOperand :: Expression -> Bool
isAtlasIdentifierOperand expressionValue = case expressionValue of
  SyntaxBoundary body -> isAtlasIdentifierOperand body
  AtlasMap {} -> True
  MapSequence {} -> True
  MapExpansion {} -> True
  _ -> False

-- An ungrouped arrow in the final member owns the complete semicolon domain.
-- Explicit parentheses around that final function retain it as a sequence
-- member because they introduce a 'SyntaxBoundary'.
parenthesizedSequenceExpression :: [Expression] -> Expression
parenthesizedSequenceExpression expressions =
  case reverse expressions of
    final : reversedPrefix
      | not (null reversedPrefix)
      , Just lifted <- prependDomain (reverse reversedPrefix) final -> lifted
    _ -> sequenceExpression expressions
  where
    prependDomain prefix expressionValue =
      case expressionValue of
        FunctionTypeExpression generics domain codomain ->
          Just (FunctionTypeExpression generics
            (sequenceExpression (prefix <> [domain])) codomain)
        MapSpecification implementation signature ->
          MapSpecification implementation <$> prependDomain prefix signature
        _ -> Nothing

-- Arithmetic follows Haskell and binds more tightly than range construction.
arithmeticOperatorTable :: [[Operator Parser Expression]]
arithmeticOperatorTable =
  [ [InfixR (Exponentiation <$ continuedOperator AST.ExponentiationOperator)]
  , [ Prefix (constructor <$ operatorToken operator)
    | (operator, constructor) <- arithmeticPrefixOperators
    ]
  , [InfixL (Multiplication <$ continuedOperator AST.MultiplicationOperator)]
  , [ InfixL (Addition <$ continuedOperator AST.AdditionOperator)
    , InfixL (Subtraction <$ continuedOperator AST.SubtractionOperator)
    ]
  ]

arithmeticPrefixOperators :: [(AST.Operator, Expression -> Expression)]
arithmeticPrefixOperators =
  [ (AST.AdditionOperator, Plus)
  , (AST.MinusOperator, Minus)
  , (AST.CoalizationOperator, Coalization)
  ]

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
       , [Postfix
          ((\value -> MapConcatenation value (AtlasMap [])) <$ trailingComma)]
       , mapAccessAndSpecificationOperators
       ]

identifierValueOperatorTable :: [[Operator Parser Expression]]
identifierValueOperatorTable =
  [[InfixL (MapAccess <$ continuedOperator AST.AccessOperator)]]

mapAccessAndSpecificationOperators :: [Operator Parser Expression]
mapAccessAndSpecificationOperators =
  [ InfixL (MapAccess <$ continuedOperator AST.AccessOperator)
  , InfixL (SafeOverload <$ continuedOperator AST.SafeOverloadOperator)
  , InfixL
      (ReverseSafeOverload
        <$ continuedOperator AST.ReverseSafeOverloadOperator)
  , InfixL (Overload <$ continuedOperator AST.OverloadOperator)
  , InfixL
      (ReverseOverload <$ continuedOperator AST.ReverseOverloadOperator)
  , InfixL
      (MapSpecification <$ continuedOperator AST.SpecificationOperator)
  ]

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
  choice
    ( map (void . sourceDelimiter) closingDelimiters
        <> [void (sourceOperatorToken AST.SequentialOperator), eof]
    )

bareIdentifier :: Parser String
bareIdentifier = bareIdentifierToken

identifierName :: Parser String
identifierName = standardString <|> bareIdentifier

bareIdentifierToken :: Parser String
bareIdentifierToken = do
  first <- satisfy isIdentifierCharacter
  rest <- many (satisfy isIdentifierCharacter)
  pure (first : rest)

-- | The standard quoted spelling. It is multiline by default and retains all
-- non-comment contents exactly. A hash begins a line comment, while newline,
-- quote, backslash, and a literal hash have named escaped spellings. Any byte
-- can also be written using one or two hexadecimal digits.
standardString :: Parser String
standardString = standardStringToken


-- | Every quoted source expression is parsed as a template. The common case
-- with no interpolation is collapsed back to the existing string literal AST.
stringExpression :: Parser Expression
stringExpression = sourceStringTemplateToken

sourceStringTemplateToken :: Parser Expression
sourceStringTemplateToken =
  stringTemplateToken sourceInterpolationExpression sourceSimpleInterpolation

sourceInterpolationExpression :: Parser Expression
sourceInterpolationExpression = parenthesizedSequenceExpression <$>
  elementsUntil (void (lookAhead (sourceDelimiter CloseParenthesis)))

sourceSimpleInterpolation :: Parser Expression
sourceSimpleInterpolation =
  dollarIdentifierExpression
      <|> sourceAtomicExpressionToken
      <|> (IdentifierReference . SimpleIdentifierString <$> bareIdentifierToken)

horizontalSpaceConsumer :: Parser ()
horizontalSpaceConsumer = Lexer.space hspace1 empty empty

fullSpaceConsumer :: Parser ()
fullSpaceConsumer = Lexer.space space1 empty empty

lineSpaceConsumer :: Parser ()
lineSpaceConsumer = horizontalSpaceConsumer *> void (many lineBreak)

lineBreak :: Parser ()
lineBreak = void (eol <* horizontalSpaceConsumer)

operatorToken :: AST.Operator -> Parser Text
operatorToken operator = try
  (horizontalSpaceConsumer *> sourceOperatorToken operator
    <* horizontalSpaceConsumer)

sourceOperatorToken :: AST.Operator -> Parser Text
sourceOperatorToken operator = try $ do
  source <- maybe empty pure (AST.operatorSourceSymbol operator)
  if all isSymbolicSourceCharacter source
    then do
      run <- some (satisfy isSymbolicSourceCharacter)
      guard (run == source)
      pure (Text.pack run)
    else do
      token <- chunk (Text.pack source)
      notFollowedBy (satisfy isIdentifierCharacter)
      pure token

sourceDelimiter :: StructuralDelimiter -> Parser Char
sourceDelimiter = char . delimiterCharacter

continuedOperator :: AST.Operator -> Parser Text
continuedOperator operator = try
  (lineSpaceConsumer *> sourceOperatorToken operator <* lineSpaceConsumer)
