{-# LANGUAGE OverloadedStrings #-}

-- | Canonical AST notation reader, mechanically separate from ordinary source parsing.
module CanonicalParsing (parseDatraAstLocatedWithSourceName) where

import Control.Applicative (empty, optional, some, (<|>))
import Control.Monad (guard)
import Data.Bifunctor qualified as Bifunctor
import Data.List (find)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
import DatraLanguage.AST.CanonicalForm
  ( CanonicalForm (..), canonicalFormName )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.AST.Reserved.Bootstrap (reservedSymbolReplacements)
import DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (..), delimiterText )
import DatraLanguage.DependentDeclaration
  ( applyDeclarationModifier, dependentDeclaration )
import DatraLanguage.Diagnostics
  ( Located (Located), SourcePosition (SourcePosition), SourceSpan (SourceSpan) )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (DatraSourceParseFailure) )
import DatraLanguage.Identifier (isIdentifierCharacter, isPrivateIdentifier)
import StringParsing (standardStringToken, stringTemplateToken)
import Text.Megaparsec
  ( Parsec, between, choice, chunk, eof, errorBundlePretty, getOffset
  , getSourcePos, lookAhead, many, runParser, sourceColumn, sourceLine
  , satisfy, sourceName, try, unPos
  )
import Text.Megaparsec.Char (char, space1)
import Text.Megaparsec.Char.Lexer qualified as Lexer

type Parser = Parsec Void Text

parseDatraAstLocatedWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseDatraAstLocatedWithSourceName resourceName sourceText =
  Bifunctor.first (DatraSourceParseFailure . errorBundlePretty)
    (runParser (located astResource) resourceName (Text.pack sourceText))

located :: Parser Expression -> Parser (Located Expression)
located parser = do
  startOffset <- getOffset
  start <- getSourcePos
  value <- parser
  endOffset <- getOffset
  end <- getSourcePos
  pure (Located
    (SourceSpan
      (sourceName start)
      (SourcePosition (fromIntegral startOffset)
        (fromIntegral (unPos (sourceLine start)))
        (fromIntegral (unPos (sourceColumn start))))
      (SourcePosition (fromIntegral endOffset)
        (fromIntegral (unPos (sourceLine end)))
        (fromIntegral (unPos (sourceColumn end)))))
    value)

astResource :: Parser Expression
astResource = astSpaceConsumer *> astExpression <* eof

astExpression :: Parser Expression
astExpression = try astEmptyMap <|> astForm <|> astAtom

astEmptyMap :: Parser Expression
astEmptyMap = AtlasMap [] <$
  (astDelimiter OpenParenthesis *> astDelimiter CloseParenthesis)

astAtom :: Parser Expression
astAtom = astLexeme
  (Skip <$ chunk (Text.pack AST.skipSourceSymbol)
    <|> astAtomicExpressionToken
    <|> astNamedAtom)

astNamedAtom :: Parser Expression
astNamedAtom = do
  name <- bareIdentifierToken
  pure (maybe
    (IdentifierReference (SimpleIdentifierString name))
    snd
    (find ((== name) . Reserved.reservedSymbolIdentifierString . fst)
      reservedSymbolReplacements))

bareIdentifierToken :: Parser String
bareIdentifierToken = some (satisfy isIdentifierCharacter)

astString :: Parser String
astString = astLexeme
  (sourceOperatorCharacter AST.IdentifierExpressionCharacterOperator *>
    bareIdentifierToken <|> standardStringToken)

astStringTemplateToken :: Parser Expression
astStringTemplateToken = stringTemplateToken astExpression astAtom

astAtomicExpressionToken :: Parser Expression
astAtomicExpressionToken =
  choice
    [ EllipsisLiteral <$ chunk (Text.pack AST.ellipsisSymbol)
    , astStringTemplateToken
    , EllipsisNatural <$> Lexer.decimal
    ]

astForm :: Parser Expression
astForm =
  between (astDelimiter OpenParenthesis) (astDelimiter CloseParenthesis)
    (choice
      [ InModule <$> (astCanonicalForm InModuleForm *> astString) <*> astExpression
      , astImport
      , astUnaryForm FunctionForm Fun
      , astGenericIntroduction
      , astFunctionType
      , astBlock Reserved.DoWord FunctionBody
      , astSequence
      , ArgumentativeMap <$>
          (astCanonicalForm ArgumentativeMapForm *> many astExpression)
      , astWithScopes
      , astNaturalRangeExpression
      , astDependentArgument AST.AssignmentOperator (Just ())
      , astDependentArgument AST.DependentArgumentTypeOperator Nothing
      , astBlock Reserved.BeginWord Begin
      , astDeclarationModifier AST.LetOperator DeclarationLet
      , astDeclarationModifier AST.DefOperator DeclarationDef
      , astDeclarationModifier AST.ValOperator DeclarationVal
      , IdentifierReference . SimpleIdentifierString <$>
          (astCanonicalForm IdentifierReferenceForm *> astString)
      , LineBreak <$ astCanonicalForm LineBreakForm
      , UnresolvedSyntaxLiteral <$>
          (astCanonicalForm UnresolvedSyntaxForm *> astString)
      , astConditional
      , try astRegisteredBinary
      , astRegisteredUnary
      ])

astWithScopes :: Parser Expression
astWithScopes = do
  _ <- astCanonicalForm WithScopesForm
  sources <- between
    (astDelimiter OpenParenthesis)
    (astDelimiter CloseParenthesis)
    (astCanonicalForm ArgumentativeMapForm *> many astExpression)
  WithScopes sources <$> astExpression

astImport :: Parser Expression
astImport = do
  _ <- astCanonicalForm ImportForm
  paths <- between (astDelimiter OpenParenthesis) (astDelimiter CloseParenthesis) $ do
    _ <- astCanonicalForm ImportPathsForm
    many astString
  Import paths <$> astExpression

astGenericIntroduction :: Parser Expression
astGenericIntroduction = do
  _ <- astCanonicalForm GenericIntroductionForm
  polarity <- astGenericPolarity
  identifier <- astExpression
  bound <- astExpression
  GenericIntroductionExpression <$> astGenericArgument
    polarity identifier bound

astFunctionType :: Parser Expression
astFunctionType = do
  _ <- astSymbol
    (Text.pack (AST.operatorCanonicalSymbol AST.FunctionTypeOperator))
  generics <- maybe [] id <$> optional
    (try (between (astDelimiter OpenParenthesis) (astDelimiter CloseParenthesis) $ do
      _ <- astCanonicalForm GenericPrefixForm
      some astGenericBinder))
  FunctionTypeExpression generics
    <$> astExpression
    <*> astExpression

astGenericBinder :: Parser (GenericBinder Expression)
astGenericBinder = between
  (astDelimiter OpenParenthesis) (astDelimiter CloseParenthesis) $ do
  _ <- astCanonicalForm GenericBinderForm
  identity <- GenericBinderId <$> astLexeme Lexer.decimal
  polarity <- astGenericPolarity
  identifier <- astExpression
  bound <- astExpression
  argument <- astGenericArgument polarity identifier bound
  pure GenericBinder
    { genericBinderId = identity
    , genericBinderArgument = argument
    }

astGenericPolarity :: Parser GenericPolarity
astGenericPolarity = choice
  [ GenericProduct <$ astOperatorToken AST.GenericProductOperator
  , GenericSum <$ astOperatorToken AST.ExponentiationOperator
  ]

astGenericArgument
  :: GenericPolarity
  -> Expression
  -> Expression
  -> Parser (GenericArgument Expression)
astGenericArgument polarity expressionValue bound = do
  (name, optionalName) <- case expressionValue of
    IdentifierReference name -> pure (name, False)
    OptionalType (IdentifierReference name) -> pure (name, True)
    _ -> empty
  guard (not
    (optionalName && isPrivateIdentifier (simpleIdentifierStringText name)))
  pure GenericArgument
    { genericArgumentPolarity = polarity
    , genericArgumentName = name
    , genericArgumentOptional = optionalName
    , genericArgumentBound = bound
    }

astDependentArgument
  :: AST.Operator
  -> Maybe ()
  -> Parser Expression
astDependentArgument operator assignmentMarker = do
  _ <- astOperatorToken operator
  nameExpression <- astExpression
  name <- maybe empty pure
    (identifierExpressionFromExpression nameExpression)
  typeAnnotation <- astExpression
  case assignmentMarker of
    Nothing -> pure
      (constructDependentArgument name False (Just typeAnnotation) Nothing)
    Just () -> do
      givenValue <- optional astExpression
      pure (case givenValue of
        Nothing -> constructDependentArgument
          name False Nothing (Just typeAnnotation)
        Just given -> constructDependentArgument
          name False (Just typeAnnotation) (Just given))

astConditional :: Parser Expression
astConditional = do
  _ <- astReservedSymbol Reserved.IfSymbol
  condition <- astExpression
  consequent <- astExpression
  alternative <- astExpression
  pure (Conditional condition consequent alternative)

astBlock
  :: Reserved.ReservedWord
  -> ([DependentDeclaration Expression] -> Expression -> Expression)
  -> Parser Expression
astBlock blockWord construct = do
  _ <- astReservedWord blockWord
  bindings <- between (astDelimiter OpenParenthesis) (astDelimiter CloseParenthesis)
    (astCanonicalForm BindingsForm *> many astExpression)
  declarations <- traverse
    (maybe empty pure . dependentDeclaration)
    bindings
  construct declarations <$> astExpression

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

-- The shared @a to b@ / @a up@ grammar is intentionally reachable only
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

astSignedInteger :: Parser Integer
astSignedInteger =
  astLexeme
    (try (sourceOperatorCharacter AST.MinusCharacterOperator *>
      (negate <$> Lexer.decimal))
      <|> Lexer.decimal)

astRegisteredUnary :: Parser Expression
astRegisteredUnary = do
  operator <- astRegisteredOperator unaryExpressionOperators
  operand <- astExpression
  maybe empty pure (applyUnaryExpressionOperator operator operand)

astRegisteredBinary :: Parser Expression
astRegisteredBinary = do
  operator <- astRegisteredOperator binaryExpressionOperators
  left <- astExpression
  right <- astExpression
  maybe empty pure (applyBinaryExpressionOperator operator left right)

astRegisteredOperator :: [AST.Operator] -> Parser AST.Operator
astRegisteredOperator = choice . map (\operator ->
  operator <$ astOperatorToken operator)

astDeclarationModifier
  :: AST.Operator
  -> DeclarationModifier
  -> Parser Expression
astDeclarationModifier operator modifier = do
  _ <- astOperatorToken operator
  operand <- astExpression
  maybe empty pure (applyDeclarationModifier modifier operand)

astUnaryForm
  :: CanonicalForm
  -> (Expression -> Expression)
  -> Parser Expression
astUnaryForm form constructor = do
  _ <- astCanonicalForm form
  constructor <$> astExpression

astSpaceConsumer :: Parser ()
astSpaceConsumer = Lexer.space space1 empty empty

astLexeme :: Parser value -> Parser value
astLexeme = Lexer.lexeme astSpaceConsumer

astSymbol :: Text -> Parser Text
astSymbol = Lexer.symbol astSpaceConsumer

astCanonicalForm :: CanonicalForm -> Parser Text
astCanonicalForm = astSymbol . Text.pack . canonicalFormName

astReservedSymbol :: Reserved.ReservedSymbol -> Parser Text
astReservedSymbol =
  astSymbol . Text.pack . Reserved.reservedSymbolIdentifierString

astReservedWord :: Reserved.ReservedWord -> Parser Text
astReservedWord = astSymbol . Text.pack . Reserved.reservedWordText

astDelimiter :: StructuralDelimiter -> Parser Text
astDelimiter = astSymbol . Text.pack . delimiterText

astOperatorToken :: AST.Operator -> Parser Text
astOperatorToken operator = astLexeme $ try $ do
  token <- chunk (Text.pack (AST.operatorCanonicalSymbol operator))
  _ <- lookAhead space1
  pure token

sourceOperatorCharacter :: AST.SourceCharacterOperator -> Parser Char
sourceOperatorCharacter = char . AST.sourceOperatorCharacter


