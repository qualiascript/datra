{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}

module Parsing
  ( ResourceEnvelope (..)
  , FunctionTypeIdentifier (..)
  , PreparedFunctionDomainKind (..)
  , PreparedFunctionDomainMember (..)
  , PreparedFunctionDomain (..)
  , functionTypeIdentifiers
  , prepareFunctionDomain
  , prepareFunctionDomainExpression
  , prepareGenericExpression
  , forwardGenericBoundReference
  , parseDatra
  , sourceImports
  , sourceImportInvocations
  , parseDatraRawLocatedWithSourceName
  , parseDatraAst
  , parseDatraAstLocatedWithSourceName
  ) where

import Control.Applicative (empty, optional, some, (<|>))
import Control.Monad (guard, void)
import Control.Monad.Trans.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import Control.Monad.Combinators.Expr
  ( Operator (InfixL, InfixR, Postfix, Prefix)
  , makeExprParser
  )
import Data.Bifunctor qualified as Bifunctor
import Data.List (find, isPrefixOf)
import Data.Char (chr, digitToInt, isHexDigit)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Void (Void)
import DatraLanguage.AST
  ( IdentifierString (IdentifierString)
  , GenericPolarity (GenericProduct, GenericSum)
  , GenericIdentifier (..)
  , GenericBinderId (..)
  , GenericReferenceRole
      ( GenericDeclarationReference
      , GenericUseReference
      )
  , GenericIntroduction (..)
  , GenericBinder (..)
  , GenericReference (..)
  , Expression
      ( Addition
      , AsciiStringLiteral
      , StringTemplate
      , AtlasMap
      , ArgumentMap
      , Skip
      , EllipsisLiteral
      , EllipsisNatural
      , Exponentiation
      , NamedAccess
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
      , IdentifierOperation
      , IdentifierTemplateOperation
      , Multiplication
      , Subtraction
      , Plus
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
      , ListUncons
      , MaybeThen
      , Conditional
      , Subfederation
      , Equality
      , Inequality
      , LessThan
      , LessThanOrEqual
      , GreaterThan
      , GreaterThanOrEqual
      , BooleanAnd
      , BooleanOr
      , BooleanNot
      , Coalization
      , Assert
      , Begin
      , Program
      , SyntaxType
      , Fun
      , GenericIntroductionExpression
      , GenericReferenceExpression
      , InModule
      , Import
      , FunctionTypeExpression
      , FunctionBody
      , FunctionApplication
      , External
      , Let
      , IdentifierReference
      )
  , pattern FunctionType
  , StringTemplatePart
      ( StringTemplateInterpolation
      , StringTemplateLiteral
      )
  , contextualAccess
  , expressionChildren
  , mapExpressionChildren
  , traverseExpressionChildren
  )
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.AST.Reserved.Bootstrap
  ( reservedSymbolReplacements )
import DatraLanguage.Identifier
  ( IdentifierSpelling (..)
  , identifierSpellingValue
  , public
  , isAsciiCharacter
  , isIdentifierCharacter
  , isLeadingIdentifierCharacter
  )
import DatraLanguage.SyntaxTemplate
  ( isSymbolicSyntaxCharacter )
import DatraLanguage.Diagnostics
  ( Located (Located, locatedValue)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (ParseFailure) )
import IdentifierValueType
  ( isIdentifierValue
  , isIdentifierValueCharacter
  )
import Numeric.Natural (Natural)
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
  { interpolationDepth :: Int }

type Parser = ReaderT ParserContext (Parsec Void Text)

data ResourceEnvelope
  = ExplicitMapEnvelope
  | ImplicitBlockEnvelope
  deriving (Eq, Show)

-- | One identifier introduced into a completed function-type domain or
-- codomain scope. Simple identifiers can be compared lexically; dependent
-- identifiers retain their expression for the semantic all-fibre proof.
data FunctionTypeIdentifier
  = SimpleFunctionTypeIdentifier IdentifierString
  | DependentFunctionTypeIdentifier Expression
  deriving (Eq, Show)

-- | Container behavior retained while generic binders become real leading
-- domain members. Both parenthesized Atlas maps and semicolon map sequences
-- use the ordered path; argument maps retain their name-matching boundary.
data PreparedFunctionDomainKind
  = PreparedOrderedFunctionDomain
  | PreparedArgumentFunctionDomain
  | PreparedScalarFunctionDomain
  deriving (Eq, Show)

data PreparedFunctionDomainMember
  = PreparedGenericFunctionDomainMember (GenericBinder Expression)
  | PreparedOrdinaryFunctionDomainMember Expression
  deriving (Eq, Show)

data PreparedFunctionDomain = PreparedFunctionDomain
  { preparedFunctionDomainKind :: PreparedFunctionDomainKind
  , preparedFunctionDomainMembers :: [PreparedFunctionDomainMember]
  }
  deriving (Eq, Show)

-- | Parse an in-memory Datra resource without associating it with a real
-- filesystem path. This is the entry point used by tests and other callers
-- that already have the source contents.
parseDatra :: String -> Either ParseFailure Expression
parseDatra = parseDatraWithSourceName "<input>"

-- | Outer parentheses select expression mode; every other resource is an
-- implicit block whose exported result is introduced explicitly by @yield@.
parseDatraWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure Expression
parseDatraWithSourceName sourceName source =
  unwrap <$> parseDatraRawLocatedWithSourceName sourceName source
  where
    unwrap (_, Located _ (SyntaxBoundary value)) = value
    unwrap (_, Located _ value) = value

-- | Read source into the neutral AST used by declarative syntax matching.
-- No declared template is consulted here. An implicit resource temporarily
-- stores all of its surface entries as program bindings; the post-AST pass
-- resolves its ordinary @yield@ application after syntax scopes are known.
parseDatraRawLocatedWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure (ResourceEnvelope, Located Expression)
parseDatraRawLocatedWithSourceName resourceName source = do
  (envelope, Located sourceSpan expressionValue) <-
    Bifunctor.first (ParseFailure . errorBundlePretty) (runParser
      (runReaderT locatedRawResourceWithEnvelope
        (ParserContext 0))
      resourceName (Text.pack source))
  pure (envelope, Located sourceSpan
    (resolveGenericFunctionTypes expressionValue))

type GenericScope = [(String, GenericBinderId)]
type GenericResolution = State Natural

-- Generic declarations are collected after the neutral expression parser has
-- established arrow ownership. This gives every binder a globally unique AST
-- identity while keeping nested function domains independent.
resolveGenericFunctionTypes :: Expression -> Expression
resolveGenericFunctionTypes expressionValue =
  evalState (resolveGenericExpression [] expressionValue) 0

resolveGenericExpression
  :: GenericScope
  -> Expression
  -> GenericResolution Expression
resolveGenericExpression enclosing expressionValue =
  case expressionValue of
    IdentifierOperation name annotation (Just given)
      | given == annotation -> do
          resolved <- resolveGenericExpression enclosing annotation
          pure (IdentifierOperation name resolved (Just resolved))
    IdentifierTemplateOperation parts annotation (Just given)
      | given == annotation -> do
          resolved <- resolveGenericExpression enclosing annotation
          pure (IdentifierTemplateOperation parts resolved (Just resolved))
    FunctionTypeExpression [] domain codomain ->
      resolveNewGenericFunctionType enclosing domain codomain
    FunctionTypeExpression generics domain codomain -> do
      let localScope =
            [ (genericIdentifierText (genericBinderIdentifier binder)
              , genericBinderId binder)
            | binder <- generics
            ]
          visibleScope = localScope <> enclosing
      resolvedGenerics <- traverse
        (\binder -> do
          bound <- resolveGenericExpression enclosing
            (genericBinderBound binder)
          pure binder { genericBinderBound = bound })
        generics
      resolvedDomain <- resolveGenericExpression visibleScope domain
      resolvedCodomain <- resolveGenericExpression visibleScope codomain
      pure (FunctionTypeExpression
        resolvedGenerics resolvedDomain resolvedCodomain)
    GenericIntroductionExpression introduction -> do
      bound <- resolveGenericExpression enclosing
        (genericIntroductionBound introduction)
      pure (GenericIntroductionExpression
        introduction { genericIntroductionBound = bound })
    IdentifierReference (IdentifierString name) ->
      pure (case lookup name enclosing of
        Nothing -> expressionValue
        Just binderIdentity ->
          GenericReferenceExpression
            (GenericReference binderIdentity GenericUseReference))
    _ -> traverseExpressionChildren
      (resolveGenericExpression enclosing)
      expressionValue

resolveNewGenericFunctionType
  :: GenericScope
  -> Expression
  -> Expression
  -> GenericResolution Expression
resolveNewGenericFunctionType enclosing domain codomain = do
  let introductions = collectOwnedGenericIntroductions domain
  identities <- traverse (const freshGenericBinderId) introductions
  let declarations = zip introductions identities
      localScope =
        [ (genericIdentifierText (genericIntroductionIdentifier introduction)
          , identity)
        | (introduction, identity) <- declarations
        ]
      visibleScope = localScope <> enclosing
  binders <- resolveGenericBinders enclosing [] declarations
  resolvedDomain <- resolveOwnedGenericDomain
    visibleScope declarations domain
  resolvedCodomain <- resolveGenericExpression visibleScope codomain
  pure (FunctionTypeExpression binders resolvedDomain resolvedCodomain)

resolveGenericBinders
  :: GenericScope
  -> GenericScope
  -> [(GenericIntroduction Expression, GenericBinderId)]
  -> GenericResolution [GenericBinder Expression]
resolveGenericBinders _ _ [] = pure []
resolveGenericBinders enclosing earlier
    ((introduction, identity) : remaining) = do
  bound <- resolveGenericExpression
    (earlier <> enclosing)
    (genericIntroductionBound introduction)
  let identifier = genericIntroductionIdentifier introduction
      binder = GenericBinder
        { genericBinderId = identity
        , genericBinderPolarity = genericIntroductionPolarity introduction
        , genericBinderIdentifier = identifier
        , genericBinderBound = bound
        , genericBinderSource = genericIntroductionSource introduction
        }
      current = (genericIdentifierText identifier, identity)
  later <- resolveGenericBinders enclosing (current : earlier) remaining
  pure (binder : later)

resolveOwnedGenericDomain
  :: GenericScope
  -> [(GenericIntroduction Expression, GenericBinderId)]
  -> Expression
  -> GenericResolution Expression
resolveOwnedGenericDomain visible declarations expressionValue =
  case expressionValue of
    FunctionTypeExpression {} ->
      resolveGenericExpression visible expressionValue
    GenericIntroductionExpression introduction ->
      case lookup introduction declarations of
        Nothing -> resolveGenericExpression visible expressionValue
        Just binderIdentity ->
          pure (GenericReferenceExpression
            (GenericReference binderIdentity GenericDeclarationReference))
    IdentifierReference (IdentifierString name) ->
      pure (case lookup name visible of
        Nothing -> expressionValue
        Just binderIdentity ->
          GenericReferenceExpression
            (GenericReference binderIdentity GenericUseReference))
    _ -> traverseExpressionChildren
      (resolveOwnedGenericDomain visible declarations)
      expressionValue

collectOwnedGenericIntroductions
  :: Expression
  -> [GenericIntroduction Expression]
collectOwnedGenericIntroductions expressionValue =
  case expressionValue of
    FunctionTypeExpression {} -> []
    GenericIntroductionExpression introduction -> [introduction]
    _ -> concatMap collectOwnedGenericIntroductions
      (expressionChildren expressionValue)

freshGenericBinderId :: GenericResolution GenericBinderId
freshGenericBinderId = do
  next <- get
  put (next + 1)
  pure (GenericBinderId next)

genericIdentifierText :: GenericIdentifier -> String
genericIdentifierText
    (GenericIdentifier (IdentifierString name) _) = name

-- Identifier declarations buried in a domain combinator still contribute to
-- that function type's completed scope. An identifier declaration owns its
-- annotation, so names nested inside that annotation are not members of the
-- surrounding scope. Nested function types likewise establish a fresh
-- ownership boundary.
functionTypeIdentifiers :: Expression -> [FunctionTypeIdentifier]
functionTypeIdentifiers expressionValue =
  case expressionValue of
    FunctionTypeExpression {} -> []
    IdentifierOperation name _ _ ->
      [SimpleFunctionTypeIdentifier name]
    dependent@IdentifierTemplateOperation {} ->
      [DependentFunctionTypeIdentifier dependent]
    SyntaxBoundary value -> functionTypeIdentifiers value
    OptionalType value -> functionTypeIdentifiers value
    EitherType left right -> both left right
    AtlasMap entries -> entriesOf entries
    ArgumentMap entries -> entriesOf entries
    MapSequence entries -> entriesOf entries
    MapConcatenation left right -> both left right
    MapSpecification _ target -> functionTypeIdentifiers target
    ReverseMapSpecification target _ -> functionTypeIdentifiers target
    Overload defaults supplied -> both defaults supplied
    ReverseOverload supplied defaults -> both defaults supplied
    SafeOverload defaults supplied -> both defaults supplied
    ReverseSafeOverload supplied defaults -> both defaults supplied
    _ -> []
  where
    entriesOf = concatMap functionTypeIdentifiers
    both left right =
      functionTypeIdentifiers left <> functionTypeIdentifiers right

-- | Materialize the domain order consumed by generic-aware matching. The
-- declaration marker remains at its written location as an ordinary binder
-- reference; the telescope entries themselves occupy the leading positions.
prepareFunctionDomain
  :: [GenericBinder Expression]
  -> Expression
  -> PreparedFunctionDomain
prepareFunctionDomain generics domain =
  PreparedFunctionDomain kind
    (map PreparedGenericFunctionDomainMember generics
      <> map PreparedOrdinaryFunctionDomainMember suffix)
  where
    (kind, suffix) = layout domain
    layout expressionValue =
      case expressionValue of
        SyntaxBoundary value -> layout value
        AtlasMap entries -> (PreparedOrderedFunctionDomain, entries)
        MapSequence entries -> (PreparedOrderedFunctionDomain, entries)
        ArgumentMap entries -> (PreparedArgumentFunctionDomain, entries)
        GenericReferenceExpression reference
          | genericReferenceRole reference == GenericDeclarationReference
          , any ((== genericReferenceBinderId reference) . genericBinderId)
              generics ->
              (PreparedScalarFunctionDomain, [])
        _ -> (PreparedScalarFunctionDomain, [expressionValue])

-- | Materialize the identity-based generic telescope as ordinary named prefix
-- slots. The owning telescope retains polarity and identity; the prepared
-- domain needs only the existing identifier-slot representation.
prepareFunctionDomainExpression
  :: [GenericBinder Expression]
  -> Expression
  -> Expression
prepareFunctionDomainExpression generics domain =
  case prepareFunctionDomain generics domain of
    PreparedFunctionDomain kind members ->
      container kind (map lowerMember members)
  where
    container PreparedArgumentFunctionDomain = ArgumentMap
    container PreparedOrderedFunctionDomain = AtlasMap
    container PreparedScalarFunctionDomain = AtlasMap
    lowerMember member =
      case member of
        PreparedGenericFunctionDomainMember binder ->
          let GenericIdentifier name optionalName =
                genericBinderIdentifier binder
              bound = prepareGenericExpression generics
                (genericBinderBound binder)
              declaration = IdentifierOperation name bound Nothing
          in if optionalName
              then OptionalType declaration
              else declaration
        PreparedOrdinaryFunctionDomainMember expressionValue ->
          prepareGenericExpression generics expressionValue

-- | Convert references owned by the supplied telescope back to lexical
-- references for the existing dependent-map evaluator. References belonging
-- to another telescope remain identity based.
prepareGenericExpression
  :: [GenericBinder Expression]
  -> Expression
  -> Expression
prepareGenericExpression generics = lower
  where
    lower expressionValue =
      case expressionValue of
        GenericReferenceExpression reference ->
          case binderName (genericReferenceBinderId reference) generics of
            Just name -> IdentifierReference name
            Nothing -> expressionValue
        _ -> mapExpressionChildren lower expressionValue
    binderName _ [] = Nothing
    binderName identity (binder : remaining)
      | genericBinderId binder == identity =
          Just (genericIdentifierName (genericBinderIdentifier binder))
      | otherwise = binderName identity remaining

-- | Find the first self or forward reference in an ordered generic telescope.
-- Earlier binders have already become identity-based references; a remaining
-- lexical occurrence of the current or a later local name is therefore an
-- invalid forward dependency rather than an ambient lookup.
forwardGenericBoundReference
  :: [GenericBinder Expression]
  -> Maybe (IdentifierString, IdentifierString)
forwardGenericBoundReference = go
  where
    go [] = Nothing
    go remaining@(binder : later) =
      case firstMatchingReference unavailable
          (genericBinderBound binder) of
        Just referenced -> Just (owner, referenced)
        Nothing -> go later
      where
        owner = genericIdentifierName (genericBinderIdentifier binder)
        unavailable = map
          (genericIdentifierName . genericBinderIdentifier)
          remaining
    firstMatchingReference unavailable expressionValue =
      case expressionValue of
        IdentifierReference name
          | name `elem` unavailable -> Just name
        _ -> firstFrom
          (map (firstMatchingReference unavailable)
            (expressionChildren expressionValue))
    firstFrom [] = Nothing
    firstFrom (result : remaining) =
      case result of
        Just value -> Just value
        Nothing -> firstFrom remaining

-- | Parse the canonical symbolic S-expression emitted by 'renderExpression'.
parseDatraAst :: String -> Either ParseFailure Expression
parseDatraAst = parseDatraAstWithSourceName "<ast-input>"

parseDatraAstWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure Expression
parseDatraAstWithSourceName sourceName source =
  locatedValue <$> parseDatraAstLocatedWithSourceName sourceName source

parseDatraAstLocatedWithSourceName
  :: FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseDatraAstLocatedWithSourceName resourceName source =
  Bifunctor.first (ParseFailure . errorBundlePretty)
    (runDatraParser locatedAstResource resourceName (Text.pack source))

runDatraParser
  :: Parser value
  -> FilePath
  -> Text
  -> Either (ParseErrorBundle Text Void) value
runDatraParser parser resourceName source =
  runParser (runReaderT parser
    (ParserContext 0))
    resourceName source

locatedRawResourceWithEnvelope
  :: Parser (ResourceEnvelope, Located Expression)
locatedRawResourceWithEnvelope = do
  (sourceSpan, (envelope, expressionValue)) <-
    spanned rawResourceWithEnvelope
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
astAtom = astLexeme
  (Skip <$ chunk (Text.pack AST.skipSourceSymbol)
    <|> atomicExpressionToken astStringTemplateToken
    <|> astNamedAtom)

astNamedAtom :: Parser Expression
astNamedAtom = do
  name <- bareIdentifierToken
  pure (maybe
    (IdentifierReference (IdentifierString name))
    snd
    (find ((== name) . Reserved.reservedSymbolIdentifierString . fst)
      reservedSymbolReplacements))

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
      , astUnaryForm "fun" Fun
      , astGenericIntroduction
      , astGenericReference
      , astGenericFunctionType
      , astBinary AST.SyntaxTypeOperator SyntaxType
      , astBinary AST.FunctionTypeOperator FunctionType
      , astBinary AST.ApplicationOperator FunctionApplication
      , astUnary AST.ExternalOperator External
      , astBlock "do" FunctionBody
      , astSequence
      , ArgumentMap <$> (astSymbol "{}" *> many astExpression)
      , astBinary AST.ConcatenationOperator MapConcatenation
      , astNaturalRangeExpression
      , try (astIdentifierTemplateOperation AST.AssignmentOperator (Just ()))
      , try (astIdentifierTemplateOperation AST.DependentIdentifierTypeOperator Nothing)
      , astIdentifierOperation AST.AssignmentOperator (Just ())
      , astIdentifierOperation AST.DependentIdentifierTypeOperator Nothing
      , astBinary AST.ExpansionOperator MapExpansion
      , astBinary AST.RangeOperator SuperEllipsisRange
      , astUnary AST.RangePlusOperator SuperEllipsisRangePlus
      , astUnary AST.RangeMinusOperator SuperEllipsisRangeMinus
      , try (astBinary AST.AdditionOperator Addition)
      , astUnary AST.AdditionOperator Plus
      , try (astBinary AST.SubtractionOperator Subtraction)
      , astUnary AST.MinusOperator Minus
      , astBinary AST.SubfederationOperator Subfederation
      , astBinary AST.InequalityOperator Inequality
      , astBinary AST.EqualityOperator Equality
      , astBinary AST.LessThanOrEqualOperator LessThanOrEqual
      , astBinary AST.GreaterThanOrEqualOperator GreaterThanOrEqual
      , astBinary AST.LessThanOperator LessThan
      , astBinary AST.GreaterThanOperator GreaterThan
      , astBinary AST.BooleanAndOperator BooleanAnd
      , astBinary AST.BooleanOrOperator BooleanOr
      , astUnary AST.BooleanNotOperator BooleanNot
      , astUnary AST.CoalizationOperator Coalization
      , astBlock "begin" Begin
      , astBlock "program" Program
      , astUnary AST.LetOperator Let
      , IdentifierReference . IdentifierString <$>
          (astSymbol "ref" *> astString)
      , astBinary AST.EitherOperator EitherType
      , astUnary AST.OptionalOperator OptionalType
      , astUnary AST.ListUnconsOperator ListUncons
      , astBinary AST.MaybeThenOperator MaybeThen
      , astConditional
      , astBinary AST.MultiplicationOperator Multiplication
      , astBinary AST.ExponentiationOperator Exponentiation
      , NamedAccess <$> (astSymbol "." *> astExpression) <*> (IdentifierString <$> astString)
      , astBinary AST.AccessOperator MapAccess
      , astBinary AST.SpecificationOperator MapSpecification
      , astBinary AST.SafeOverloadOperator SafeOverload
      , astBinary AST.OverloadOperator Overload
      ])

astGenericIntroduction :: Parser Expression
astGenericIntroduction = do
  _ <- astSymbol "generic-introduction"
  polarity <- astGenericPolarity
  identifier <- astExpression >>= astGenericIdentifier
  bound <- astExpression
  pure (GenericIntroductionExpression
    (GenericIntroduction polarity identifier bound Nothing))

astGenericReference :: Parser Expression
astGenericReference = do
  _ <- astSymbol "generic-reference"
  identity <- GenericBinderId <$> astLexeme Lexer.decimal
  role <- choice
    [ GenericDeclarationReference <$ astSymbol "declaration"
    , GenericUseReference <$ astSymbol "use"
    ]
  pure (GenericReferenceExpression (GenericReference identity role))

astGenericFunctionType :: Parser Expression
astGenericFunctionType = do
  _ <- astSymbol "generic-function-type"
  generics <- between (astSymbol "(") (astSymbol ")") $ do
    _ <- astSymbol "generic-prefix"
    many astGenericBinder
  FunctionTypeExpression generics
    <$> astExpression
    <*> astExpression

astGenericBinder :: Parser (GenericBinder Expression)
astGenericBinder = between (astSymbol "(") (astSymbol ")") $ do
  _ <- astSymbol "generic-binder"
  identity <- GenericBinderId <$> astLexeme Lexer.decimal
  polarity <- astGenericPolarity
  identifier <- astExpression >>= astGenericIdentifier
  bound <- astExpression
  pure GenericBinder
    { genericBinderId = identity
    , genericBinderPolarity = polarity
    , genericBinderIdentifier = identifier
    , genericBinderBound = bound
    , genericBinderSource = Nothing
    }

astGenericPolarity :: Parser GenericPolarity
astGenericPolarity = choice
  [ GenericProduct <$ astSymbol "&"
  , GenericSum <$ astSymbol "^"
  ]

astGenericIdentifier :: Expression -> Parser GenericIdentifier
astGenericIdentifier expressionValue = do
  identifier <- case expressionValue of
    IdentifierReference name -> pure (GenericIdentifier name False)
    OptionalType (IdentifierReference name) ->
      pure (GenericIdentifier name True)
    _ -> empty
  guard
    (not
      (genericIdentifierNameOptional identifier
        && null (public
          [(genericIdentifierText identifier, ())])))
  pure identifier

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

astIdentifierTemplateOperation
  :: AST.Operator
  -> Maybe ()
  -> Parser Expression
astIdentifierTemplateOperation operator assignmentMarker = do
  _ <- astOperatorToken operator
  template <- astLexeme astStringTemplateToken
  parts <- case template of
    StringTemplate values -> pure values
    _ -> empty
  typeAnnotation <- astExpression
  case assignmentMarker of
    Nothing ->
      pure (IdentifierTemplateOperation parts typeAnnotation Nothing)
    Just () -> do
      givenValue <- optional astExpression
      pure (IdentifierTemplateOperation
        parts typeAnnotation (Just (maybe typeAnnotation id givenValue)))

astConditional :: Parser Expression
astConditional = do
  _ <- astSymbol "if"
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
    [ RangePrefix <$ astSymbol "range"
    , FromPrefix <$ astSymbol "from"
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
        <$> (astSymbol "to" *> astSignedInteger)
    , NaturalRangeFromUpwards origin <$ astSymbol "up"
    , IntegerRangeFromDownwards origin <$ astSymbol "down"
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

astUnaryForm
  :: Text
  -> (Expression -> Expression)
  -> Parser Expression
astUnaryForm name constructor = do
  _ <- astSymbol name
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
astOperatorToken operator = astLexeme $ try $ do
  token <- chunk (Text.pack (AST.operatorCanonicalSymbol operator))
  _ <- lookAhead space1
  pure token

rawResourceWithEnvelope :: Parser (ResourceEnvelope, Expression)
rawResourceWithEnvelope = do
  fullSpaceConsumer
  result <- explicitResource <|> implicitResource
  fullSpaceConsumer
  eof
  pure result
  where
    explicitResource = do
      _ <- try (lookAhead outerMapEnvelope)
      (,) ExplicitMapEnvelope <$> parenthesizedExpression
    implicitResource = do
      entries <- elements
      pure (ImplicitBlockEnvelope, Program entries (AtlasMap []))

-- Parse the parenthesized expression itself in lookahead so the closing
-- parenthesis must enclose the whole resource. This distinguishes an explicit
-- map from an implicit sequence such as @(a); (b)@.
outerMapEnvelope :: Parser ()
outerMapEnvelope =
  void (parenthesizedExpression <* fullSpaceConsumer <* eof)

sequenceExpression :: [Expression] -> Expression
sequenceExpression [] = AtlasMap []
sequenceExpression [expressionValue] = expressionValue
sequenceExpression expressions = AtlasMap expressions

elements :: Parser [Expression]
elements = do
  first <- optional expression
  case first of
    Nothing -> pure []
    Just entry -> do
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
expression = expressionWith mapExpression

expressionWith :: Parser Expression -> Parser Expression
expressionWith operand = do
  target <- maybeThenExpressionWith operand
  maybeSource <-
    optional (continuedSymbol reverseSpecificationSymbol *> expressionWith operand)
  pure
    (case maybeSource of
      Nothing -> target
      Just source -> ReverseMapSpecification
        target
        (SyntaxBoundary source))

-- Maybe sequencing is deliberately low-precedence and right-associative so
-- its lazy branch can contain a complete function or map expression. The
-- list-sequencing shorthand lowers here so evaluation and inference share the
-- existing list split and Maybe sequencing semantics.
maybeThenExpressionWith :: Parser Expression -> Parser Expression
maybeThenExpressionWith operand =
  maybeThenExpressionFrom (functionExpressionWith operand)

maybeThenExpressionFrom :: Parser Expression -> Parser Expression
maybeThenExpressionFrom operand = do
  optionalValue <- operand
  continuation <- optional $ do
    constructor <-
      MaybeThen <$ continuedOperator AST.MaybeThenOperator
        <|> listMaybeThen <$ continuedOperator AST.ListMaybeThenOperator
    branch <- maybeThenExpressionFrom operand
    pure (constructor, branch)
  pure (case continuation of
    Nothing -> optionalValue
    Just (constructor, branch) -> constructor optionalValue branch)

-- @values !? function@ is exactly @values! ?? function it@. Keeping the
-- expansion structural also preserves the laziness of an absent list split.
listMaybeThen :: Expression -> Expression -> Expression
listMaybeThen values function =
  MaybeThen
    (ListUncons values)
    (FunctionApplication
      function
      (contextualAccess (IdentifierString "_it")))

functionExpressionWith :: Parser Expression -> Parser Expression
functionExpressionWith operand = do
  signature <- arrowExpressionWith operand
  attachFunctionImplementation signature

-- A code block turns an arrow-less expression into a function whose output is
-- unconstrained. Explicit function types retain their declared codomain.
attachFunctionImplementation :: Expression -> Parser Expression
attachFunctionImplementation signature = do
  implementation <- if acceptsFunctionBody signature
    then optional (functionImplementation signature)
    else pure Nothing
  pure (case implementation of
    Nothing -> signature
    Just body -> implementedFunction body signature)

acceptsFunctionBody :: Expression -> Bool
acceptsFunctionBody FunctionTypeExpression {} = True
acceptsFunctionBody SyntaxType {} = True
acceptsFunctionBody (Fun signature) = acceptsFunctionBody signature
acceptsFunctionBody (SyntaxBoundary signature) = acceptsFunctionBody signature
acceptsFunctionBody _ = False

-- @fun@ is syntax, so its capture is parsed before a following function body
-- is attached. Lift the fixed point over the completed function instead of
-- leaving it on the domain of an inferred outer function. Thus
-- @fun {x? : T} -> U do ...@ has the same AST as
-- @fun ({x? : T} -> U do ...)@.
implementedFunction :: Expression -> Expression -> Expression
implementedFunction body (Fun signature) =
  Fun (MapSpecification body signature)
implementedFunction body (SyntaxBoundary signature) =
  SyntaxBoundary (implementedFunction body signature)
implementedFunction body signature =
  MapSpecification body signature

-- External blocks are the only function implementations recognized by the
-- neutral reader. Declarative block forms are attached during syntax rewrite.
functionImplementation :: Expression -> Parser Expression
functionImplementation _ = externalExpression

externalExpression :: Parser Expression
externalExpression =
  External <$> (operatorToken AST.ExternalOperator *> externalTermAtom)

arrowExpressionWith :: Parser Expression -> Parser Expression
arrowExpressionWith = arrowExpressionWithLayer eitherExpressionWith

arrowExpressionWithLayer
  :: (Parser Expression -> Parser Expression)
  -> Parser Expression
  -> Parser Expression
arrowExpressionWithLayer expressionLayer operand = do
  rawInput <- expressionLayer operand
  let signature = arrowExpressionWithLayer expressionLayer operand
  input <- syntaxTypeSuffix rawInput signature
  output <- optional
    (continuedOperator AST.FunctionTypeOperator *> signature)
  pure (maybe input (FunctionType input) output)

syntaxTypeSuffix :: Expression -> Parser Expression -> Parser Expression
syntaxTypeSuffix input signature = do
  syntaxSignature <- optional . try $ do
    _ <- continuedOperator AST.SyntaxTypeOperator
    SyntaxType input <$> signature
  pure (maybe input id syntaxSignature)

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
    (try identifierTemplateOperation <|> try identifierOperation <|> rangeExpression)
    mapOperatorTable

identifierTemplateOperation :: Parser Expression
identifierTemplateOperation = do
  template <- try stringExpression
  parts <- case template of
    StringTemplate values -> pure values
    _ -> empty
  isOptional <-
    maybe False (const True)
      <$> optional (operatorToken AST.OptionalOperator)
  choice
    [ do
        _ <- continuedOperator AST.AssignmentOperator
        (typeAnnotation, givenValue) <- assignedIdentifierValue
        let operation = IdentifierTemplateOperation
              parts typeAnnotation (Just givenValue)
        pure (optionalIdentifier isOptional operation)
    , do
        _ <- continuedOperator AST.DependentIdentifierTypeOperator
        typeAnnotation <- identifierValueExpression
        givenValue <- optional (assignedValueFor typeAnnotation)
        let operation = IdentifierTemplateOperation parts typeAnnotation givenValue
        pure (optionalIdentifier isOptional operation)
    ]

-- A colon distinguishes a declaration from a bare lexical reference or call.
identifierOperation :: Parser Expression
identifierOperation = do
  identifierSpelling <- try identifierExpression
  let identifierName = case identifierSpelling of
        BareIdentifier name -> name
        FullStringIdentifier name -> name
  isOptional <-
    maybe False (const True)
      <$> optional (operatorToken AST.OptionalOperator)
  guard
    (not
      (isOptional
        && null (public [(identifierName, ())])))
  choice
    [ do
        _ <- continuedOperator AST.AssignmentOperator
        let name = case identifierSpelling of BareIdentifier value -> value; FullStringIdentifier value -> value
            operationIdentifierString = IdentifierString name
        (typeAnnotation, givenValue) <- assignedIdentifierValue
        void (validateIdentifierSpelling identifierSpelling)
        let operation =
              IdentifierOperation
                operationIdentifierString
                typeAnnotation
                (Just givenValue)
        pure (optionalIdentifier isOptional operation)
    , do
        _ <- continuedOperator AST.DependentIdentifierTypeOperator
        operationIdentifierString <-
          IdentifierString
            <$> pure (case identifierSpelling of BareIdentifier name -> name; FullStringIdentifier name -> name)
        typeAnnotation <- identifierValueExpression
        case typeAnnotation of
          SyntaxType {} -> pure ()
          _ -> void (validateIdentifierSpelling identifierSpelling)
        givenValue <- optional (assignedValueFor typeAnnotation)
        let operation =
              IdentifierOperation
                operationIdentifierString typeAnnotation givenValue
        pure (optionalIdentifier isOptional operation)
    ]

assignedValueFor :: Expression -> Parser Expression
assignedValueFor _ = do
  _ <- continuedOperator AST.AssignmentOperator
  assignedValueExpression

optionalIdentifier :: Bool -> Expression -> Expression
optionalIdentifier False operation = operation
optionalIdentifier True operation = OptionalType operation

assignedIdentifierValue :: Parser (Expression, Expression)
assignedIdentifierValue = do
  inferred <- assignedValueExpression
  pure (inferred, inferred)

-- Identifier annotations and assigned values may use range, arithmetic, and
-- access operators directly. Concatenation and specification are deliberately
-- excluded at this level so @,@ and @~>@ terminate the identifier operand;
-- explicit parentheses remain available when either belongs to the
-- identifier's own value.
identifierValueExpression :: Parser Expression
identifierValueExpression = do
  signature <- do
    rawInput <- makeExprParser rangeExpression identifierValueOperatorTable
    input <- syntaxTypeSuffix rawInput
      (arrowExpressionWith
        (makeExprParser rangeExpression identifierValueOperatorTable))
    output <- optional
      (continuedOperator AST.FunctionTypeOperator *> arrowExpressionWith
        (makeExprParser rangeExpression identifierValueOperatorTable))
    pure (maybe input (FunctionType input) output)
  attachFunctionImplementation signature

-- The value following @:=@ additionally admits an unparenthesized federation.
-- Type annotations keep the narrower grammar so @name : T | U@ continues to
-- mean a federation whose first member is a named type.
assignedValueExpression :: Parser Expression
assignedValueExpression = do
  signature <- arrowExpressionWithLayer
    assignmentEitherExpressionWith
    (makeExprParser rangeExpression identifierValueOperatorTable)
  attachFunctionImplementation signature

-- Assignment has lower precedence than federation, except that a following
-- identifier declaration starts the next federation member. Thus
-- @Alias := Nat | Str@ assigns the complete federation while
-- @False := 0 | True := 1@ remains a federation of two declarations.
assignmentEitherExpressionWith :: Parser Expression -> Parser Expression
assignmentEitherExpressionWith = eitherExpressionWithOperator
  (try
    (continuedOperator AST.EitherOperator
      <* notFollowedBy (try identifierOperationStart)))

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
  function <- accessedTerm externalTermAtom
  arguments <- many (try (applicationArgument function))
  pure (foldl FunctionApplication function arguments)
  where
    -- Horizontal whitespace has already been consumed by lexemes. A newline
    -- remains a block boundary; operator and syntax words cannot be arguments.
    applicationArgument function = accessedTerm (choice
      [ try identifierTemplateOperation
      , try identifierOperation
      , argumentMap
      , parenthesizedExpression
      , valueOfExpression
      , trailingApplicationSkip
      , prefixedApplicationArgument
      , lexeme (atomicExpressionToken sourceStringTemplateToken)
      , do
          guard (not (acceptsFunctionBody function))
          externalExpression
      , symbolicSyntaxLiteral
      , identifierReference
      ])

-- At an expression boundary, a bare @*@ cannot be multiplication because it
-- has no right operand. Keep it in the neutral application spine so declared
-- syntax such as @value of *@ can capture it as an expression hole. Ambiguous
-- arithmetic positions continue to require the grouped skip spelling @(*)@.
trailingApplicationSkip :: Parser Expression
trailingApplicationSkip = try $ do
  _ <- symbol (Text.pack AST.skipSourceSymbol)
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

externalTermAtom :: Parser Expression
externalTermAtom =
  externalExpression
    <|> termAtom

termAtom :: Parser Expression
termAtom =
  choice
    [ bareSkip
    , genericIntroduction
    , valueOfExpression
    , argumentMap
    , try parenthesizedReverseSpecification
    , parenthesizedExpression
    , lexeme (atomicExpressionToken sourceStringTemplateToken)
    , identifierReference
    ]

genericIntroduction :: Parser Expression
genericIntroduction = do
  (sourceSpan, (polarity, identifier, bound)) <- spanned $ do
    polarity <- choice
      [ GenericProduct <$ lexeme (char '&')
      , GenericSum <$ operatorToken AST.ExponentiationOperator
      ]
    spelling <- identifierExpression
    name <- validateIdentifierSpelling spelling
    optionalName <- maybe False (const True) <$> optional
      (operatorToken AST.OptionalOperator)
    guard
      (not
        (optionalName
          && null (public [(name, ())])))
    bound <- maybe
      (IdentifierReference (IdentifierString "Any"))
      id
      <$> optional
        (try (continuedSymbol "::" *> identifierValueExpression))
    pure
      ( polarity
      , GenericIdentifier (IdentifierString name) optionalName
      , bound
      )
  pure (GenericIntroductionExpression
    (GenericIntroduction polarity identifier bound (Just sourceSpan)))

-- Declarative syntax is discovered only after the complete resource has been
-- read, so the neutral reader must retain symbolic words that are not core
-- operators when they follow an already-parsed operand. Maximal-munch keeps
-- an adjacent spelling such as @2++@ as the application phrase @2 ++@; the
-- later syntax pass alone decides whether a visible postfix/infix template
-- gives that phrase meaning. Exact core tokens remain owned by their ordinary
-- grammar paths, and unknown prefix symbols remain parse errors.
--
-- A deeper parser cleanup should move neutral symbolic syntax beneath the
-- ordinary expression grammar. Then a successful core parse would naturally
-- win before an opaque symbolic literal, and this fallback would no longer
-- need to reserve compact core expressions explicitly.
symbolicSyntaxLiteral :: Parser Expression
symbolicSyntaxLiteral = lexeme . try $ do
  literal <- some (satisfy isSymbolicSyntaxCharacter)
  guard (literal `notElem` reservedCoreSymbolicRuns)
  guard (all (`notPrefixOf` literal) reservedCoreSymbolicPrefixes)
  pure (IdentifierReference (IdentifierString literal))
  where
    notPrefixOf prefix value = not (prefix `isPrefixOf` value)

coreSymbolicTokens :: [String]
coreSymbolicTokens = "&" : AST.ellipsisSymbol : Text.unpack reverseSpecificationSymbol :
  [ symbolText
  | operator <- [minBound .. maxBound]
  , Just symbolText <- [AST.operatorSourceSymbol operator]
  , any (not . isIdentifierCharacter) symbolText
  ]

-- Prefix operators and skip are separate tokens, but their compact forms are
-- complete core expressions. Derive those runs from the same prefix table
-- used by the arithmetic parser so new prefix operators cannot be forgotten.
reservedCoreSymbolicRuns :: [String]
reservedCoreSymbolicRuns = coreSymbolicTokens <> compactPrefixSkipRuns

-- Percent owns interpolation inside strings and syntax attachment between
-- expressions. Do not let longer unrecognized percent runs escape into the
-- declarative-symbol fallback as ordinary identifiers.
reservedCoreSymbolicPrefixes :: [String]
reservedCoreSymbolicPrefixes =
  [ symbolText
  | operator <- [AST.SyntaxTypeOperator]
  , Just symbolText <- [AST.operatorSourceSymbol operator]
  ]

compactPrefixSkipRuns :: [String]
compactPrefixSkipRuns =
  [ prefix <> AST.skipSourceSymbol
  | (operator, _) <- arithmeticPrefixOperators
  , Just prefix <- [AST.operatorSourceSymbol operator]
  ]

-- The skip atom and multiplication share @*@. A bare skip can participate in
-- every unambiguous expression position, but multiplication requires explicit
-- grouping on each skip side: @(*) * 7@ and @7 * (*)@.
bareSkip :: Parser Expression
bareSkip = do
  _ <- symbol (Text.pack AST.skipSourceSymbol)
  notFollowedBy (operatorToken AST.MultiplicationOperator)
  pure Skip

importExpression :: Parser Expression
importExpression = do
  _ <- continuedKeyword "import"
  allNames <- maybe False (const True) <$> optional (continuedKeyword "all")
  Import allNames <$> standardString

-- Scan import literals without interpreting strings as syntax. This allows the
-- loader to resolve dependencies before parsing expressions using their names.
sourceImports :: String -> Either ParseFailure [String]
sourceImports = fmap (map snd) . sourceImportInvocations

sourceImportInvocations :: String -> Either ParseFailure [(Bool, String)]
sourceImportInvocations source = Bifunctor.first (ParseFailure . errorBundlePretty) $
  runParser (runReaderT scan
    (ParserContext 0))
    "<imports>" (Text.pack source)
  where
    invocations (Import allNames path) = [(allNames, path)]
    invocations _ = []
    scan = concat <$> many item <* eof
    item = try (invocations <$> importExpression)
      <|> ([] <$ sourceStringTemplateToken)
      <|> ([] <$ lineComment)
      <|> ([] <$ anySingle)

identifierReference :: Parser Expression
identifierReference = try $ do
  first <- bareIdentifierToken
  horizontalSpaceConsumer
  name <- validateIdentifierSpelling (BareIdentifier first)
  pure (IdentifierReference (IdentifierString name))

-- Argument maps use the same expression operators and sequence separators as
-- parenthesized maps: comma concatenates within one expression, while a
-- semicolon or newline starts the next argument-map member.
argumentMap :: Parser Expression
argumentMap = do
  members <- between (symbol "{" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol "}")
    elements
  guard (all validDependentName members)
  pure (ArgumentMap members)
  where
    validDependentName _ = True

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
        _ <- try (char '.' <* notFollowedBy (char '.'))
        horizontalSpaceConsumer
        names <- namedAccessNames
        horizontalSpaceConsumer
        pure (expandedNamedAccess names)
    , OptionalType <$ optionalTypeSuffix
    , ListUncons <$ listUnconsSuffix
    ])
  pure (foldl (\value select -> select value) source selections)

optionalTypeSuffix :: Parser Text
optionalTypeSuffix = try $ do
  token <- operatorToken AST.OptionalOperator
  notFollowedBy (char ':')
  pure token

listUnconsSuffix :: Parser Text
listUnconsSuffix = operatorToken AST.ListUnconsOperator

namedAccessNames :: Parser [IdentifierString]
namedAccessNames = parenthesized <|> ((: []) <$> namedAccessName)
  where
    parenthesized = between
      (symbol "(" <* lineSpaceConsumer)
      (lineSpaceConsumer *> symbol ")") $ do
        first <- namedAccessName
        rest <- many
          (continuedOperator AST.ConcatenationOperator *> namedAccessName)
        pure (first : rest)

-- Like named access, the operand denotes names rather than evaluating them.
-- Subsequent selections apply to the retrieved value: @~a[0]@ means
-- @this.a[1][0]@. Keep this sugar in the core grammar so serialized closures
-- can use it without importing a syntax declaration from Std.
valueOfExpression :: Parser Expression
valueOfExpression = do
  _ <- operatorToken AST.ValueOfOperator
  names <- namedAccessNames
  horizontalSpaceConsumer
  notFollowedBy (operatorToken AST.ExponentiationOperator)
  pure (MapAccess
    (expandedNamedAccess names
      (contextualAccess (IdentifierString "_this")))
    (EllipsisNatural 1))

namedAccessName :: Parser IdentifierString
namedAccessName =
  IdentifierString <$> (bareIdentifierToken <|> standardStringToken)

expandedNamedAccess
  :: [IdentifierString]
  -> Expression
  -> Expression
expandedNamedAccess names value =
  case map (NamedAccess value) names of
    [] -> value
    first : rest -> foldl MapConcatenation first rest

bracketedInsertion :: Parser Expression
bracketedInsertion =
  between
    (symbol "[" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol "]")
    (do
      selections <- elements
      guard (not (null selections))
      pure (sequenceExpression selections))

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

continuedKeyword :: Text -> Parser Text
continuedKeyword value = keywordToken value <* keywordSeparator

keywordToken :: Text -> Parser Text
keywordToken value =
  try
    (value <$ chunk value
      <* notFollowedBy (satisfy isIdentifierCharacter))

keywordSeparator :: Parser ()
keywordSeparator =
  void (some (void space1 <|> lineComment))

parenthesizedExpression :: Parser Expression
parenthesizedExpression =
  between
    (symbol "(" <* lineSpaceConsumer)
    (lineSpaceConsumer *> symbol ")")
    (SyntaxBoundary . sequenceExpression <$> elements)

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
  [ [InfixR (Exponentiation <$ exponentiationOperator infixOperator)]
  , [ Prefix (constructor <$ operatorToken operator)
    | (operator, constructor) <- arithmeticPrefixOperators
    ]
  , [InfixL (Multiplication <$ multiplicationOperator infixOperator)]
  , [ InfixL (Addition <$ infixOperator AST.AdditionOperator)
    , InfixL (Subtraction <$ infixOperator AST.SubtractionOperator)
    ]
  ]

arithmeticPrefixOperators :: [(AST.Operator, Expression -> Expression)]
arithmeticPrefixOperators =
  [ (AST.AdditionOperator, Plus)
  , (AST.MinusOperator, Minus)
  , (AST.CoalizationOperator, Coalization)
  ]

-- Parentheses make transitions between prefix value lookup and infix
-- exponentiation explicit.
exponentiationOperator
  :: (AST.Operator -> Parser Text)
  -> Parser Text
exponentiationOperator infixOperator = try $ do
  token <- infixOperator AST.ExponentiationOperator
  notFollowedBy (operatorToken AST.ValueOfOperator)
  pure token

multiplicationOperator
  :: (AST.Operator -> Parser Text)
  -> Parser Text
multiplicationOperator infixOperator = try $ do
  token <- infixOperator AST.MultiplicationOperator
  notFollowedBy (char '*')
  pure token

operatorBeforeIdentifierBoundary :: AST.Operator -> Parser Text
operatorBeforeIdentifierBoundary operator = try $ do
  continuedOperator operator
    <* notFollowedBy (try identifierOperationStart)

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

reverseSpecificationSymbol :: Text
reverseSpecificationSymbol = "<~"

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
        , operatorToken AST.SafeOverloadOperator
        , operatorToken AST.ReverseSafeOverloadOperator
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

identifierExpression :: Parser IdentifierSpelling
identifierExpression =
  FullStringIdentifier <$> standardString
    <|> BareIdentifier <$> bareIdentifier

astIdentifierExpression :: Parser IdentifierSpelling
astIdentifierExpression =
  FullStringIdentifier <$> astStandardString
    <|> BareIdentifier <$> astBareIdentifier

validateIdentifierSpelling :: IdentifierSpelling -> Parser String
validateIdentifierSpelling = maybe empty pure . identifierSpellingValue

bareIdentifierToken :: Parser String
bareIdentifierToken = do
  first <- satisfy isLeadingIdentifierCharacter
  rest <- many (satisfy isIdentifierCharacter)
  let value = first : rest
  if isIdentifierValue value then pure value else empty

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
      ParsedStringTemplateInterpolation . StringTemplateInterpolation
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
simpleInterpolationWith = id

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

operatorToken :: AST.Operator -> Parser Text
operatorToken operator = lexeme $ try $ do
  sourceText <-
    case AST.operatorSourceSymbol operator of
      Just value -> pure (Text.pack value)
      Nothing -> empty
  token <- chunk sourceText
  case operator of
    AST.MinusOperator -> notFollowedBy (char '>')
    AST.SubtractionOperator -> notFollowedBy (char '>')
    AST.OptionalOperator -> notFollowedBy (char '?')
    AST.ListUnconsOperator -> notFollowedBy (char '?' <|> char '~')
    AST.ValueOfOperator -> notFollowedBy (char '>' <|> char '%')
    AST.SyntaxTypeOperator -> notFollowedBy (char '%')
    AST.LessThanOperator -> notFollowedBy (char '=' <|> char '<' <|> char '~')
    AST.GreaterThanOperator -> notFollowedBy (char '=' <|> char '>')
    _ -> pure ()
  pure token

continuedOperator :: AST.Operator -> Parser Text
continuedOperator operator = operatorToken operator <* lineSpaceConsumer

semicolon :: Parser Text
semicolon = symbol ";"
