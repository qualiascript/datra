{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..), SyntaxRuleIdentity (..)
  , syntaxRuleDeclaredName, syntaxRuleLabel
  , DeclarativeMatcherPlan (..)
  , NativeApplicationPattern (..), ExactPresentationPattern (..)
  , ExactPresentationPart (..)
  , AtlasSyntaxPattern (..), AtlasSyntaxPart (..)
  , DependentSyntaxRule (..)
  , SyntaxRuleSemantics (..), DependentSyntaxInvocation (..)
  , StringInterpolationTemplate, StringTemplateInterpolation (..)
  , StringExpression (..)
  , TemplateSelection (..)
  , declarationRules, declarationRuleBranches
  , syntaxRuleCaptures, mapSyntaxRuleCaptures
  , exactPresentationPattern
  , syntaxApplicationRule
  , commentSyntaxRule
  , lineSyntaxRule
  , horizontalApplicationRule
  , syntaxWhitespaceSource
  , horizontalSyntaxWhitespace
  , lineSeparatedApplication
  , horizontallySeparatedApplication
  , syntaxApplicationImplementation
  , syntaxDependentRule, syntaxRuleAdapter
  , expandSyntax
  , declarationLiterals
  ) where
import DatraLanguage.DependentDeclaration
  ( dependentDeclaration
  , dependentDeclarationTemplateBranches
  )
import DatraLanguage.AST
import DatraLanguage.Identifier (isIdentifierValue)
import StringExpression
  ( StringExpression (..)
  , stringExpressionValue
  , StringInterpolationTemplate
  , TemplateSelection (..)
  )
import DatraLanguage.ConcreteSyntax
  ( commentCharacter
  , isSourceHorizontalPresentationCharacter
  , isSourceLineBreakCharacter
  , isSourcePresentationCharacter
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Application
  ( applicationFrom, rawApplicationPhrase )
import Control.Monad (guard)

data DeclarativeMatcherPlan
  = NativeApplicationMatcher NativeApplicationPattern
  | AtlasSyntaxMatcher AtlasSyntaxPattern
  | ExactPresentationMatcher
      (ExactPresentationPattern (StringExpression Expression))
  | LineSequenceMatcher
  | HorizontalApplicationMatcher
  deriving (Eq, Show)

data NativeApplicationPattern = NativeApplicationPattern
  { nativeApplicationHead :: Expression
  , nativeApplicationOperand :: StringExpression Expression
  }
  deriving (Eq, Show)

newtype ExactPresentationPattern capture = ExactPresentationPattern
  { exactPresentationParts :: [ExactPresentationPart capture]
  }
  deriving (Eq, Show)

data ExactPresentationPart capture
  = ExactPresentationLiteral String
  | ExactPresentationCapture capture
  deriving (Eq, Show)

-- | The matcher AST for declaration forms whose syntax is already structural.
-- Literals and captures are nodes in this tree; neither is encoded as a value
-- which must be rendered and rediscovered by the expression parser.
newtype AtlasSyntaxPattern = AtlasSyntaxPattern
  { atlasSyntaxParts :: [AtlasSyntaxPart]
  }
  deriving (Eq, Show)

data AtlasSyntaxPart
  = AtlasSyntaxLiteral Expression
  | AtlasSyntaxCapture (StringExpression Expression)
  deriving (Eq, Show)

data SyntaxRuleIdentity
  = DeclaredSyntaxName String
  | CommentSyntaxIdentity
  | LineSequenceSyntaxIdentity
  | HorizontalApplicationSyntaxIdentity
  deriving (Eq, Show)

data SyntaxRule = SyntaxRule
  { syntaxIdentity :: SyntaxRuleIdentity
  , declarativeMatcherPlan :: DeclarativeMatcherPlan
  , syntaxSemantics :: SyntaxRuleSemantics
  } deriving (Eq,Show)

syntaxRuleDeclaredName :: SyntaxRule -> Maybe String
syntaxRuleDeclaredName rule = case syntaxIdentity rule of
  DeclaredSyntaxName name -> Just name
  _ -> Nothing

-- Diagnostic rendering is the only place built-in identities become text.
syntaxRuleLabel :: SyntaxRule -> String
syntaxRuleLabel rule = case syntaxIdentity rule of
  DeclaredSyntaxName name -> name
  CommentSyntaxIdentity -> "comment"
  LineSequenceSyntaxIdentity -> "line sequence"
  HorizontalApplicationSyntaxIdentity -> "horizontal application"

syntaxRuleCaptures :: SyntaxRule -> [StringExpression Expression]
syntaxRuleCaptures rule = case declarativeMatcherPlan rule of
  NativeApplicationMatcher patternValue ->
    [nativeApplicationOperand patternValue]
  AtlasSyntaxMatcher (AtlasSyntaxPattern parts) ->
    [capture | AtlasSyntaxCapture capture <- parts]
  ExactPresentationMatcher (ExactPresentationPattern parts) ->
    [capture | ExactPresentationCapture capture <- parts]
  LineSequenceMatcher -> []
  HorizontalApplicationMatcher -> []

exactPresentationPattern
  :: StringInterpolationTemplate Expression
  -> ExactPresentationPattern (StringExpression Expression)
exactPresentationPattern = ExactPresentationPattern . map part
  where
    part (StringTemplateInterpolation expressionValue) =
      case expressionValue of
        LiteralString literal -> ExactPresentationLiteral literal
        capture -> ExactPresentationCapture capture

mapSyntaxRuleCaptures
  :: (StringExpression Expression -> StringExpression Expression)
  -> SyntaxRule
  -> SyntaxRule
mapSyntaxRuleCaptures transform rule = rule
  { declarativeMatcherPlan = case declarativeMatcherPlan rule of
      NativeApplicationMatcher patternValue -> NativeApplicationMatcher
        patternValue
          { nativeApplicationOperand =
              transform (nativeApplicationOperand patternValue)
          }
      AtlasSyntaxMatcher (AtlasSyntaxPattern parts) ->
        AtlasSyntaxMatcher (AtlasSyntaxPattern (map mapAtlasPart parts))
      ExactPresentationMatcher (ExactPresentationPattern parts) ->
        ExactPresentationMatcher
          (ExactPresentationPattern (map mapExactPart parts))
      LineSequenceMatcher -> LineSequenceMatcher
      HorizontalApplicationMatcher -> HorizontalApplicationMatcher
  }
  where
    mapAtlasPart patternValue = case patternValue of
      AtlasSyntaxLiteral literal -> AtlasSyntaxLiteral literal
      AtlasSyntaxCapture capture -> AtlasSyntaxCapture (transform capture)
    mapExactPart partValue = case partValue of
      ExactPresentationLiteral literal -> ExactPresentationLiteral literal
      ExactPresentationCapture capture ->
        ExactPresentationCapture (transform capture)

data SyntaxRuleSemantics
  = SyntaxAdapter Expression
  | SyntaxApplication Expression Expression
  | DependentSyntax DependentSyntaxRule
  | SyntaxDiscard
  | SyntaxLineSequence
  | SyntaxHorizontalApplication
  deriving (Eq, Show)

data DependentSyntaxRule = DependentSyntaxRule
  { dependentSyntaxCaptures
      :: [Maybe (SimpleIdentifierString, Expression)]
  , dependentSyntaxImplementation :: Expression
  , dependentSyntaxInvocation :: DependentSyntaxInvocation
  } deriving (Eq, Show)

data DependentSyntaxInvocation
  = DependentSyntaxLookup [StringTemplateInterpolation Expression]
  deriving (Eq, Show)

syntaxDependentRule :: SyntaxRule -> Maybe DependentSyntaxRule
syntaxDependentRule rule = case syntaxSemantics rule of
  SyntaxAdapter {} -> Nothing
  SyntaxApplication {} -> Nothing
  DependentSyntax dependent -> Just dependent
  SyntaxDiscard -> Nothing
  SyntaxLineSequence -> Nothing
  SyntaxHorizontalApplication -> Nothing

syntaxRuleAdapter :: SyntaxRule -> Maybe Expression
syntaxRuleAdapter rule = case syntaxSemantics rule of
  SyntaxAdapter adapter -> Just adapter
  SyntaxApplication _ implementation -> Just implementation
  DependentSyntax dependent -> Just
    (dependentSyntaxImplementation dependent)
  SyntaxDiscard -> Nothing
  SyntaxLineSequence -> Nothing
  SyntaxHorizontalApplication -> Nothing

syntaxApplicationImplementation :: SyntaxRule -> Maybe Expression
syntaxApplicationImplementation rule = case syntaxSemantics rule of
  SyntaxApplication _ implementation -> Just implementation
  _ -> Nothing

-- | The first declaration in every syntax environment. Its operand has
-- already been delimited by the concrete parser, but remains ordinary syntax
-- data until this rule discards it.
commentSyntaxRule :: SyntaxRule
commentSyntaxRule = SyntaxRule
  { syntaxIdentity = CommentSyntaxIdentity
  , declarativeMatcherPlan = NativeApplicationMatcher
      (NativeApplicationPattern
        (UnresolvedSyntaxLiteral [commentCharacter])
        (ExpressionString (AtlasMap [])))
  , syntaxSemantics = SyntaxDiscard
  }

-- | Final built-in declarations. They assign semantics to unresolved source
-- separators only after visible declarations have matched their presentation.
lineSyntaxRule :: SyntaxRule
lineSyntaxRule = SyntaxRule
  { syntaxIdentity = LineSequenceSyntaxIdentity
  , declarativeMatcherPlan = LineSequenceMatcher
  , syntaxSemantics = SyntaxLineSequence
  }

horizontalApplicationRule :: SyntaxRule
horizontalApplicationRule = SyntaxRule
  { syntaxIdentity = HorizontalApplicationSyntaxIdentity
  , declarativeMatcherPlan = HorizontalApplicationMatcher
  , syntaxSemantics = SyntaxHorizontalApplication
  }

declarationRules :: Expression -> [SyntaxRule]
declarationRules = map third . declarationRuleBranches
  where
    third (_, _, rule) = rule

declarationRuleBranches
  :: Expression
  -> [(DependentDeclaration Expression, Int, SyntaxRule)]
declarationRuleBranches expressionValue =
  case dependentDeclaration expressionValue of
    Nothing -> []
    Just declaration -> dependentDeclarationRuleBranches declaration

dependentDeclarationRuleBranches
  :: DependentDeclaration Expression
  -> [(DependentDeclaration Expression, Int, SyntaxRule)]
dependentDeclarationRuleBranches declaration =
  case dependentDeclarationHead declaration of
    IdentifierExpressionBody (IdentifierReference name) ->
      [(declaration, 0, simpleApplicationRule declaration name)]
    AtlasIdentifierExpressionBody body -> zipWith
      (\branch (patternValue, captures) ->
        ( declaration
        , branch
        , structuralTemplateRule declaration patternValue captures
        ))
      [0 ..]
      (atlasSyntaxPatternBranches body)
    _ -> zipWith
      (\branch parts ->
        (declaration, branch, directTemplateRule declaration parts))
      [0 ..]
      (dependentDeclarationSyntaxAlternatives declaration)

simpleApplicationRule
  :: DependentDeclaration Expression
  -> SimpleIdentifierString
  -> SyntaxRule
simpleApplicationRule declaration (SimpleIdentifierString text) =
  syntaxApplicationRule
    text
    (SimpleIdentifierString text)
    (dependentLookup [literalInterpolation text] [])
    (dependentDeclarationImplementation declaration)

syntaxApplicationRule
  :: String
  -> SimpleIdentifierString
  -> Expression
  -> Expression
  -> SyntaxRule
syntaxApplicationRule name literalHead callable implementation = SyntaxRule
  { syntaxIdentity = DeclaredSyntaxName name
  , declarativeMatcherPlan = NativeApplicationMatcher
      (NativeApplicationPattern
        (IdentifierReference literalHead)
        (ExpressionString (AtlasMap [])))
  , syntaxSemantics = SyntaxApplication callable implementation
  }

directTemplateRule
  :: DependentDeclaration Expression
  -> [StringTemplateInterpolation Expression]
  -> SyntaxRule
directTemplateRule declaration parts =
  SyntaxRule
    { syntaxIdentity = DeclaredSyntaxName (case dependentDeclarationHead declaration of
        IdentifierExpressionBody
            (IdentifierReference (SimpleIdentifierString name)) -> name
        IdentifierExpressionBody (AsciiStringLiteral name) -> name
        _ -> renderSourceExpression (StringTemplate parts)
      )
    , declarativeMatcherPlan =
        ExactPresentationMatcher (exactPresentationPattern template)
    , syntaxSemantics = DependentSyntax (DependentSyntaxRule
        captures
        (dependentDeclarationImplementation declaration)
        (DependentSyntaxLookup parts))
    }
  where
    (template, captures) = compileDependentDeclarationTemplate parts

structuralTemplateRule
  :: DependentDeclaration Expression
  -> AtlasSyntaxPattern
  -> [Maybe (SimpleIdentifierString, Expression)]
  -> SyntaxRule
structuralTemplateRule declaration patternValue captures = SyntaxRule
  { syntaxIdentity = DeclaredSyntaxName (case atlasSyntaxLiterals patternValue of
      name : _ -> name
      [] -> renderSourceExpression
        (identifierHeadExpression (dependentDeclarationHead declaration))
    )
  , declarativeMatcherPlan = AtlasSyntaxMatcher patternValue
  , syntaxSemantics = DependentSyntax (DependentSyntaxRule
      captures
      (dependentDeclarationImplementation declaration)
      (DependentSyntaxLookup
        (atlasSyntaxInvocation patternValue)))
  }
  where
    identifierHeadExpression headValue = case headValue of
      IdentifierExpressionBody body -> IdentifierExpression body
      AtlasIdentifierExpressionBody body -> AtlasIdentifierExpression body

atlasSyntaxLiterals
  :: AtlasSyntaxPattern
  -> [String]
atlasSyntaxLiterals (AtlasSyntaxPattern parts) =
  [renderSourceExpression literal | AtlasSyntaxLiteral literal <- parts]

atlasSyntaxInvocation
  :: AtlasSyntaxPattern
  -> [StringTemplateInterpolation Expression]
atlasSyntaxInvocation (AtlasSyntaxPattern parts) = map invocation parts
  where
    invocation partValue = case partValue of
      AtlasSyntaxLiteral literal -> StringTemplateInterpolation
        (AsciiStringLiteral (renderSourceExpression literal))
      AtlasSyntaxCapture capture -> StringTemplateInterpolation
        (maybe (AsciiStringLiteral "") id (stringExpressionValue capture))

atlasSyntaxPatternBranches
  :: Expression
  -> [(AtlasSyntaxPattern, [Maybe (SimpleIdentifierString, Expression)])]
atlasSyntaxPatternBranches expressionValue =
  [ (AtlasSyntaxPattern patterns, concat captures)
  | parts <- atlasSyntaxAlternatives expressionValue
  , let compiled = map compileAtlasSyntaxPart parts
        patterns = map fst compiled
        captures = map snd compiled
  , not (null patterns)
  ]
  where
    atlasSyntaxAlternatives value = case value of
      SyntaxBoundary inner -> atlasSyntaxAlternatives inner
      AtlasMap members -> atlasSyntaxSequence members
      MapSequence members -> atlasSyntaxSequence members
      EitherType left right ->
        atlasSyntaxAlternatives left <> atlasSyntaxAlternatives right
      OptionalType present -> atlasSyntaxAlternatives present <> [[]]
      _ -> [[value]]
    atlasSyntaxSequence =
      foldl combine [[]] . map atlasSyntaxAlternatives
    combine prefixes suffixes =
      [ prefix <> suffix | prefix <- prefixes, suffix <- suffixes ]
    compileAtlasSyntaxPart value = case value of
      IdentifierExpression (IdentifierReference literal) ->
        (AtlasSyntaxLiteral (IdentifierReference literal), [])
      IdentifierExpression (AsciiStringLiteral literal) ->
        (AtlasSyntaxLiteral (atlasSyntaxLiteral literal), [])
      _ ->
        let (target, name) = captureDescriptor value
        in (AtlasSyntaxCapture (ValueString target), [name])
    atlasSyntaxLiteral literal
      | isIdentifierValue literal =
          IdentifierReference (SimpleIdentifierString literal)
      | otherwise = UnresolvedSyntaxLiteral literal

dependentDeclarationSyntaxAlternatives
  :: DependentDeclaration Expression
  -> [[StringTemplateInterpolation Expression]]
dependentDeclarationSyntaxAlternatives declaration =
  maybe [] id (dependentDeclarationTemplateBranches declaration)

compileDependentDeclarationTemplate
  :: [StringTemplateInterpolation Expression]
  -> ( StringInterpolationTemplate Expression
     , [Maybe (SimpleIdentifierString, Expression)]
     )
compileDependentDeclarationTemplate parts =
  let (pieces, captures) = foldMap compilePart parts
  in (pieces, captures)
  where
    compilePart
        (StringTemplateInterpolation (AsciiStringLiteral literal)) =
      ([StringTemplateInterpolation (LiteralString literal)], [])
    compilePart (StringTemplateInterpolation expressionValue) =
      let (target, name) = captureDescriptor expressionValue
      in ([StringTemplateInterpolation (ValueString target)], [name])

captureDescriptor
  :: Expression
  -> (Expression, Maybe (SimpleIdentifierString, Expression))
captureDescriptor (SyntaxBoundary inner) = captureDescriptor inner
captureDescriptor (DependentArgument nameExpression (Just annotation))
  | Just name <- literalIdentifierName nameExpression =
      (annotation, Just (name, annotation))
captureDescriptor value = (value, Nothing)

-- | Expand captures selected by one declared string interpolation.
expandSyntax
  :: SyntaxRule
  -> TemplateSelection Expression Expression
  -> Expression
expandSyntax rule selection =
  case syntaxSemantics rule of
    DependentSyntax dependent -> case dependentSyntaxInvocation dependent of
      DependentSyntaxLookup parts -> selectedDependentLookup parts captures
    SyntaxAdapter adapter -> FunctionApplication adapter suppliedInput
    SyntaxApplication callable _ ->
      FunctionApplication callable suppliedInput
    SyntaxDiscard -> ElidedSyntax
    SyntaxLineSequence -> maybe whole id
      (lineSeparatedApplication whole)
    SyntaxHorizontalApplication -> maybe whole id
      (horizontallySeparatedApplication whole)
  where
    whole = templateSelectionWhole selection
    captures = templateSelectionCaptures selection
    suppliedInput = case captures of
      [] -> AtlasMap []
      [value] -> value
      values -> AtlasMap values
    -- Function preparation overloads this supplied tail onto the declared
    -- domain. Empty, singleton, and multi-capture syntax therefore follows the
    -- same call path as an ordinary partial argumentative map.

syntaxWhitespaceSource :: String -> Bool
syntaxWhitespaceSource source =
  not (null source) && all isSourcePresentationCharacter source

horizontalSyntaxWhitespace :: String -> Bool
horizontalSyntaxWhitespace source =
  not (null source) && all isSourceHorizontalPresentationCharacter source

lineSyntaxWhitespace :: String -> Bool
lineSyntaxWhitespace source =
  syntaxWhitespaceSource source
    && any isSourceLineBreakCharacter source

lineSeparatedApplication :: Expression -> Maybe Expression
lineSeparatedApplication expressionValue = do
  let (completedReversed, currentReversed, foundLine) =
        foldl splitLine ([], [], False) (rawApplicationPhrase expressionValue)
      linePhrases = reverse
        (reverse currentReversed : completedReversed)
  guard foundLine
  guard (all (not . null) linePhrases)
  pure (AtlasMap (map applicationFrom linePhrases))
  where
    splitLine (completed, current, foundLine) member
      | lineWhitespaceLiteral member =
          (reverse current : completed, [], True)
      | otherwise = (completed, member : current, foundLine)

horizontallySeparatedApplication :: Expression -> Maybe Expression
horizontallySeparatedApplication expressionValue = do
  let phrase = rawApplicationPhrase expressionValue
      operands = filter (not . horizontalWhitespaceLiteral) phrase
  guard (not (any lineWhitespaceLiteral phrase))
  guard (any horizontalWhitespaceLiteral phrase)
  case operands of
    [] -> Nothing
    _ -> pure (applicationFrom operands)

horizontalWhitespaceLiteral :: Expression -> Bool
horizontalWhitespaceLiteral (UnresolvedSyntaxLiteral source) =
  horizontalSyntaxWhitespace source
horizontalWhitespaceLiteral _ = False

lineWhitespaceLiteral :: Expression -> Bool
lineWhitespaceLiteral (UnresolvedSyntaxLiteral source) =
  lineSyntaxWhitespace source
lineWhitespaceLiteral _ = False

dependentLookup
  :: [StringTemplateInterpolation Expression]
  -> [Expression]
  -> Expression
dependentLookup parts values =
  lookupExpression (StringTemplate (substituteCaptures parts values))

-- Keep the selected branch and its source captures alongside the ordinary
-- lookup query. Evaluation uses them only to preserve deferred fixed points;
-- the lookup still resolves through the normal named-map interface.
selectedDependentLookup
  :: [StringTemplateInterpolation Expression]
  -> [Expression]
  -> Expression
selectedDependentLookup parts values =
  lookupExpression (ArgumentativeMap
    [ StringTemplate parts
    , StringTemplate (substituteCaptures parts values)
    ])

lookupExpression :: Expression -> Expression
lookupExpression operand =
  ScopeAccess
    (MapAccess
      (Lookup operand)
      (EllipsisNatural 0))
    (IdentifierReference (SimpleIdentifierString "value"))

substituteCaptures
  :: [StringTemplateInterpolation Expression]
  -> [Expression]
  -> [StringTemplateInterpolation Expression]
substituteCaptures [] _ = []
substituteCaptures
    ( literalPart@(StringTemplateInterpolation (AsciiStringLiteral _))
      : remaining
    )
    arguments =
  literalPart : substituteCaptures remaining arguments
substituteCaptures (StringTemplateInterpolation _ : remaining)
    (argument : arguments) =
  StringTemplateInterpolation argument :
    substituteCaptures remaining arguments
substituteCaptures
    (interpolation@StringTemplateInterpolation {} : remaining) [] =
  interpolation : substituteCaptures remaining []

literalInterpolation :: String -> StringTemplateInterpolation Expression
literalInterpolation = StringTemplateInterpolation . AsciiStringLiteral

-- Literal alternatives of a named type can be spelled as keywords in an AST
-- pattern, while ordinary application keeps their $identifier value spelling.
declarationLiterals :: [Expression] -> String -> [String]
declarationLiterals declarations typeName = concatMap declaration declarations
  where
    declaration dependent
      | Just semantic <- dependentDeclaration dependent
      , IdentifierExpressionBody
          (IdentifierReference (SimpleIdentifierString name)) <-
          dependentDeclarationHead semantic
      , name == typeName = literals
          (dependentDeclarationImplementation semantic)
    declaration _ = []
    literals (AsciiStringLiteral text) = [text]
    literals (EitherType a b) = literals a <> literals b
    literals _ = []
