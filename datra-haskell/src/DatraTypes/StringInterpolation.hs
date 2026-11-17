{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..), SyntaxRuleIdentity (..)
  , syntaxRuleDeclaredName, syntaxRuleLabel
  , DeclarativeMatcherPlan (..)
  , NativeApplicationPattern (..), ExactPresentationPattern (..)
  , ExactPresentationPart (..)
  , DeclarativeCapture (..)
  , LiteralTemplatePattern (..), LiteralTemplatePatternPart (..)
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
import StringExpression
  ( StringExpression (..)
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
import Data.Foldable (toList)

data DeclarativeMatcherPlan
  = NativeApplicationMatcher NativeApplicationPattern
  | LiteralTemplateMatcher LiteralTemplatePattern
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

-- | Captures from literal expressions retain the existing string-expression
-- descriptor. A literal-template capture instead retains the Datra target
-- expression written after @%@; it is never converted to a string expression.
data DeclarativeCapture
  = StringExpressionCapture (StringExpression Expression)
  | LiteralTemplateCapture Expression
  deriving (Eq, Show)

newtype LiteralTemplatePattern = LiteralTemplatePattern
  { literalTemplatePatternParts :: [LiteralTemplatePatternPart]
  }
  deriving (Eq, Show)

data LiteralTemplatePatternPart
  = LiteralTemplatePatternLiteral LiteralTemplateLiteral
  | LiteralTemplatePatternCapture Expression
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

syntaxRuleCaptures :: SyntaxRule -> [DeclarativeCapture]
syntaxRuleCaptures rule = case declarativeMatcherPlan rule of
  NativeApplicationMatcher patternValue ->
    [StringExpressionCapture (nativeApplicationOperand patternValue)]
  LiteralTemplateMatcher (LiteralTemplatePattern parts) ->
    [ LiteralTemplateCapture capture
    | LiteralTemplatePatternCapture capture <- parts
    ]
  ExactPresentationMatcher (ExactPresentationPattern parts) ->
    [ StringExpressionCapture capture
    | ExactPresentationCapture capture <- parts
    ]
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
  :: (DeclarativeCapture -> DeclarativeCapture)
  -> SyntaxRule
  -> SyntaxRule
mapSyntaxRuleCaptures transform rule = rule
  { declarativeMatcherPlan = case declarativeMatcherPlan rule of
      NativeApplicationMatcher patternValue -> NativeApplicationMatcher
        patternValue
          { nativeApplicationOperand =
              mapStringCapture (nativeApplicationOperand patternValue)
          }
      LiteralTemplateMatcher (LiteralTemplatePattern parts) ->
        LiteralTemplateMatcher
          (LiteralTemplatePattern (map mapLiteralTemplatePart parts))
      ExactPresentationMatcher (ExactPresentationPattern parts) ->
        ExactPresentationMatcher
          (ExactPresentationPattern (map mapExactPart parts))
      LineSequenceMatcher -> LineSequenceMatcher
      HorizontalApplicationMatcher -> HorizontalApplicationMatcher
  }
  where
    mapExactPart partValue = case partValue of
      ExactPresentationLiteral literal -> ExactPresentationLiteral literal
      ExactPresentationCapture capture ->
        ExactPresentationCapture (mapStringCapture capture)
    mapStringCapture capture = case transform
        (StringExpressionCapture capture) of
      StringExpressionCapture transformed -> transformed
      LiteralTemplateCapture _ -> capture
    mapLiteralTemplatePart partValue = case partValue of
      LiteralTemplatePatternLiteral literal ->
        LiteralTemplatePatternLiteral literal
      LiteralTemplatePatternCapture capture ->
        case transform (LiteralTemplateCapture capture) of
          LiteralTemplateCapture transformed ->
            LiteralTemplatePatternCapture transformed
          StringExpressionCapture _ ->
            LiteralTemplatePatternCapture capture

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
    LiteralTemplateIdentifier body -> zipWith
      (\branch (patternValue, captures) ->
        ( declaration
        , branch
        , literalTemplateRule declaration patternValue captures
        ))
      [0 ..]
      (literalTemplatePatternBranches body)
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

literalTemplateRule
  :: DependentDeclaration Expression
  -> LiteralTemplatePattern
  -> [Maybe (SimpleIdentifierString, Expression)]
  -> SyntaxRule
literalTemplateRule declaration patternValue captures = SyntaxRule
  { syntaxIdentity = DeclaredSyntaxName
      (case literalTemplateLiterals patternValue of
        name : _ -> name
        [] -> renderSourceExpression
          (identifierHeadExpression (dependentDeclarationHead declaration)))
  , declarativeMatcherPlan = LiteralTemplateMatcher patternValue
  , syntaxSemantics = DependentSyntax (DependentSyntaxRule
      captures
      (dependentDeclarationImplementation declaration)
      (DependentSyntaxLookup (literalTemplateInvocation patternValue)))
  }
  where
    identifierHeadExpression headValue = case headValue of
      IdentifierExpressionBody body -> IdentifierExpression body
      LiteralTemplateIdentifier body -> LiteralTemplateExpression body

literalTemplateLiterals :: LiteralTemplatePattern -> [String]
literalTemplateLiterals (LiteralTemplatePattern parts) =
  [ literalTemplateLiteralText literal
  | LiteralTemplatePatternLiteral literal <- parts
  ]

literalTemplateLiteralText :: LiteralTemplateLiteral -> String
literalTemplateLiteralText literal = case literal of
  IdentifierTemplateLiteral (SimpleIdentifierString text) -> text
  SymbolTemplateLiteral (SymbolLiteral text) -> text

literalTemplateInvocation
  :: LiteralTemplatePattern
  -> [StringTemplateInterpolation Expression]
literalTemplateInvocation (LiteralTemplatePattern parts) = map invocation parts
  where
    invocation partValue = case partValue of
      LiteralTemplatePatternLiteral literal -> StringTemplateInterpolation
        (AsciiStringLiteral (literalTemplateLiteralText literal))
      LiteralTemplatePatternCapture capture ->
        StringTemplateInterpolation capture

literalTemplatePatternBranches
  :: LiteralTemplate Expression
  -> [(LiteralTemplatePattern, [Maybe (SimpleIdentifierString, Expression)])]
literalTemplatePatternBranches template =
  [ (LiteralTemplatePattern patterns, captures)
  | (patterns, captures) <- compileTemplate template
  , not (null patterns)
  ]
  where
    compileTemplate (LiteralTemplate body) =
      compileComposition compileSequence body

    compileSequence (LiteralTemplateSequence parts) =
      foldl combine [([], [])]
        (map (compileComposition compileAtom) (toList parts))

    compileAtom atom = case atom of
      LiteralTemplateLiteralAtom literal ->
        [([LiteralTemplatePatternLiteral literal], [])]
      LiteralTemplateCaptureAtom expression ->
        let (_, name) = captureDescriptor expression
        in [([LiteralTemplatePatternCapture expression], [name])]
      LiteralTemplateGroupAtom group -> compileTemplate group

    compileComposition compileLeaf composition = case composition of
      IdentifierComposition value -> compileLeaf value
      EitherExpression left right ->
        compileComposition compileLeaf left
          <> compileComposition compileLeaf right
      OptionalExpression present ->
        compileComposition compileLeaf present <> [([], [])]

    combine prefixes suffixes =
      [ (prefixPatterns <> suffixPatterns, prefixCaptures <> suffixCaptures)
      | (prefixPatterns, prefixCaptures) <- prefixes
      , (suffixPatterns, suffixCaptures) <- suffixes
      ]

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
