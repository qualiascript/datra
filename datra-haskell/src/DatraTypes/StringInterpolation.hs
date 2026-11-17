{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..)
  , DeclarativeMatcherPlan (..)
  , IdentifierApplicationPattern (..), LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , DeclarativeCapture (..)
  , LiteralTemplatePattern (..), LiteralTemplatePatternPart (..)
  , DependentSyntaxRule (..)
  , SyntaxRuleSemantics (..), DependentSyntaxInvocation (..)
  , StringInterpolationTemplate, StringTemplateInterpolation (..)
  , StringExpression (..)
  , TemplateSelection (..)
  , declarationRules, declarationRuleBranches
  , syntaxRuleCaptures, mapSyntaxRuleCaptures
  , literalExpressionPattern
  , identifierApplicationRule
  , commentSyntaxRule
  , syntaxWhitespaceSource
  , horizontalSyntaxWhitespace
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
  , isSourcePresentationCharacter
  )
import Data.Foldable (toList)

data DeclarativeMatcherPlan
  = IdentifierApplicationMatcher IdentifierApplicationPattern
  | LiteralTemplateMatcher LiteralTemplatePattern
  | LiteralExpressionMatcher
      (LiteralExpressionPattern (StringExpression Expression))
  deriving (Eq, Show)

data IdentifierApplicationPattern = IdentifierApplicationPattern
  { identifierApplicationHead :: Expression
  , identifierApplicationOperand :: StringExpression Expression
  }
  deriving (Eq, Show)

newtype LiteralExpressionPattern capture = LiteralExpressionPattern
  { literalExpressionPatternParts :: [LiteralExpressionPatternPart capture]
  }
  deriving (Eq, Show)

data LiteralExpressionPatternPart capture
  = LiteralExpressionPatternLiteral String
  | LiteralExpressionPatternCapture capture
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

data SyntaxRule = SyntaxRule
  { declarativeMatcherPlan :: DeclarativeMatcherPlan
  , syntaxSemantics :: SyntaxRuleSemantics
  } deriving (Eq,Show)

syntaxRuleCaptures :: SyntaxRule -> [DeclarativeCapture]
syntaxRuleCaptures rule = case declarativeMatcherPlan rule of
  IdentifierApplicationMatcher patternValue ->
    [StringExpressionCapture (identifierApplicationOperand patternValue)]
  LiteralTemplateMatcher (LiteralTemplatePattern parts) ->
    [ LiteralTemplateCapture capture
    | LiteralTemplatePatternCapture capture <- parts
    ]
  LiteralExpressionMatcher (LiteralExpressionPattern parts) ->
    [ StringExpressionCapture capture
    | LiteralExpressionPatternCapture capture <- parts
    ]

literalExpressionPattern
  :: StringInterpolationTemplate Expression
  -> LiteralExpressionPattern (StringExpression Expression)
literalExpressionPattern = LiteralExpressionPattern . map part
  where
    part (StringTemplateInterpolation expressionValue) =
      case expressionValue of
        LiteralString literal -> LiteralExpressionPatternLiteral literal
        capture -> LiteralExpressionPatternCapture capture

mapSyntaxRuleCaptures
  :: (DeclarativeCapture -> DeclarativeCapture)
  -> SyntaxRule
  -> SyntaxRule
mapSyntaxRuleCaptures transform rule = rule
  { declarativeMatcherPlan = case declarativeMatcherPlan rule of
      IdentifierApplicationMatcher patternValue -> IdentifierApplicationMatcher
        patternValue
          { identifierApplicationOperand =
              mapStringCapture (identifierApplicationOperand patternValue)
          }
      LiteralTemplateMatcher (LiteralTemplatePattern parts) ->
        LiteralTemplateMatcher
          (LiteralTemplatePattern (map mapLiteralTemplatePart parts))
      LiteralExpressionMatcher (LiteralExpressionPattern parts) ->
        LiteralExpressionMatcher
          (LiteralExpressionPattern (map mapLiteralExpressionPart parts))
  }
  where
    mapLiteralExpressionPart partValue = case partValue of
      LiteralExpressionPatternLiteral literal ->
        LiteralExpressionPatternLiteral literal
      LiteralExpressionPatternCapture capture ->
        LiteralExpressionPatternCapture (mapStringCapture capture)
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

syntaxRuleAdapter :: SyntaxRule -> Maybe Expression
syntaxRuleAdapter rule = case syntaxSemantics rule of
  SyntaxAdapter adapter -> Just adapter
  SyntaxApplication _ implementation -> Just implementation
  DependentSyntax dependent -> Just
    (dependentSyntaxImplementation dependent)
  SyntaxDiscard -> Nothing

syntaxApplicationImplementation :: SyntaxRule -> Maybe Expression
syntaxApplicationImplementation rule = case syntaxSemantics rule of
  SyntaxApplication _ implementation -> Just implementation
  _ -> Nothing

-- | The first declaration in every syntax environment. Its operand has
-- already been delimited by the concrete parser, but remains ordinary syntax
-- data until this rule discards it.
commentSyntaxRule :: SyntaxRule
commentSyntaxRule = SyntaxRule
  { declarativeMatcherPlan = IdentifierApplicationMatcher
      (IdentifierApplicationPattern
        (UnresolvedSyntaxLiteral [commentCharacter])
        (ExpressionString (AtlasMap [])))
  , syntaxSemantics = SyntaxDiscard
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
      [(declaration, 0, identifierDeclarationRule declaration name)]
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

identifierDeclarationRule
  :: DependentDeclaration Expression
  -> SimpleIdentifierString
  -> SyntaxRule
identifierDeclarationRule declaration (SimpleIdentifierString text) =
  identifierApplicationRule
    (SimpleIdentifierString text)
    (dependentLookup [literalInterpolation text] [])
    (dependentDeclarationImplementation declaration)

identifierApplicationRule
  :: SimpleIdentifierString
  -> Expression
  -> Expression
  -> SyntaxRule
identifierApplicationRule literalHead callable implementation = SyntaxRule
  { declarativeMatcherPlan = IdentifierApplicationMatcher
      (IdentifierApplicationPattern
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
    { declarativeMatcherPlan =
        LiteralExpressionMatcher (literalExpressionPattern template)
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
  { declarativeMatcherPlan = LiteralTemplateMatcher patternValue
  , syntaxSemantics = DependentSyntax (DependentSyntaxRule
      captures
      (dependentDeclarationImplementation declaration)
      (DependentSyntaxLookup (literalTemplateInvocation patternValue)))
  }
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
  where
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
