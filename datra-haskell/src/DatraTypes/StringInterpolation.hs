{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..)
  , DeclarativeMatcherPlan (..)
  , IdentifierApplicationPattern (..), LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , DeclarativeCapture (..)
  , DependentSyntaxRule (..)
  , SyntaxRuleSemantics (..), DependentSyntaxInvocation (..)
  , StringInterpolationTemplate, StringTemplateInterpolation (..)
  , StringExpression (..)
  , TemplateSelection (..)
  , declarationRules, declarationRuleBranches
  , identifierExpressionBranches, identifierExpressionMatchingBranches
  , syntaxRuleCaptures, mapSyntaxRuleCaptures
  , literalExpressionPattern
  , identifierApplicationRule
  , syntaxApplicationImplementation
  , syntaxDependentRule, syntaxRuleAdapter
  , expandSyntax
  , declarationLiterals
  ) where
import DatraLanguage.DependentDeclaration (dependentDeclaration)
import DatraTypes.Lookup (lookupValueFieldPosition)
import DatraLanguage.AST
import DatraLanguage.ConcreteSyntax (sourceSpace)
import StringExpression
  ( StringExpression (..)
  , StringInterpolationTemplate
  , TemplateSelection (..)
  )
import Data.Foldable (toList)
import StringInterpolation.Exact (matchesExactSkeleton)

data DeclarativeMatcherPlan
  = IdentifierApplicationMatcher IdentifierApplicationPattern
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

newtype DeclarativeCapture
  = StringExpressionCapture (StringExpression Expression)
  deriving (Eq, Show)

data SyntaxRule = SyntaxRule
  { declarativeMatcherPlan :: DeclarativeMatcherPlan
  , syntaxSemantics :: SyntaxRuleSemantics
  } deriving (Eq,Show)

syntaxRuleCaptures :: SyntaxRule -> [DeclarativeCapture]
syntaxRuleCaptures rule = case declarativeMatcherPlan rule of
  IdentifierApplicationMatcher patternValue ->
    [StringExpressionCapture (identifierApplicationOperand patternValue)]
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

data SyntaxRuleSemantics
  = SyntaxAdapter Expression
  | SyntaxApplication Expression Expression
  | DependentSyntax DependentSyntaxRule
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

syntaxRuleAdapter :: SyntaxRule -> Maybe Expression
syntaxRuleAdapter rule = case syntaxSemantics rule of
  SyntaxAdapter adapter -> Just adapter
  SyntaxApplication _ implementation -> Just implementation
  DependentSyntax dependent -> Just
    (dependentSyntaxImplementation dependent)

syntaxApplicationImplementation :: SyntaxRule -> Maybe Expression
syntaxApplicationImplementation rule = case syntaxSemantics rule of
  SyntaxApplication _ implementation -> Just implementation
  _ -> Nothing

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
  case literalIdentifierName (dependentDeclarationHead declaration) of
    Just name ->
      [(declaration, 0, identifierDeclarationRule declaration name)]
    Nothing -> zipWith
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

dependentDeclarationSyntaxAlternatives
  :: DependentDeclaration Expression
  -> [[StringTemplateInterpolation Expression]]
dependentDeclarationSyntaxAlternatives declaration = case
    dependentDeclarationHead declaration of
  identifier -> identifierExpressionBranches identifier

identifierExpressionBranches
  :: IdentifierExpression Expression
  -> [[StringTemplateInterpolation Expression]]
identifierExpressionBranches identifier = case identifier of
  IdentifierExpressionBody body -> identifierBranches body
  where
    identifierBranches (AsciiStringLiteral name) =
      [[stringLiteral name]]
    identifierBranches (AtlasMap members) = identifierSequence members
    identifierBranches (MapSequence members) = identifierSequence members
    identifierBranches (EitherType left right) =
      identifierBranches left <> identifierBranches right
    identifierBranches (OptionalType present) =
      identifierBranches present <> [[]]
    identifierBranches (StringTemplate parts) = [parts]
    identifierBranches identifier@(IdentifierExpression expressionValue) =
      case expressionValue of
        AsciiStringLiteral literal -> [[stringLiteral literal]]
        _ -> [[StringTemplateInterpolation identifier]]
    identifierBranches expressionValue =
      [[StringTemplateInterpolation expressionValue]]

    identifierSequence = foldl combine [[]] . map identifierBranches
    combine prefixes suffixes =
      [ join prefix suffix
      | prefix <- prefixes
      , suffix <- suffixes
      ]
    join [] suffix = suffix
    join prefix [] = prefix
    join prefix suffix =
      prefix <> [stringLiteral sourceSpace] <> suffix
    stringLiteral = StringTemplateInterpolation . AsciiStringLiteral

-- | Retain exactly the alternatives whose literal components can consume the
-- requested identifier. Interpolations remain unevaluated wildcards here;
-- typed capture evaluation belongs to the later exact-selection phase.
identifierExpressionMatchingBranches
  :: IdentifierExpression Expression
  -> String
  -> [[StringTemplateInterpolation Expression]]
identifierExpressionMatchingBranches identifier requested =
  filter (\branch -> matchesExactSkeleton view branch requested)
    (identifierExpressionBranches identifier)
  where
    view (StringTemplateInterpolation expressionValue) =
      case expressionValue of
        AsciiStringLiteral literal -> Right literal
        capture -> Left capture

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
  where
    captures = templateSelectionCaptures selection
    suppliedInput = case captures of
      [] -> AtlasMap []
      [value] -> value
      values -> AtlasMap values
    -- Function preparation overloads this supplied tail onto the declared
    -- domain. Empty, singleton, and multi-capture syntax therefore follows the
    -- same call path as an ordinary partial argumentative map.

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
  MapAccess
    (MapAccess
      (Lookup operand)
      (EllipsisNatural 0))
    (EllipsisNatural lookupValueFieldPosition)

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
      , Just (SimpleIdentifierString name) <-
          literalIdentifierName (dependentDeclarationHead semantic)
      , name == typeName = literals
          (dependentDeclarationImplementation semantic)
    declaration _ = []
    literals (AsciiStringLiteral text) = [text]
    literals (EitherType a b) = literals a <> literals b
    literals _ = []
