{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..)
  , SyntaxRuleMode (..)
  , DeclarativeMatcherPlan (..)
  , IdentifierApplicationPattern (..), LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , DeclarativeCapture (..)
  , StringInterpolationTemplate, StringTemplateInterpolation (..)
  , StringExpression (..)
  , TemplateSelection (..)
  , declarationRules, declarationRuleBranches
  , identifierExpressionBranches, identifierExpressionMatchingBranches
  , syntaxRuleCaptures, mapSyntaxRuleCaptures
  , literalExpressionPattern
  , identifierApplicationRule
  , declarationLiterals
  ) where
import DatraLanguage.DependentDeclaration (dependentDeclaration)
import DatraLanguage.AST
import DatraLanguage.ConcreteSyntax (sourceSpace)
import StringExpression
  ( StringExpression (..)
  , StringInterpolationTemplate
  , TemplateSelection (..)
  )
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
  , syntaxRuleAdapter :: Expression
  , syntaxRuleDomain :: Expression
  , syntaxRuleCodomain :: Expression
  , syntaxRuleMode :: SyntaxRuleMode
  } deriving (Eq,Show)

data SyntaxRuleMode
  = ExpressionMode
  | FunctionMode
  deriving (Eq, Show)

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
    (dependentDeclarationImplementation declaration)

identifierApplicationRule
  :: SimpleIdentifierString
  -> Expression
  -> SyntaxRule
identifierApplicationRule literalHead implementation = SyntaxRule
  { declarativeMatcherPlan = IdentifierApplicationMatcher
      (IdentifierApplicationPattern
        (IdentifierReference literalHead)
        (ExpressionString (AtlasMap [])))
  , syntaxRuleAdapter = adapter
  , syntaxRuleDomain = domain
  , syntaxRuleCodomain = codomain
  , syntaxRuleMode = mode
  }
  where
    (adapter, domain, codomain, mode) = ruleContract (AtlasMap []) implementation

directTemplateRule
  :: DependentDeclaration Expression
  -> [StringTemplateInterpolation Expression]
  -> SyntaxRule
directTemplateRule declaration parts =
  SyntaxRule
    { declarativeMatcherPlan =
        LiteralExpressionMatcher (literalExpressionPattern template)
    , syntaxRuleAdapter = adapter
    , syntaxRuleDomain = domain
    , syntaxRuleCodomain = codomain
    , syntaxRuleMode = mode
    }
  where
    (template, captures) = compileDependentDeclarationTemplate parts
    implementation = dependentDeclarationImplementation declaration
    fallbackDomain = captureDomain captures
    (adapter, domain, codomain, mode) = ruleContract
      fallbackDomain implementation

captureDomain
  :: [Maybe (SimpleIdentifierString, Expression)]
  -> Expression
captureDomain captures = case map capture captures of
  [] -> AtlasMap []
  [single] -> single
  members -> AtlasMap members
  where
    capture Nothing = AnyType
    capture (Just (name, target)) = DependentArgument
      (literalIdentifierExpression name) (Just target)

ruleContract
  :: Expression
  -> Expression
  -> (Expression, Expression, Expression, SyntaxRuleMode)
ruleContract fallbackDomain implementation = case implementation of
  FunctionApplication signature adapter
    | Just (domain, codomain) <- functionContract signature ->
        (adapter, domain, codomain, FunctionMode)
  MapSpecification adapter signature
    | Just (domain, codomain) <- functionContract signature ->
        (adapter, domain, codomain, FunctionMode)
  _ -> (implementation, fallbackDomain, implementation, ExpressionMode)
  where
    functionContract value = case value of
      FunctionTypeExpression _ domain codomain -> Just (domain, codomain)
      SyntaxBoundary inner -> functionContract inner
      _ -> Nothing

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
