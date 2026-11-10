{-# LANGUAGE LambdaCase #-}

-- | Declarative string interpolations. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module StringInterpolation
  ( SyntaxRule (..), DependentSyntaxRule (..)
  , SyntaxRuleSemantics (..), DependentSyntaxInvocation (..)
  , StringInterpolationTemplate, StringTemplatePart (..), StringExpression (..)
  , TemplateSelection (..)
  , StringInterpolationCompilationFailure (..)
  , declarationRules, declarationRuleBranches, declarationRuleFailures
  , stringInterpolationTemplateFromPattern, stringInterpolationLiteralPrefix
  , syntaxApplicationRule
  , syntaxApplicationImplementation
  , syntaxDependentRule, syntaxRuleAdapter
  , expandSyntax
  , declarationLiterals
  , normalizeSyntaxExpansion
  ) where
import DatraLanguage.DependentDeclaration
  ( dependentDeclaration
  , dependentDeclarationTemplateBranches
  )
import DatraLanguage.AST
import DatraLanguage.StringExpression
  ( StringExpression (..)
  , StringInterpolationTemplate
  , TemplateSelection (..)
  , literalStringInterpolationTemplate
  , renderStringInterpolationTemplate
  )
import DatraLanguage.Diagnostics.Application
  ( StringInterpolationAdmissibilityFailure )
import DatraLanguage.AST.Source (renderSourceExpression)
import Data.Either (partitionEithers)
import StringInterpolation.Admissibility (validateStringTemplate)
import StringInterpolation.Projection (StringInterpolationParser)

data SyntaxRule = SyntaxRule
  { syntaxName :: String
  , stringInterpolationTemplate :: StringInterpolationTemplate Expression
  , syntaxSemantics :: SyntaxRuleSemantics
  } deriving (Eq,Show)

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
  = DependentSyntaxLookup [StringTemplatePart Expression]
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

data StringInterpolationCompilationFailure
  = InadmissibleStringInterpolation
      String
      StringInterpolationAdmissibilityFailure
  deriving (Eq, Show)

declarationRules :: StringInterpolationParser -> Expression -> [SyntaxRule]
declarationRules parser = map third . snd . declarationRuleResults parser
  where
    third (_, _, rule) = rule

declarationRuleBranches
  :: StringInterpolationParser
  -> Expression
  -> [(DependentDeclaration Expression, Int, SyntaxRule)]
declarationRuleBranches parser = snd . declarationRuleResults parser

declarationRuleFailures
  :: StringInterpolationParser
  -> Expression
  -> [StringInterpolationCompilationFailure]
declarationRuleFailures parser = fst . declarationRuleResults parser

declarationRuleResults
  :: StringInterpolationParser
  -> Expression
  -> ( [StringInterpolationCompilationFailure]
     , [(DependentDeclaration Expression, Int, SyntaxRule)]
     )
declarationRuleResults parser expressionValue =
  case dependentDeclaration expressionValue of
    Nothing -> ([], [])
    Just declaration -> partitionEithers
      (dependentDeclarationRuleResults parser declaration)

dependentDeclarationRuleResults
  :: StringInterpolationParser
  -> DependentDeclaration Expression
  -> [Either StringInterpolationCompilationFailure
      (DependentDeclaration Expression, Int, SyntaxRule)]
dependentDeclarationRuleResults parser declaration =
  case dependentDeclarationHead declaration of
    IdentifierExpressionBody (IdentifierReference name) ->
      [Right (declaration, 0, simpleApplicationRule declaration name)]
    _ -> zipWith
      (\branch parts ->
        (declaration, branch,) <$>
          directTemplateRule parser declaration parts)
      [0 ..]
      (dependentDeclarationSyntaxAlternatives declaration)

simpleApplicationRule
  :: DependentDeclaration Expression
  -> SimpleIdentifierString
  -> SyntaxRule
simpleApplicationRule declaration (SimpleIdentifierString text) =
  syntaxApplicationRule
    text
    (stringInterpolationTemplateFromPattern text)
    (dependentLookup [StringTemplateLiteral text] [])
    (dependentDeclarationImplementation declaration)

syntaxApplicationRule
  :: String
  -> StringInterpolationTemplate Expression
  -> Expression
  -> Expression
  -> SyntaxRule
syntaxApplicationRule name template callable implementation = SyntaxRule
  { syntaxName = name
  , stringInterpolationTemplate = template <>
      [StringTemplateInterpolation (ExpressionString
        (IdentifierReference (SimpleIdentifierString "_Expr")))]
  , syntaxSemantics = SyntaxApplication callable implementation
  }

directTemplateRule
  :: StringInterpolationParser
  -> DependentDeclaration Expression
  -> [StringTemplatePart Expression]
  -> Either StringInterpolationCompilationFailure SyntaxRule
directTemplateRule parser declaration parts = do
  (template, captures) <-
    compileDependentDeclarationTemplate parser parts
  pure SyntaxRule
    { syntaxName = case dependentDeclarationHead declaration of
        IdentifierExpressionBody
            (IdentifierReference (SimpleIdentifierString name)) -> name
        IdentifierExpressionBody (AsciiStringLiteral name) -> name
        _ -> renderSourceExpression (StringTemplate parts)
    , stringInterpolationTemplate = template
    , syntaxSemantics = DependentSyntax (DependentSyntaxRule
        captures
        (dependentDeclarationImplementation declaration)
        (DependentSyntaxLookup parts))
    }

dependentDeclarationSyntaxAlternatives
  :: DependentDeclaration Expression
  -> [[StringTemplatePart Expression]]
dependentDeclarationSyntaxAlternatives declaration =
  maybe [] id (dependentDeclarationTemplateBranches declaration)

compileDependentDeclarationTemplate
  :: StringInterpolationParser
  -> [StringTemplatePart Expression]
  -> Either StringInterpolationCompilationFailure
      ( StringInterpolationTemplate Expression
      , [Maybe (SimpleIdentifierString, Expression)]
      )
compileDependentDeclarationTemplate parser parts = do
  let (pieces, captures) = foldMap compilePart parts
      template = pieces
  case validateStringTemplate parser parts template of
    Left failure -> Left (InadmissibleStringInterpolation
      (renderStringInterpolationTemplate renderSourceExpression template)
      failure)
    Right () -> Right (template, captures)
  where
    compilePart (StringTemplateLiteral literal) =
      (stringInterpolationTemplateFromPattern literal, [])
    compilePart (StringTemplateInterpolation expressionValue) =
      let (target, name) = capture expressionValue
      in ([StringTemplateInterpolation (ValueString target)], [name])
    capture (SyntaxBoundary inner) = capture inner
    capture (DependentArgument
        (IdentifierReference name) (Just annotation)) =
      (annotation, Just (name, annotation))
    capture value = (value, Nothing)

stringInterpolationTemplateFromPattern :: String -> StringInterpolationTemplate Expression
stringInterpolationTemplateFromPattern = literalStringInterpolationTemplate

stringInterpolationLiteralPrefix :: SyntaxRule -> [String]
stringInterpolationLiteralPrefix = foldr prefix []
  . stringInterpolationTemplate
  where
    prefix (StringTemplateLiteral literal) rest = literal : rest
    prefix (StringTemplateInterpolation _) _ = []

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
  :: [StringTemplatePart Expression]
  -> [Expression]
  -> Expression
dependentLookup parts values =
  lookupExpression (StringTemplate (substituteCaptures parts values))

-- Keep the selected branch and its source captures alongside the ordinary
-- lookup query. Evaluation uses them only to preserve deferred fixed points;
-- the lookup still resolves through the normal named-map interface.
selectedDependentLookup
  :: [StringTemplatePart Expression]
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
  :: [StringTemplatePart Expression]
  -> [Expression]
  -> [StringTemplatePart Expression]
substituteCaptures [] _ = []
substituteCaptures (StringTemplateLiteral literal : remaining) arguments =
  StringTemplateLiteral literal : substituteCaptures remaining arguments
substituteCaptures (StringTemplateInterpolation _ : remaining)
    (argument : arguments) =
  StringTemplateInterpolation argument :
    substituteCaptures remaining arguments
substituteCaptures
    (interpolation@StringTemplateInterpolation {} : remaining) [] =
  interpolation : substituteCaptures remaining []

-- A named subexpression in a condition becomes a condition-local declaration
-- when its name is used elsewhere in that condition or in either branch.
-- Operator semantics belong to declared functions; this pass only localizes
-- the complete condition expression.
conditionalWithBindings
  :: Expression
  -> Expression
  -> Expression
  -> Expression
conditionalWithBindings rawCondition yes no
  | null (selectedConditionBindings condition yes no) =
      Conditional condition yes no
  | otherwise = lowerConditionAtom condition yes no
  where
    condition = normalizeExpression rawCondition

-- Syntax captures are themselves rewritten after their enclosing template is
-- expanded. Re-run the shape-dependent part of a control expansion once those
-- captures have reached their final AST form. This is an AST semantic pass,
-- independent of which declaration supplied the surface spelling.
normalizeSyntaxExpansion :: Expression -> Expression
normalizeSyntaxExpansion (Conditional condition yes no) =
  conditionalWithBindings condition yes no
normalizeSyntaxExpansion value = value

lowerConditionAtom :: Expression -> Expression -> Expression -> Expression
lowerConditionAtom condition yes no =
  case selected of
    [] -> Conditional condition yes no
    _ -> Begin declarations (Conditional rewrittenCondition yes no)
  where
    selected = selectedConditionBindings condition yes no
    selectedNames = map fst selected
    declarations =
      [ DependentDeclaration
          (IdentifierExpressionBody (IdentifierReference name))
          False False False [] value
      | (name, original) <- selected
      , let value = rewrite original
      ]
    rewrittenCondition = rewrite condition
    rewrite expressionValue = case expressionValue of
      DependentArgument (IdentifierReference name) (Just _)
        | name `elem` selectedNames -> IdentifierReference name
      _ -> mapExpressionChildren rewrite expressionValue

selectedConditionBindings
  :: Expression
  -> Expression
  -> Expression
  -> [(SimpleIdentifierString, Expression)]
selectedConditionBindings condition yes no =
  [ (name, value)
  | (name@(SimpleIdentifierString text), value) <- candidates
  , text `elem` referenced
  ]
  where
    candidates = conditionBindingCandidates condition
    referenced = identifierReferences condition
      <> identifierReferences yes
      <> identifierReferences no

-- Nested declarations are emitted before their enclosing named expression so
-- a hoisted outer value can refer to a hoisted inner value in ordinary block
-- order.
conditionBindingCandidates
  :: Expression
  -> [(SimpleIdentifierString, Expression)]
conditionBindingCandidates expressionValue =
  concatMap conditionBindingCandidates (expressionChildren expressionValue)
    <> case expressionValue of
      DependentArgument
          (IdentifierReference name) (Just value) -> [(name, value)]
      _ -> []

identifierReferences :: Expression -> [String]
identifierReferences expressionValue = case expressionValue of
  IdentifierReference (SimpleIdentifierString name) -> [name]
  _ -> concatMap identifierReferences (expressionChildren expressionValue)

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
