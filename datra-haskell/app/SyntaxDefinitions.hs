{-# LANGUAGE LambdaCase #-}

-- | Declarative AST templates. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), DependentSyntaxRule (..)
  , SyntaxRuleSemantics (..), DependentSyntaxInvocation (..)
  , SyntaxTemplate (..), SyntaxPiece (..), SyntaxHoleKind (..)
  , TemplateSelection (..)
  , SyntaxTemplateCompilationFailure (..)
  , declarationRules, compileSyntaxTemplatesFromExpression
  , contextualSyntaxRulesFor
  , syntaxTemplateFromPattern, syntaxTemplateLiteralPrefix
  , syntaxDependentRule, syntaxRuleAdapter
  , expandSyntax
  , declarationLiterals, absorbFunSequence
  , normalizeSyntaxExpansion
  ) where
import DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , dependentDeclaration
  )
import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , mapSyntaxHoleKind
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  , literalSyntaxTemplate
  , renderSyntaxTemplate
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxTemplateAdmissibilityFailure )
import DatraLanguage.AST.Source (renderSourceExpression)
import SyntaxTemplateAdmissibility (validateSyntaxTemplate)

data SyntaxRule = SyntaxRule
  { syntaxName :: String, syntaxTemplate :: SyntaxTemplate Expression
  , syntaxSemantics :: SyntaxRuleSemantics
  } deriving (Eq,Show)

data SyntaxRuleSemantics
  = SyntaxAdapter Expression
  | DependentSyntax DependentSyntaxRule
  deriving (Eq, Show)

data DependentSyntaxRule = DependentSyntaxRule
  { dependentSyntaxCaptures
      :: [Maybe (IdentifierString, Expression)]
  , dependentSyntaxImplementation :: Expression
  , dependentSyntaxInvocation :: DependentSyntaxInvocation
  } deriving (Eq, Show)

data DependentSyntaxInvocation
  = DependentSyntaxLookup [StringTemplatePart Expression]
  | DependentSyntaxAdapter Expression
  deriving (Eq, Show)

syntaxDependentRule :: SyntaxRule -> Maybe DependentSyntaxRule
syntaxDependentRule rule = case syntaxSemantics rule of
  SyntaxAdapter {} -> Nothing
  DependentSyntax dependent -> Just dependent

syntaxRuleAdapter :: SyntaxRule -> Maybe Expression
syntaxRuleAdapter rule = case syntaxSemantics rule of
  SyntaxAdapter adapter -> Just adapter
  DependentSyntax dependent -> case dependentSyntaxInvocation dependent of
    DependentSyntaxLookup {} -> Nothing
    DependentSyntaxAdapter adapter -> Just adapter

data SyntaxTemplateCompilationFailure
  = ExpectedSyntaxTemplateOperand
  | InadmissibleSyntaxTemplate
      String
      SyntaxTemplateAdmissibilityFailure
  deriving (Eq, Show)

-- | Contextual bindings are supplied by their enclosing evaluator scopes,
-- not by Std. These zero-hole templates are ordinary syntax-function rules:
-- each surface word omits the argument whose domain has depth @0@ as its
-- default.
contextualSyntaxRulesFor :: [String] -> [SyntaxRule]
contextualSyntaxRulesFor = map rule
  where
    rule surface = SyntaxRule
      { syntaxName = "_" <> surface
      , syntaxTemplate = syntaxTemplateFromPattern surface
      , syntaxSemantics = SyntaxAdapter callable
      }
      where
        callable = IdentifierReference
          (IdentifierString ("_" <> surface))

declarationRules :: Expression -> [SyntaxRule]
declarationRules expressionValue =
  maybe [] dependentDeclarationRules (dependentDeclaration expressionValue)

dependentDeclarationRules :: DependentDeclaration -> [SyntaxRule]
dependentDeclarationRules declaration =
  directTemplateRule declaration <>
    compatibilityRules
      (renderSourceExpression
        (StringTemplate (dependentDeclarationParts declaration)))
      declaration

directTemplateRule :: DependentDeclaration -> [SyntaxRule]
directTemplateRule declaration =
  case compileDependentDeclarationTemplate
      (dependentDeclarationParts declaration) of
    Left _ -> []
    Right (template, captures) ->
      [ SyntaxRule
          { syntaxName = renderSourceExpression
              (StringTemplate (dependentDeclarationParts declaration))
          , syntaxTemplate = template
          , syntaxSemantics = DependentSyntax (DependentSyntaxRule
              captures
              (dependentDeclarationImplementation declaration)
              (DependentSyntaxLookup
                (dependentDeclarationParts declaration)))
          }
      ]

-- The old @%@ form is now only a compatibility frontend. Strip the syntax
-- decoration from its callable and express each pattern as the same
-- capture-to-@it@ declaration used by a string-template declaration.
compatibilityRules :: String -> DependentDeclaration -> [SyntaxRule]
compatibilityRules name declaration =
  collect (dependentDeclarationImplementation declaration)
  where
    collect (EitherType left right) = collect left <> collect right
    collect (In contextual value) = map (scopeRule contextual) (collect value)
    collect (MapSpecification body (SyntaxType templates signature)) =
      rules templates body (MapSpecification body signature)
    collect (SyntaxType templates (MapSpecification body signature)) =
      rules templates body (MapSpecification body signature)
    collect (SyntaxType templates (FunctionApplication signature body)) =
      rules templates body (FunctionApplication signature body)
    collect (FunctionApplication (SyntaxType templates signature) body) =
      rules templates body (FunctionApplication signature body)
    collect _ = []
    scopeRule contextual rule = rule
      { syntaxTemplate = SyntaxTemplate
          [ case piece of
              SyntaxLiteral {} -> piece
              SyntaxHole kind -> SyntaxHole
                (mapSyntaxHoleKind (In contextual) kind)
          | piece <- syntaxTemplatePieces (syntaxTemplate rule)
          ]
      , syntaxSemantics = case syntaxSemantics rule of
          SyntaxAdapter adapter -> SyntaxAdapter (In contextual adapter)
          DependentSyntax dependent ->
            DependentSyntax (scopeDependentRule dependent)
      }
      where
        -- The declaration context closes over the callable. The capture-side
        -- @it@ remains supplied by the dependent declaration expansion.
        scopeDependent (FunctionApplication callable supplied) =
          FunctionApplication (In contextual callable) supplied
        scopeDependent implementation = In contextual implementation
        scopeDependentRule dependent = dependent
          { dependentSyntaxImplementation = scopeDependent
              (dependentSyntaxImplementation dependent)
          , dependentSyntaxInvocation = case
                dependentSyntaxInvocation dependent of
              DependentSyntaxLookup parts -> DependentSyntaxLookup parts
              DependentSyntaxAdapter adapter ->
                DependentSyntaxAdapter (In contextual adapter)
          }
    rules templates _body callable =
      [ SyntaxRule
          { syntaxName = name
          , syntaxTemplate = template
          , syntaxSemantics = DependentSyntax (DependentSyntaxRule
              [ Nothing
              | SyntaxHole {} <- syntaxTemplatePieces template
              ]
              (FunctionApplication callable
                (IdentifierReference (IdentifierString "it")))
              (DependentSyntaxAdapter _body))
          }
      | template <- either (const []) id
          (compileSyntaxTemplatesFromExpression templates)
      ]

compileDependentDeclarationTemplate
  :: [StringTemplatePart Expression]
  -> Either SyntaxTemplateCompilationFailure
      ( SyntaxTemplate Expression
      , [Maybe (IdentifierString, Expression)]
      )
compileDependentDeclarationTemplate parts = do
  let (pieces, captures) = foldMap compilePart parts
      template = SyntaxTemplate pieces
  case validateSyntaxTemplate template of
    Left failure -> Left (InadmissibleSyntaxTemplate
      (renderSyntaxTemplate renderSourceExpression template)
      failure)
    Right () -> Right (template, captures)
  where
    compilePart (StringTemplateLiteral literal) =
      (syntaxTemplatePieces (syntaxTemplateFromPattern literal), [])
    compilePart (StringTemplateInterpolation expressionValue) =
      let (target, name) = capture expressionValue
      in ([SyntaxHole (ValueSyntaxHole target)], [name])
    capture (SyntaxBoundary inner) = capture inner
    capture (IdentifierOperation name annotation Nothing) =
      (annotation, Just (name, annotation))
    capture value = (value, Nothing)

-- | The left operand of @%@ is either one string template or an inhabited
-- compile-time total map of string templates. Rules must be available before
-- evaluation, so every map member must be explicit at declaration time.
compileSyntaxTemplatesFromExpression
  :: Expression
  -> Either SyntaxTemplateCompilationFailure [SyntaxTemplate Expression]
compileSyntaxTemplatesFromExpression templates = do
  compiled <- maybe
    (Left ExpectedSyntaxTemplateOperand)
    Right
    (templateValues templates)
  _ <- traverse validate compiled
  pure compiled
  where
    validate template = case validateSyntaxTemplate template of
      Left failure -> Left (InadmissibleSyntaxTemplate
        (renderSyntaxTemplate renderSourceExpression template)
        failure)
      Right () -> Right ()
    templateValues value@AsciiStringLiteral {} =
      (: []) <$> templateValue value
    templateValues value@StringTemplate {} =
      (: []) <$> templateValue value
    templateValues (SyntaxBoundary value) = templateValues value
    templateValues (AtlasMap values)
      | not (null values) = traverse templateValue values
    templateValues _ = Nothing
    templateValue (AsciiStringLiteral patternText) =
      Just (syntaxTemplateFromPattern patternText)
    templateValue (StringTemplate parts) =
      SyntaxTemplate . concat <$> traverse templatePart parts
    templateValue _ = Nothing
    templatePart (StringTemplateLiteral literal) =
      Just (syntaxTemplatePieces (syntaxTemplateFromPattern literal))
    templatePart (StringTemplateInterpolation value) =
      Just [SyntaxHole (ValueSyntaxHole value)]

syntaxTemplateFromPattern :: String -> SyntaxTemplate Expression
syntaxTemplateFromPattern = literalSyntaxTemplate

syntaxTemplateLiteralPrefix :: SyntaxRule -> [String]
syntaxTemplateLiteralPrefix = foldr prefix []
  . syntaxTemplatePieces . syntaxTemplate
  where
    prefix (SyntaxLiteral literal) rest = literal : rest
    prefix (SyntaxHole _) _ = []

-- | Expand captures selected by one declared syntax template.
expandSyntax
  :: SyntaxRule
  -> TemplateSelection Expression Expression
  -> Expression
expandSyntax rule selection =
  case syntaxSemantics rule of
    DependentSyntax dependent -> case dependentSyntaxInvocation dependent of
      DependentSyntaxLookup parts -> dependentLookup parts captures
      DependentSyntaxAdapter adapter ->
        FunctionApplication adapter suppliedInput
    SyntaxAdapter adapter -> FunctionApplication adapter suppliedInput
  where
    captures = templateSelectionCaptures selection
    suppliedInput = case captures of
      [] -> AtlasMap []
      [value] -> value
      values -> AtlasMap values
    dependentLookup parts values =
      MapAccess
        (MapAccess
          (Lookup (StringTemplate (substitute parts values)))
          (EllipsisNatural 0))
        (EllipsisNatural 1)
    substitute [] _ = []
    substitute (StringTemplateLiteral literal : parts) values =
      StringTemplateLiteral literal : substitute parts values
    substitute (StringTemplateInterpolation _ : parts) (value : values) =
      StringTemplateInterpolation value : substitute parts values
    substitute (interpolation@StringTemplateInterpolation {} : parts) [] =
      interpolation : substitute parts []
    -- Function preparation overloads this supplied tail onto the declared
    -- domain. Empty, singleton, and multi-capture syntax therefore follows the
    -- same call path as an ordinary partial argument map.

-- A named subexpression in a condition becomes a condition-local declaration
-- when its name is used elsewhere in that condition or in either branch.
-- Boolean operators lower to nested conditionals only when such a binding is
-- present. This preserves short-circuit paths: a binding in the right side of
-- @or@ is not evaluated when the left side succeeds, while it remains visible
-- wherever that right side was evaluated. Unreferenced named values retain
-- their ordinary value semantics (for example, @Just : 1@ remains a tag).
conditionalWithBindings
  :: Expression
  -> Expression
  -> Expression
  -> Expression
conditionalWithBindings rawCondition yes no
  | null (selectedConditionBindings condition yes no) =
      Conditional condition yes no
  | otherwise = lower condition yes no
  where
    condition = normalizeExpression rawCondition
    lower (BooleanOr left right) consequent alternative =
      lower left consequent (lower right consequent alternative)
    lower (BooleanAnd left right) consequent alternative =
      lower left (lower right consequent alternative) alternative
    lower (BooleanNot operand) consequent alternative =
      lower operand alternative consequent
    lower operand consequent alternative =
      lowerConditionAtom operand consequent alternative

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
      [ IdentifierOperation name value (Just value)
      | (name, original) <- selected
      , let value = rewrite original
      ]
    rewrittenCondition = rewrite condition
    rewrite expressionValue = case expressionValue of
      IdentifierOperation name _ Nothing
        | name `elem` selectedNames -> IdentifierReference name
      _ -> mapExpressionChildren rewrite expressionValue

selectedConditionBindings
  :: Expression
  -> Expression
  -> Expression
  -> [(IdentifierString, Expression)]
selectedConditionBindings condition yes no =
  [ (name, value)
  | (name@(IdentifierString text), value) <- candidates
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
  -> [(IdentifierString, Expression)]
conditionBindingCandidates expressionValue =
  concatMap conditionBindingCandidates (expressionChildren expressionValue)
    <> case expressionValue of
      IdentifierOperation name value Nothing -> [(name, value)]
      _ -> []

identifierReferences :: Expression -> [String]
identifierReferences expressionValue = case expressionValue of
  IdentifierReference (IdentifierString name) -> [name]
  _ -> concatMap identifierReferences (expressionChildren expressionValue)

-- Within @fun@, the canonical recursive-list spelling associates a following
-- sequence with the nonempty branch: @() | T; this@ means
-- @() | (T; this)@.  This keeps @;@ available for nested element types.
absorbFunSequence :: Expression -> Expression
absorbFunSequence expressionValue =
  case expressionValue of
    MapSequence (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , isContextualAccessOf (IdentifierString "_this") (last remaining) ->
          EitherType (AtlasMap []) (MapSequence (headValue : remaining))
    AtlasMap (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , isContextualAccessOf (IdentifierString "_this") (last remaining) ->
          EitherType (AtlasMap []) (AtlasMap (headValue : remaining))
    _ -> expressionValue

-- Literal alternatives of a named type can be spelled as keywords in an AST
-- pattern, while ordinary application keeps their $identifier value spelling.
declarationLiterals :: [Expression] -> String -> [String]
declarationLiterals declarations typeName = concatMap declaration declarations
  where
    declaration (Let value) = declaration value
    declaration (Val value) = declaration value
    declaration (IdentifierOperation (IdentifierString name) annotation given)
      | name == typeName = literals (maybe annotation id given)
    declaration _ = []
    literals (AsciiStringLiteral text) = [text]
    literals (EitherType a b) = literals a <> literals b
    literals _ = []
