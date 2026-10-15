{-# LANGUAGE LambdaCase #-}

-- | Declarative AST templates. Syntax function bodies preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxTemplate (..), SyntaxPiece (..), SyntaxHoleKind (..)
  , TemplateSelection (..)
  , SyntaxTemplateCompilationFailure (..)
  , declarationRules, compileSyntaxTemplatesFromExpression
  , contextualSyntaxRulesFor
  , syntaxTemplateFromPattern, syntaxTemplateLiteralPrefix
  , expandSyntax
  , declarationLiterals, absorbFunSequence
  , normalizeSyntaxExpansion
  ) where
import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  , literalSyntaxTemplate
  , renderSyntaxTemplate
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure (..)
  , SyntaxTemplateAdmissibilityFailure
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import SyntaxTemplateAdmissibility (validateSyntaxTemplate)

data SyntaxRule = SyntaxRule
  { syntaxName :: String, syntaxTemplate :: SyntaxTemplate Expression
  , syntaxSignature :: Expression
  , syntaxRecursive :: Bool
  , syntaxModule :: Maybe String
  , syntaxImplementation :: Expression
  } deriving (Eq,Show)

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
      ("_" <> surface)
      (syntaxTemplateFromPattern surface)
      signature
      False
      Nothing
      (IdentifierReference (IdentifierString ("_" <> surface)))
    signature = FunctionType
      (EllipsisNatural 0)
      (IdentifierReference (IdentifierString "Any"))

declarationRules :: Expression -> [SyntaxRule]
declarationRules (Let value) =
  [rule { syntaxRecursive = True } | rule <- declarationRules value]
declarationRules (Val value) = declarationRules value
declarationRules optional
  | Just (operation, _) <- optionalIdentifierExpression optional =
      declarationRules operation
declarationRules (IdentifierOperation (IdentifierString name) annotation (Just implementation)) =
  collect name (if annotation == implementation then implementation else MapSpecification implementation annotation)
  where
    collect key (EitherType a b) = collect key a <> collect key b
    collect key (MapSpecification body (SyntaxType templates signature)) =
      rules key templates signature body
    collect key (SyntaxType templates (MapSpecification body signature)) =
      rules key templates signature body
    collect key (SyntaxType templates (FunctionApplication signature body)) =
      rules key templates signature body
    collect key (FunctionApplication (SyntaxType templates signature) body) =
      rules key templates signature body
    collect _ _ = []
    rules key templates signature body =
      [ SyntaxRule key template
          signature False Nothing body
      | template <- either (const []) id
          (compileSyntaxTemplatesFromExpression templates)
      ]
declarationRules _ = []

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
  -> Either SyntaxExpansionFailure Expression
expandSyntax rule selection =
  Right (FunctionApplication callable suppliedInput)
  where
    captures = templateSelectionCaptures selection
    callable = scoped (IdentifierReference (IdentifierString localName))
    localName = reverse (takeWhile (/= '.') (reverse (syntaxName rule)))
    scoped value = maybe value (`InModule` value) (syntaxModule rule)
    suppliedInput = case captures of
      [] -> AtlasMap []
      [value] -> value
      values -> AtlasMap values
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
