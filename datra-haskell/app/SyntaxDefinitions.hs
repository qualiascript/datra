{-# LANGUAGE LambdaCase #-}

-- | Declarative AST templates. External AST adapters preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxTemplate (..), SyntaxPiece (..), SyntaxHoleKind (..)
  , SyntaxTemplateCompilationFailure (..)
  , SyntaxFunctionBody, syntaxFunctionBodyForSymbol, applySyntaxFunctionBody
  , declarationRules, compileSyntaxTemplatesFromExpression
  , contextualSyntaxRules
  , syntaxTemplateFromPattern, syntaxTemplateLiteralPrefix
  , qualifySyntaxRule, expandSyntax
  , declarationLiterals, absorbFunSequence, externalSymbol
  , normalizeSyntaxExpansion
  ) where
import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , invalidSyntaxTemplateCharacter
  , literalSyntaxTemplate
  )
import IdentifierValueType (isIdentifierValue)
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure (..))

data SyntaxRule = SyntaxRule
  { syntaxName :: String, syntaxTemplate :: SyntaxTemplate Expression
  , syntaxSignature :: Expression
  , syntaxRecursive :: Bool
  , syntaxModule :: Maybe String
  , syntaxImplementation :: Expression
  } deriving (Eq,Show)

data SyntaxTemplateCompilationFailure
  = ExpectedSyntaxTemplateOperand
  | ForbiddenSyntaxTemplateCharacter Char
  deriving (Eq, Show)

-- | Contextual bindings are supplied by their enclosing evaluator scopes,
-- not by Std. These zero-hole templates are ordinary syntax-function rules:
-- each surface word applies its private contextual function to literal @0@.
contextualSyntaxRules :: [SyntaxRule]
contextualSyntaxRules = map rule
  [ ("_this", "this")
  , ("_it", "it")
  ]
  where
    rule (binding, surface) = SyntaxRule
      binding
      (syntaxTemplateFromPattern surface)
      signature
      False
      Nothing
      (IdentifierReference (IdentifierString binding))
    signature = FunctionType
      (EllipsisNatural 0)
      (External (AsciiStringLiteral "datra.Any"))

newtype SyntaxFunctionBody = SyntaxFunctionBody
  { applySyntaxFunctionBody
      :: [Expression]
      -> Either SyntaxExpansionFailure Expression
  }

syntaxFunctionBodyForSymbol :: String -> Maybe SyntaxFunctionBody
syntaxFunctionBodyForSymbol symbol = SyntaxFunctionBody <$> lookup symbol
  [ ("datra.if", \case
      [condition, yes, no] -> Right
        (Conditional condition yes no)
      captures -> invalidBody symbol captures)
  , ("datra.ifThen", \case
      [condition, yes] -> Right
        (Conditional condition yes (AtlasMap []))
      captures -> invalidBody symbol captures)
  , ("datra.begin", \case
      [entries, result] -> Right (Begin (blockEntries entries) result)
      captures -> invalidBody symbol captures)
  , ("datra.do", \case
      [entries, result] -> Right (FunctionBody (blockEntries entries) result)
      captures -> invalidBody symbol captures)
  , ("datra.let", \case
      [entry] -> Right (Let (absorbAssignedConcatenation entry))
      captures -> invalidBody symbol captures)
  , ("datra.fun", \case
      [entry] -> Right (Fun (absorbFunSequence entry))
      captures -> invalidBody symbol captures)
  , ("datra.with", \case
      [name, bound] -> dependentBinder "with" WithBinding name bound
      captures -> invalidBody symbol captures)
  , ("datra.for", \case
      [name, bound] -> dependentBinder "for" ForBinding name bound
      captures -> invalidBody symbol captures)
  , ("datra.withIn", \case
      [name, bound, body] ->
        localDependentFamily "with" WithBinding name bound body
      captures -> invalidBody symbol captures)
  , ("datra.forIn", \case
      [name, bound, body] ->
        localDependentFamily "for" ForBinding name bound body
      captures -> invalidBody symbol captures)
  , ("datra.modular", \case
      [value] -> Right (Modular value)
      captures -> invalidBody symbol captures)
  , ("datra.of", \case
      [source, target] -> Right (Subfederation source target)
      captures -> invalidBody symbol captures)
  , ("datra.and", \case
      [left, right] -> Right (BooleanAnd left right)
      captures -> invalidBody symbol captures)
  , ("datra.or", \case
      [left, right] -> Right (BooleanOr left right)
      captures -> invalidBody symbol captures)
  , ("datra.not", \case
      [value] -> Right (BooleanNot value)
      captures -> invalidBody symbol captures)
  , ("datra.assert", \case
      [condition] -> Right (Assert False condition)
      captures -> invalidBody symbol captures)
  , ("datra.assertHard", \case
      [_, condition] -> Right (Assert True condition)
      captures -> invalidBody symbol captures)
  , ("datra.import", \case
      [AsciiStringLiteral path] -> Right (Import False path)
      captures -> invalidBody symbol captures)
  , ("datra.importAll", \case
      [AsciiStringLiteral "all", AsciiStringLiteral path] ->
        Right (Import True path)
      captures -> invalidBody symbol captures)
  ]
  where
    invalidBody name _ = Left (UnknownSyntaxControlAdapter name)

blockEntries :: Expression -> [Expression]
blockEntries (AtlasMap entries) = entries
blockEntries value = [value]

dependentBinder
  :: String
  -> (IdentifierString -> Bool -> Expression -> Expression)
  -> Expression
  -> Expression
  -> Either SyntaxExpansionFailure Expression
dependentBinder name constructor binder bound =
  case binder of
    IdentifierReference identifier ->
      Right (constructor identifier False bound)
    OptionalType (IdentifierReference identifier) ->
      Right (constructor identifier True bound)
    AsciiStringLiteral identifier
      | isIdentifierValue identifier ->
          Right (constructor (IdentifierString identifier) False bound)
    OptionalType (AsciiStringLiteral identifier)
      | isIdentifierValue identifier ->
          Right (constructor (IdentifierString identifier) True bound)
    value
      | dynamicIdentifierExpression value ->
          Left (UndecidableDependentBinder name)
    _ -> Left (InvalidDependentBinder name)
  where
    dynamicIdentifierExpression value =
      case value of
        StringTemplate {} -> True
        OptionalType underlying -> dynamicIdentifierExpression underlying
        _ -> False

localDependentFamily
  :: String
  -> (IdentifierString -> Bool -> Expression -> Expression)
  -> Expression
  -> Expression
  -> Expression
  -> Either SyntaxExpansionFailure Expression
localDependentFamily name constructor binder bound body = do
  dependent <- dependentBinder name constructor binder bound
  Right (MapAccess (AtlasMap [makeOptional dependent, body])
    (EllipsisNatural 1))
  where
    makeOptional (WithBinding identifier _ value) =
      WithBinding identifier True value
    makeOptional (ForBinding identifier _ value) =
      ForBinding identifier True value
    makeOptional value = value

absorbAssignedConcatenation :: Expression -> Expression
absorbAssignedConcatenation value = case value of
  MapConcatenation
      (IdentifierOperation name annotation (Just given)) right
    | annotation == given ->
        let assignedValue = MapConcatenation given right
        in IdentifierOperation name assignedValue (Just assignedValue)
  _ -> value

declarationRules :: Expression -> [SyntaxRule]
declarationRules (Let value) =
  [rule { syntaxRecursive = True } | rule <- declarationRules value]
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
    collect _ _ = []
    rules key templates signature body =
      [ SyntaxRule key template
          signature False Nothing body
      | template <- either (const []) id
          (compileSyntaxTemplatesFromExpression templates)
      ]
declarationRules _ = []

-- | The left operand of @%%@ is either one string template or an inhabited
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
  case
      [ invalid
      | template <- compiled
      , Just invalid <- [invalidSyntaxTemplateCharacter template]
      ] of
    invalid : _ -> Left (ForbiddenSyntaxTemplateCharacter invalid)
    [] -> Right compiled
  where
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

-- | Qualify a literal-headed syntax declaration. A hole-led declaration has
-- no surface head to qualify, so exposing it through a qualified import would
-- silently duplicate its unqualified spelling (and change declaration-order
-- precedence for an accompanying @import all@).
qualifySyntaxRule :: String -> SyntaxRule -> Maybe SyntaxRule
qualifySyntaxRule namespace rule = case syntaxTemplate rule of
  SyntaxTemplate (SyntaxLiteral name : pieces) -> Just rule
    { syntaxName = qualifiedName
    , syntaxTemplate = SyntaxTemplate
        (SyntaxLiteral (namespace <> "." <> name) : pieces)
    }
  _ -> Nothing
  where
    originalName = syntaxName rule
    qualifiedName = namespace <> "." <> originalName

-- | Expand captures selected by one declared syntax template.
expandSyntax
  :: SyntaxRule
  -> [Expression]
  -> Either SyntaxExpansionFailure Expression
expandSyntax rule captures = case
    externalSymbol (syntaxImplementation rule) >>= syntaxFunctionBodyForSymbol of
  Just body -> applySyntaxFunctionBody body captures
  _ -> Right (FunctionApplication callable (applicationInput captures))
  where
    callable = scoped (IdentifierReference (IdentifierString localName))
    localName = reverse (takeWhile (/= '.') (reverse (syntaxName rule)))
    scoped value = maybe value (`InModule` value) (syntaxModule rule)
    -- A zero-hole syntax function receives the singleton value written as its
    -- domain. Thus @"this" %% (0 -> Any)@ applies its function to @0@ using
    -- the same expansion path as any other declared template.
    applicationInput [] = case syntaxSignature rule of
      FunctionType domain _ -> domain
      _ -> AtlasMap []
    applicationInput [value] = value
    applicationInput values = AtlasMap values

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
      [ IdentifierOperation name (rewrite value) Nothing
      | (name, value) <- selected
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

externalSymbol :: Expression -> Maybe String
externalSymbol (External (AsciiStringLiteral symbol)) = Just symbol
externalSymbol (External descriptor) = findSymbol descriptor
  where
    findSymbol (IdentifierOperation (IdentifierString "symbol") (AsciiStringLiteral value) _) = Just value
    findSymbol (AtlasMap members) = first (map findSymbol members)
    findSymbol (MapConcatenation left right) =
      first [findSymbol left, findSymbol right]
    findSymbol _ = Nothing
    first [] = Nothing
    first (Just value:_) = Just value
    first (_:rest) = first rest
externalSymbol _ = Nothing

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
    declaration (IdentifierOperation (IdentifierString name) annotation given)
      | name == typeName = literals (maybe annotation id given)
    declaration _ = []
    literals (AsciiStringLiteral text) = [text]
    literals (EitherType a b) = literals a <> literals b
    literals _ = []
