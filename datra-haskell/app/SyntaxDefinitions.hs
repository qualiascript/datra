{-# LANGUAGE LambdaCase #-}

-- | Declarative AST templates. External AST adapters preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxTemplate (..), SyntaxPiece (..), SyntaxHoleKind (..)
  , SyntaxFunctionBody, syntaxFunctionBodyForSymbol, applySyntaxFunctionBody
  , declarationRules, syntaxTemplatesFromExpression
  , syntaxTemplateFromPattern, syntaxTemplateLiteralPrefix
  , qualifySyntaxRule, expandSyntax
  , declarationLiterals, absorbFunSequence, externalSymbol
  ) where
import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , parseSyntaxTemplate
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

newtype SyntaxFunctionBody = SyntaxFunctionBody
  { applySyntaxFunctionBody
      :: [Expression]
      -> Either SyntaxExpansionFailure Expression
  }

syntaxFunctionBodyForSymbol :: String -> Maybe SyntaxFunctionBody
syntaxFunctionBodyForSymbol symbol = SyntaxFunctionBody <$> lookup symbol
  [ ("datra.if", \case
      [condition, yes, no] -> Right
        (conditionalWithBindings condition yes no)
      captures -> invalidBody symbol captures)
  , ("datra.ifThen", \case
      [condition, yes] -> Right
        (conditionalWithBindings condition yes (AtlasMap []))
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
  , ("datra.val", \case
      [value] -> Right (StripIdentifiers value)
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
    _ -> Left (InvalidDependentBinder name)

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
      [ SyntaxRule key template
          signature False Nothing body
      | template <- maybe [] id (syntaxTemplatesFromExpression templates)
      ]
    collect _ _ = []
declarationRules _ = []

-- | The left operand of @%>@ is an ordinary inhabited list value. Rules must
-- be available before evaluation, so each member is required to be an
-- explicit extracted string at declaration time.
syntaxTemplatesFromExpression
  :: Expression
  -> Maybe [SyntaxTemplate Expression]
syntaxTemplatesFromExpression (Extract templates) = templateValues templates
  where
    templateValues value@AsciiStringLiteral {} =
      (: []) <$> templateValue value
    templateValues value@StringTemplate {} =
      (: []) <$> templateValue value
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
    templatePart StringTemplateWeakInterpolation {} = Nothing
syntaxTemplatesFromExpression _ = Nothing

syntaxTemplateFromPattern :: String -> SyntaxTemplate Expression
syntaxTemplateFromPattern = parseSyntaxTemplate
  (IdentifierReference . IdentifierString)

syntaxTemplateLiteralPrefix :: SyntaxRule -> [String]
syntaxTemplateLiteralPrefix = foldr prefix []
  . syntaxTemplatePieces . syntaxTemplate
  where
    prefix (SyntaxLiteral literal) rest = literal : rest
    prefix (SyntaxHole _) _ = []

-- | Qualify the callable binding and its independently declared surface head.
-- They need not have the same unqualified spelling.
qualifySyntaxRule :: String -> SyntaxRule -> SyntaxRule
qualifySyntaxRule namespace rule = rule
  { syntaxName = qualifiedName
  , syntaxTemplate = qualifyTemplate (syntaxTemplate rule)
  }
  where
    originalName = syntaxName rule
    qualifiedName = namespace <> "." <> originalName
    qualifyTemplate (SyntaxTemplate (SyntaxLiteral name : pieces)) =
      SyntaxTemplate
        (SyntaxLiteral (namespace <> "." <> name) : pieces)
    qualifyTemplate template = template

-- | Expand captures selected by one declared syntax template.
expandSyntax
  :: SyntaxRule
  -> [Expression]
  -> Either SyntaxExpansionFailure Expression
expandSyntax rule captures = case
    externalSymbol (syntaxImplementation rule) >>= syntaxFunctionBodyForSymbol of
  Just body -> applySyntaxFunctionBody body (specifiedValueCaptures captures)
  _ -> Right (FunctionApplication
    callable
    (case captures of [value] -> value; _ -> AtlasMap captures))
  where
    callable = scoped (IdentifierReference (IdentifierString localName))
    localName = reverse (takeWhile (/= '.') (reverse (syntaxName rule)))
    scoped value = maybe value (`InModule` value) (syntaxModule rule)
    specifiedValueCaptures = zipWith specifyCapture
      [kind | SyntaxHole kind <- syntaxTemplatePieces (syntaxTemplate rule)]
    specifyCapture (ValueSyntaxHole kind) capture =
      MapSpecification capture
        (scopeHoleType kind)
    specifyCapture _ capture = capture
    scopeHoleType value@IdentifierReference {} = scoped value
    scopeHoleType value = value

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
conditionalWithBindings condition yes no
  | null (selectedConditionBindings condition yes no) =
      Conditional condition yes no
  | otherwise = lower condition yes no
  where
    lower (BooleanOr left right) consequent alternative =
      lower left consequent (lower right consequent alternative)
    lower (BooleanAnd left right) consequent alternative =
      lower left (lower right consequent alternative) alternative
    lower (BooleanNot operand) consequent alternative =
      lower operand alternative consequent
    lower operand consequent alternative =
      lowerConditionAtom operand consequent alternative

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
    findSymbol (MapConcatenation a b) = first [findSymbol a,findSymbol b]
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
      , last remaining == IdentifierReference (IdentifierString "this") ->
          EitherType (AtlasMap []) (MapSequence (headValue : remaining))
    AtlasMap (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , last remaining == IdentifierReference (IdentifierString "this") ->
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
