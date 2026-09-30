-- | Declarative AST templates. External AST adapters preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxPiece (..), SyntaxHoleKind (..)
  , declarationRules, expandSyntax
  , declarationLiterals, absorbFunSequence, externalSymbol
  ) where
import Data.List (isPrefixOf)
import DatraLanguage.AST
import IdentifierValueType (isIdentifierValue)
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure (..))

data SyntaxHoleKind
  = ExpressionSyntaxHole
  | BlockSyntaxHole
  | IdentifierExpressionSyntaxHole
  | ValueSyntaxHole String
  deriving (Eq,Show)

data SyntaxPiece
  = SyntaxLiteral String
  | SyntaxHole SyntaxHoleKind
  deriving (Eq,Show)
data SyntaxRule = SyntaxRule
  { syntaxName :: String, syntaxPieces :: [SyntaxPiece]
  , syntaxOrdinary :: Bool, syntaxSignature :: Expression
  , syntaxRecursive :: Bool
  , syntaxModule :: Maybe String
  , syntaxImplementation :: Expression
  } deriving (Eq,Show)

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
    collect key (MapSpecification body (SyntaxType patternText ordinary signature)) =
      [SyntaxRule key (map piece (words patternText)) ordinary signature False Nothing body]
    collect _ _ = []
    -- These are parser-level AST categories. Every other hole names the
    -- value type that its captured expression must inhabit.
    piece "$_Expr" = SyntaxHole ExpressionSyntaxHole
    piece "$_Block" = SyntaxHole BlockSyntaxHole
    piece "$_IdenExp" = SyntaxHole IdentifierExpressionSyntaxHole
    piece ('$':kind) = SyntaxHole (ValueSyntaxHole kind)
    piece literal = SyntaxLiteral literal
declarationRules _ = []

expandSyntax
  :: SyntaxRule
  -> [Expression]
  -> Either SyntaxExpansionFailure Expression
expandSyntax rule captures = case externalSymbol (syntaxImplementation rule) of
  Just name | "datra.syntax." `isPrefixOf` name ->
    control name captures
  _ -> Right (FunctionApplication
    callable
    (case captures of [value] -> value; _ -> AtlasMap captures))
  where
    callable
      | syntaxRecursive rule
      , Nothing <- syntaxModule rule =
          IdentifierReference (IdentifierString localName)
      | otherwise = scoped
          (MapSpecification (syntaxImplementation rule) (syntaxSignature rule))
    localName = reverse (takeWhile (/= '.') (reverse (syntaxName rule)))
    scoped value = maybe value (`InModule` value) (syntaxModule rule)
    specifiedValueCaptures = zipWith specifyCapture
      [kind | SyntaxHole kind <- syntaxPieces rule]
    specifyCapture (ValueSyntaxHole kind) capture =
      MapSpecification capture
        (scoped (IdentifierReference (IdentifierString kind)))
    specifyCapture _ capture = capture
    block (AtlasMap entries) = entries
    block value = [value]
    control name values =
      case controlArity name of
        Nothing -> Left (UnknownSyntaxControlAdapter name)
        Just expected
          | length values /= expected ->
              Left
                (InvalidSyntaxControlCaptures
                  name expected (length values))
          | otherwise ->
              controlWithValidCaptures name (specifiedValueCaptures values)
    controlArity "datra.syntax.if" = Just 3
    controlArity "datra.syntax.ifThen" = Just 2
    controlArity "datra.syntax.begin" = Just 2
    controlArity "datra.syntax.do" = Just 2
    controlArity "datra.syntax.let" = Just 1
    controlArity "datra.syntax.fun" = Just 1
    controlArity "datra.syntax.with" = Just 2
    controlArity "datra.syntax.for" = Just 2
    controlArity "datra.syntax.withIn" = Just 3
    controlArity "datra.syntax.forIn" = Just 3
    controlArity "datra.syntax.val" = Just 1
    controlArity _ = Nothing
    controlWithValidCaptures "datra.syntax.if" [condition, yes, no] =
      Right (conditionalWithBindings condition yes no)
    controlWithValidCaptures "datra.syntax.ifThen" [condition, yes] =
      Right (conditionalWithBindings condition yes (AtlasMap []))
    controlWithValidCaptures "datra.syntax.begin" [entries,result] =
      Right (Begin (block entries) result)
    controlWithValidCaptures "datra.syntax.do" [entries,result] =
      Right (FunctionBody (block entries) result)
    controlWithValidCaptures "datra.syntax.let" [entry] =
      Right (Let (absorbAssignedConcatenation entry))
    controlWithValidCaptures "datra.syntax.fun" [entry] =
      Right (Fun (absorbFunSequence entry))
    controlWithValidCaptures "datra.syntax.with" [name,bound] =
      dependentBinder "with" WithBinding name bound
    controlWithValidCaptures "datra.syntax.for" [name,bound] =
      dependentBinder "for" ForBinding name bound
    controlWithValidCaptures "datra.syntax.withIn" [name,bound,body] =
      localDependentFamily "with" WithBinding name bound body
    controlWithValidCaptures "datra.syntax.forIn" [name,bound,body] =
      localDependentFamily "for" ForBinding name bound body
    controlWithValidCaptures "datra.syntax.val" [value] =
      Right (StripIdentifiers value)
    controlWithValidCaptures name _ = Left (UnknownSyntaxControlAdapter name)

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

    -- The witness is deliberately optional in the lowered representation:
    -- projection discards page zero, so the source spelling needs only the
    -- local identifier rather than the public argument-map binder form.
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

    -- @:=@ normally stops before a comma so declarations remain map members.
    -- Inside @let@ the whole captured expression is one early binding, so a
    -- following concatenation belongs to the assigned value.
    absorbAssignedConcatenation value = case value of
      MapConcatenation
          (IdentifierOperation name annotation (Just given)) right
        | annotation == given ->
            let assignedValue = MapConcatenation given right
            in IdentifierOperation name assignedValue (Just assignedValue)
      _ -> value

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
      , last remaining == This ->
          EitherType (AtlasMap []) (MapSequence (headValue : remaining))
    AtlasMap (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , last remaining == This ->
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
