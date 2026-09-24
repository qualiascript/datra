-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( ModuleSource (..)
  , EvaluationMode (..)
  , moduleExportNames
  , interpretLocatedWithImports
  , interpretLocatedWithImportsInMode
  , interpretWithImports
  , interpretWithImportsInMode
  , InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpression
  , interpretLocatedExpression
  , interpretExpressionReason
  , interpretedValueKind
  , interpretedValueHasTotalMap
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , canonicalStringCodec
  ) where

import Data.Bifunctor qualified as Bifunctor
import Data.List (nub)
import FunctionArguments
import FunctionInference
import ModuleNames (moduleIdentifier, isPrivateIdentifier)
import StandardLibrary (standardLibrarySource)
import Control.Monad (foldM)
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , normalizeExpression
  , mapExpressionChildren
  )
import DatraTypes
import Parsing (parseDatra)
import Rendering (renderCanonicalResult, renderInterpretedValue)
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import Numeric.Natural (Natural)

interpretExpression
  :: Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretExpression =
  Bifunctor.first withoutSourceSpan . interpretExpressionReason

interpretLocatedExpression
  :: Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedExpression (Located sourceSpan expressionValue) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretExpressionReason expressionValue)

interpretLocatedWithImports :: [(String, ModuleSource)] -> Located Expression -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedWithImports =
  interpretLocatedWithImportsInMode DevelopmentMode

interpretLocatedWithImportsInMode
  :: EvaluationMode
  -> [(String, ModuleSource)]
  -> Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedWithImportsInMode mode modules (Located sourceSpan expression) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretWithImportsInMode mode modules expression)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason = interpretWithImports []

interpretWithImports :: [(String, ModuleSource)] -> Expression -> Either InterpretingError InterpretedValue
interpretWithImports modules expression = do
  scope <- standardScope
  evalInScope (("\0imports", ModuleCatalog modules) : scope) [] expression

interpretWithImportsInMode
  :: EvaluationMode
  -> [(String, ModuleSource)]
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithImportsInMode mode modules expression =
  interpretWithImports
    (map (fmapModule mode) modules)
    (expressionForMode mode expression)

data ModuleSource = StandardLibraryModule | ModuleSource FilePath Expression [(String, ModuleSource)]

data EvaluationMode
  = DevelopmentMode
  | ProductionMode
  deriving (Eq, Show)

expressionForMode :: EvaluationMode -> Expression -> Expression
expressionForMode DevelopmentMode = id
expressionForMode ProductionMode = removeSoftAssertions
  where
    removeSoftAssertions (Assert False _) = AtlasMap []
    removeSoftAssertions expressionValue =
      mapExpressionChildren removeSoftAssertions expressionValue

fmapModule
  :: EvaluationMode
  -> (String, ModuleSource)
  -> (String, ModuleSource)
fmapModule mode (name, source) = (name, transform source)
  where
    transform StandardLibraryModule = StandardLibraryModule
    transform (ModuleSource path expression dependencies) =
      ModuleSource
        path
        (expressionForMode mode expression)
        (map (fmapModule mode) dependencies)


standardScope :: Either InterpretingError Scope
standardScope = do
  exported <- filter (not . isPrivateIdentifier . fst) <$> standardLibraryScope
  pure (("StandardLibrary", NamespaceBinding "standard_library" exported) : exported)

standardLibraryScope :: Either InterpretingError Scope
standardLibraryScope = do
  expression <- either (Left . FunctionError) Right (parseDatra standardLibrarySource)
  scope <- standardLibraryInternalScope
  moduleResult scope expression >>= exportedBindings

standardLibraryInternalScope :: Either InterpretingError Scope
standardLibraryInternalScope = case parseDatra standardLibrarySource of
  Left message -> Left (FunctionError ("standard_library.datra: " <> message))
  Right (Program bindings _) -> importScope [] [] bindings
  Right _ -> Left (FunctionError "standard_library.datra must contain declarations")

canonicalStringCodec :: CanonicalStringCodec
canonicalStringCodec =
  CanonicalStringCodec
    { renderCanonicalString = renderInterpretedValue
    , decodeCanonicalString = canonicalStringCandidates
    }

canonicalStringCandidates :: String -> [InterpretedValue]
canonicalStringCandidates characters =
  asciiCandidate <> parsedCanonicalCandidate
  where
    -- String-valued federations use their contents without source delimiters.
    asciiCandidate =
      case asciiStringValue characters of
        Right value -> [value]
        Left _ -> []
    -- Every other value must already use its canonical source spelling.
    parsedCanonicalCandidate =
      case parseDatra ("(" <> characters <> "\n)") of
        Left _ -> []
        Right expressionValue ->
          case interpretExpressionReason expressionValue of
            Right value
              | canonicalSpelling characters
                  (renderInterpretedValue value) ->
                    [ candidate
                    | candidateExpression <-
                        canonicalExpressionCandidates expressionValue
                    , Right candidate <-
                        [interpretExpressionReason candidateExpression]
                    ]
            _ -> []

    -- Parentheses are canonical when a rendered value is embedded as one
    -- component of a larger expression. No other alternate spelling is
    -- accepted by the inverse.
    canonicalSpelling actual rendered =
      actual == rendered || actual == "(" <> rendered <> ")"

-- Canonical Either and map syntax can retain the unselected branches that
-- explain a value's type. Decode those contexts into their concrete member
-- expressions before asking the semantic federation to select one.
canonicalExpressionCandidates :: Expression -> [Expression]
canonicalExpressionCandidates expressionValue =
  case expressionValue of
    EitherType left right ->
      canonicalExpressionCandidates left
        <> canonicalExpressionCandidates right
    AtlasMap members ->
      AtlasMap <$> traverse canonicalExpressionCandidates members
    MapSequence members ->
      MapSequence <$> traverse canonicalExpressionCandidates members
    ArgumentMap members ->
      ArgumentMap <$> traverse canonicalExpressionCandidates members
    MapExpansion left right ->
      MapExpansion
        <$> canonicalExpressionCandidates left
        <*> canonicalExpressionCandidates right
    MapConcatenation left right ->
      MapConcatenation
        <$> canonicalExpressionCandidates left
        <*> canonicalExpressionCandidates right
    _ -> [expressionValue]

type Interpreter = Expression -> Either InterpretingError InterpretedValue

type Scope = [(String, Binding)]

data Binding
  = DeferredBinding Scope Expression
  | EvaluatedBinding InterpretedValue
  | NamespaceBinding FilePath Scope
  | ModuleCatalog [(String, ModuleSource)]
  | ScopeMembers [String]

evalInScope :: Scope -> [String] -> Interpreter
evalInScope scope resolving = interpretNormalizedExpression scope resolving . normalizeExpression

interpretNormalizedExpression :: Scope -> [String] -> Interpreter
interpretNormalizedExpression scope resolving expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    AsciiStringLiteral value -> asciiStringValue value
    NothingLiteral -> Right nothingValue
    StringTemplate parts -> interpretStringTemplateWith interpret parts
    StringType -> Right stringTypeValue
    IdentifierValueType -> Right identifierValueTypeValue
    AtlasMap expressions ->
      interpretAtlasMapWith interpret expressions
    ArgumentMap expressions ->
      traverse interpret expressions >>= makeArgumentMap
    MapSequence expressions ->
      interpretAtlasMapWith interpret expressions
    MapExpansion left right ->
      interpretAtlasMapWithBuilder
        makeAtlasExpansion
        interpret
        [ensureMapLevel left, ensureMapLevel right]
    SuperEllipsisRange lower upper -> do
      lowerValue <- interpret lower
      upperValue <- interpret upper
      boundedRangeValue lowerValue upperValue
    SuperEllipsisRangePlus lower ->
      interpret lower >>= openPlusRangeValue
    SuperEllipsisRangeMinus upper ->
      interpret upper >>= openMinusRangeValue
    NaturalRange origin target -> naturalRangeValue origin target
    NaturalRangeUpwards origin -> naturalRangeUpwardsValue origin
    ValuedNaturalRange origin target -> valuedNaturalRangeValue origin target
    ValuedNaturalRangeUpwards origin -> valuedNaturalRangeUpwardsValue origin
    NaturalType -> naturalTypeValue
    IntegerRange origin target -> integerRangeValue origin target
    IntegerRangeUpwards origin -> integerRangeUpwardsValue origin
    IntegerRangeDownwards origin -> integerRangeDownwardsValue origin
    ValuedIntegerRange origin target -> valuedIntegerRangeValue origin target
    ValuedIntegerRangeUpwards origin -> valuedIntegerRangeUpwardsValue origin
    ValuedIntegerRangeDownwards origin -> valuedIntegerRangeDownwardsValue origin
    IntegerType -> integerTypeValue
    BooleanLiteral value -> Right (booleanValue value)
    BooleanType -> booleanTypeValue
    EitherType left right ->
      binary eitherValue left right
    OptionalType operand ->
      interpret operand >>= optionalValue
    Conditional condition consequent alternative -> do
      conditionValue <- interpret condition
      conditionFlag <- booleanCondition conditionValue
      interpret (if conditionFlag then consequent else alternative)
    Addition left right ->
      binary addValues left right
    Subtraction left right ->
      binary subtractValues left right
    Minus operand -> interpret operand >>= minusValue
    Multiplication left right ->
      binary multiplyValues left right
    Exponentiation base exponentValue ->
      binary exponentiateValues base exponentValue
    Subfederation source target ->
      binary subfederationValues source target
    Equality left right ->
      binary equalValues left right
    Inequality left right -> do
      equal <- binary equalValues left right
      booleanNotValue equal
    BooleanAnd left right ->
      binary booleanAndValues left right
    BooleanOr left right ->
      binary booleanOrValues left right
    BooleanNot operand ->
      interpret operand >>= booleanNotValue
    Extract operand ->
      interpret operand >>= extractValue
    This -> scopeValue scope resolving
    InModule path body -> do
      moduleSource <- lookupModule scope path
      imported <- moduleScope moduleSource
      evalInScope imported resolving body
    Import _ _ -> Left (FunctionError "import must be a scope entry")
    SyntaxType text ordinary signature -> do
      value <- interpret signature
      case interpretedFunction value of
        Just function -> pure (makeFunctionValue function { functionPattern = Just (text, ordinary) })
        Nothing -> Left (FunctionError "an AST pattern requires a function signature")
    FunctionType domain codomain -> do
      input <- compileParameters interpret domain >>= parameterDomain
      output <- interpret codomain
      pure (makeFunctionValue
        (EvaluatedFunction input output Nothing Nothing Nothing Nothing))
    FunctionBody bindings result -> createFunction scope resolving Nothing bindings result
    FunctionApplication function argument -> do
      callable <- interpret function
      input <- interpret argument >>= functionArgumentValue
      applyFunction callable input
    External descriptor -> interpret descriptor >>= externalValue
    Program bindings result -> evaluateBlock Nothing bindings result
    Begin bindings result ->
      evaluateBlock (Just (renderSourceExpression expressionValue)) bindings result
    Let _ -> Left LetOutsideBegin
    IdentifierReference (IdentifierString name) -> resolveIdentifier scope resolving name
    Eval source target ->
      binary (evalValues canonicalStringCodec) source target
    Assert _ condition -> do
      accepted <- interpret condition >>= booleanCondition
      if accepted
        then Right (makeAtlasMap 0 [])
        else Left AssertionFailed
    MapConcatenation left right ->
      binary concatenateValues left right
    Overload defaults supplied ->
      binary overloadValues defaults supplied
    SafeOverload defaults supplied ->
      binary safeOverloadValues defaults supplied
    NamedAccess (IdentifierReference (IdentifierString namespace)) (IdentifierString name)
      | Just (NamespaceBinding _ exported) <- lookup namespace scope -> do
          member <- resolveIdentifier exported [] name
          namedAccessValue (simpleIdentifierTypeValue name member) name
    NamedAccess operand (IdentifierString name) -> interpret operand >>= (`namedAccessValue` name)
    MapAccess mapOperand insertionOperand ->
      binary accessValues mapOperand insertionOperand
    MapSpecification implementation (SyntaxType text ordinary signature) -> do
      value <- interpret (MapSpecification implementation signature)
      case interpretedFunction value of
        Just function -> pure (makeFunctionValue function { functionPattern = Just (text, ordinary) })
        Nothing -> Left (FunctionError "an AST pattern requires a function implementation")
    MapSpecification (FunctionBody bindings result) (FunctionType domain codomain) ->
      createFunction scope resolving (Just (domain, codomain)) bindings result
    MapSpecification sourceOperand targetOperand ->
      interpretSpecificationWith interpret sourceOperand targetOperand
    IdentifierOperation
        (IdentifierString identifierString)
        typeAnnotationExpression
        maybeGivenValueExpression -> do
      typeAnnotation <- interpret typeAnnotationExpression
      case maybeGivenValueExpression of
        Nothing
          | identifierString == "False"
          , interpretedValueKind typeAnnotation == NaturalValueKind
          , interpretedInteger typeAnnotation == Just 0 ->
              Right (booleanValue False)
        Nothing
          | identifierString == "True"
          , interpretedValueKind typeAnnotation == NaturalValueKind
          , interpretedInteger typeAnnotation == Just 1 ->
              Right (booleanValue True)
        Nothing ->
          Right (simpleIdentifierTypeValue identifierString typeAnnotation)
        Just givenValueExpression -> do
          givenValue <- interpret givenValueExpression
          case assignIdentifierValues
              identifierString typeAnnotation givenValue of
            Left
                (AtlasMapFederationOperationRefuted
                  AtlasMapFederationSpecificationHasNoMatchingMember) ->
              Left
                (GivenValueOutsideTypeAnnotation
                  { expectedTypeAnnotation =
                      renderInterpretedValue typeAnnotation
                  , givenValue = renderInterpretedValue givenValue
                  })
            result -> result

  where
    interpret = evalInScope scope resolving
    binary = interpretBinaryWith interpret
    evaluateBlock source bindings result = do
      imported <- importScope scope resolving bindings
      withEvaluationSource source <$> evalInScope imported resolving result

resolveIdentifier
  :: Scope -> [String] -> String -> Either InterpretingError InterpretedValue
resolveIdentifier scope resolving name =
  case lookup name scope of
    Nothing -> Left (UnknownIdentifier name)
    Just (EvaluatedBinding value) -> Right value
    Just (NamespaceBinding _ exported) -> do
      values <- traverse (\(key, _) -> simpleIdentifierTypeValue key <$> resolveIdentifier exported resolving key) exported
      pure (makeAtlasMap 2 values)
    Just ScopeMembers {} -> Left (UnknownIdentifier name)
    Just ModuleCatalog {} -> Left (UnknownIdentifier name)
    Just (DeferredBinding captured expressionValue) ->
      evalInScope captured resolving expressionValue

-- A block imports declarations from left to right. Ordinary definitions capture
-- only earlier ordinary definitions, while every let definition is predeclared
-- throughout the block. Lets are forced before yield and their results replace
-- the deferred definitions. Names are checked before evaluating any binding.
importScope :: Scope -> [String] -> [Expression] -> Either InterpretingError Scope
importScope enclosing resolving entries = do
  outer <- foldM importModule enclosing [(allNames,path) | Import allNames path <- entries]
  let (definitions, eagerEntries) = foldMap (bindingImports False) entries
  _ <- foldM checkName (map fst outer) definitions
  let names = [name | (name, _, _) <- definitions]
      initial = ("\0this", ScopeMembers names) : predeclaredLets <> outer
      predeclaredLets =
        [ (name, DeferredBinding (scopeBefore position) expressionValue)
        | (position, (name, strict, expressionValue)) <- zip [0..] definitions
        , strict
        ]
      scopeBefore position =
        foldl importOrdinary initial (take position definitions)
      importOrdinary scope (name, strict, expressionValue)
        | strict = scope
        | otherwise =
            (name, DeferredBinding scope expressionValue) : scope
      deferred = foldl importOrdinary initial definitions
  evaluated <- traverse
    (\(name, _, _) -> (name,) <$> resolveIdentifier deferred resolving name)
    (filter (\(_, strict, _) -> strict) definitions)
  let imported = map replaceEvaluated deferred
      replaceEvaluated entry@(name, _) =
        maybe entry ((name,) . EvaluatedBinding) (lookup name evaluated)
  -- Anonymous let entries still have eager evaluation semantics.
  mapM_ (evalInScope imported resolving) eagerEntries
  pure imported
  where
    checkName names (name, _, _)
      | name `elem` names =
          Left (IdentifierStringOverlap name)
      | otherwise = Right (name : names)

-- Only declaration-shaped block entries create lexical bindings. Maps and map
-- operators remain values: identifier-shaped members inside them neither enter
-- the surrounding scope nor become visible to sibling members.
bindingImports :: Bool -> Expression -> ([(String, Bool, Expression)], [Expression])
bindingImports strict expressionValue =
  case expressionValue of
    Let binding -> bindingImports True binding
    IdentifierOperation (IdentifierString name) annotation given ->
      ([(name, strict, maybe annotation (\value -> if value == annotation then value else MapSpecification value annotation) given)], [])
    EitherType named@(IdentifierOperation _ annotation _) missing
      | annotation == missing -> bindingImports strict named
    Assert {} -> ([], [expressionValue])
    _ -> ([], [expressionValue | strict])

interpretStringTemplateWith
  :: Interpreter
  -> [StringTemplatePart Expression]
  -> Either InterpretingError InterpretedValue
interpretStringTemplateWith interpret parts = do
  values <- traverse interpretPart parts
  case values of
    [] -> asciiStringValue ""
    firstValue : remaining -> do
      result <- foldM concatenateTemplateValues firstValue remaining
      pure (stringTemplateValue result)
  where
    interpretPart (StringTemplateLiteral value) = asciiStringValue value
    interpretPart (StringTemplateInterpolation expressionValue) = do
      value <- interpret expressionValue
      toStringValue canonicalStringCodec value
    interpretPart (StringTemplateWeakInterpolation expressionValue) = do
      value <- interpret expressionValue
      weakToStringValue canonicalStringCodec value

    concatenateTemplateValues left right =
      case concatenateValues left right of
        Right value -> Right value
        Left _ -> Left AmbiguousStringTemplate

interpretSpecificationWith
  :: Interpreter
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretSpecificationWith interpret sourceExpression targetExpression = do
  source <- interpret sourceExpression
  target <- interpret targetExpression
  case specifyValues source target of
    Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)
      | Just (expected, given) <- identifierAnnotationMismatch source target ->
          Left
            (GivenValueOutsideTypeAnnotation
              { expectedTypeAnnotation = expected
              , givenValue = given
              })
    Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSubfederationHasMissingMember)
      | Just (expected, given) <-
          identifierIntermediateAnnotationMismatch source target ->
          Left
            (IntermediateTypeAnnotationOutsideTarget
              { expectedTargetTypeAnnotation = expected
              , givenIntermediateTypeAnnotation = given
              })
    result -> result

identifierAnnotationMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierAnnotationMismatch =
  identifierValueMismatch identifierGivenValue

identifierIntermediateAnnotationMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierIntermediateAnnotationMismatch =
  identifierValueMismatch identifierIntermediateValue

identifierValueMismatch
  :: (CanonicalResult -> Maybe (String, CanonicalResult))
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierValueMismatch givenValueFor source target = do
  (givenString, givenResult) <-
    givenValueFor (interpretedCanonicalResult source)
  (expectedString, expectedResult) <-
    identifierExpectedValue (interpretedCanonicalResult target)
  if givenString == expectedString
    then
      Just
        ( renderCanonicalResult expectedResult
        , renderCanonicalResult givenResult
        )
    else Nothing

identifierGivenValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierGivenValue result =
  case result of
    CanonicalSimpleIdentifierType identifierString givenValue ->
      Just (identifierString, givenValue)
    CanonicalAssignment identifierString _ givenValue ->
      Just (identifierString, givenValue)
    CanonicalSpecification source _ -> identifierGivenValue source
    _ -> Nothing

identifierExpectedValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierExpectedValue result =
  case result of
    CanonicalSimpleIdentifierType identifierString typeAnnotation ->
      Just (identifierString, typeAnnotation)
    CanonicalAssignment identifierString typeAnnotation _ ->
      Just (identifierString, typeAnnotation)
    CanonicalSpecification _ target -> identifierExpectedValue target
    _ -> Nothing

identifierIntermediateValue
  :: CanonicalResult
  -> Maybe (String, CanonicalResult)
identifierIntermediateValue result =
  case result of
    CanonicalAssignment identifierString typeAnnotation _ ->
      Just (identifierString, typeAnnotation)
    CanonicalSpecification _ intermediate ->
      identifierExpectedValue intermediate
    _ -> Nothing

interpretBinaryWith
  :: Interpreter
  -> ( InterpretedValue
       -> InterpretedValue
       -> Either InterpretingError InterpretedValue
     )
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretBinaryWith interpret operation left right = do
  leftValue <- interpret left
  rightValue <- interpret right
  operation leftValue rightValue

interpretAtlasMapWith
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWith interpret expressions = do
  interpretAtlasMapWithBuilder makeAtlasMap interpret expressions

interpretAtlasMapWithBuilder
  :: (Natural -> [InterpretedValue] -> InterpretedValue)
  -> (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWithBuilder buildMap interpret expressions = do
  values <- traverse interpret expressions
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  pure (buildMap cardinality values)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ -> mapNestingDepth
    MapSequence _ -> mapNestingDepth
    MapExpansion _ _ -> mapNestingDepth
    _ -> 0
  where
    mapNestingDepth =
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1

ensureMapLevel :: Expression -> Expression
ensureMapLevel expressionValue =
  case expressionValue of
    AtlasMap _ -> expressionValue
    MapSequence _ -> expressionValue
    MapExpansion _ _ -> expressionValue
    _ -> AtlasMap [expressionValue]


createFunction :: Scope -> [String] -> Maybe (Expression, Expression)
  -> [Expression] -> Expression -> Either InterpretingError InterpretedValue
createFunction captured resolving explicit bindings result = do
  (domainExpression, specifiedOutput) <- case explicit of
    Just (domain, codomain) -> Right (domain, Just codomain)
    Nothing -> do
      let body = FunctionBody bindings result
          names = filter (`notElem` map fst captured) (freeIdentifiers body)
      inferred <- inferParameters names body
      let parameter (name, target) = EitherType
            (IdentifierOperation (IdentifierString name) target Nothing) target
      pure (AtlasMap (map parameter inferred), Nothing)
  schema <- compileParameters evaluate domainExpression
  let parameters = parameterBindings schema
      names = map fst parameters
  case [name | name <- names, name `elem` map fst captured || length (filter (== name) names) > 1] of
    name : _ -> Left (IdentifierStringOverlap name)
    [] -> pure ()
  input <- parameterDomain schema
  inferredOutput <- inferBody evaluateForInference parameters bindings result
  output <- case specifiedOutput of
    Nothing -> pure inferredOutput
    Just annotation -> do
      target <- evaluate annotation
      included <- subfederationValues inferredOutput target >>= booleanCondition
      if included then pure target else Left (FunctionError "function body does not satisfy its declared output type")
  let invoke argument = do
        imported <- matchArguments schema argument
        let localScope = [(name, EvaluatedBinding value) | (name,value) <- imported] <> captured
        bodyScope <- importScope localScope [] bindings
        value <- evalInScope bodyScope [] result
        _ <- specifyValues value output
        pure value
  pure (makeFunctionValue (EvaluatedFunction input output Nothing
    (Just (renderSourceExpression (FunctionBody bindings result)))
    (Just (prepareArguments schema)) (Just invoke)))
  where
    evaluate = evalInScope captured resolving
    -- A recursive call is checked against its declared signature. Evaluating
    -- the body here would demand the closure while it is still being checked.
    -- Ordinary cyclic values still go through resolveIdentifier's cycle check.
    evaluateForInference (IdentifierReference (IdentifierString name))
      | Just (DeferredBinding lexical (MapSpecification (FunctionBody _ _) signature@FunctionType {})) <- lookup name captured =
          evalInScope lexical resolving signature
    evaluateForInference expression = evaluate expression

applyFunction :: InterpretedValue -> InterpretedValue -> Either InterpretingError InterpretedValue
applyFunction callable input = case candidates of
  [function] | Just invoke <- functionInvoke function -> do
    value <- invoke input
    _ <- specifyValues value (functionCodomain function)
    pure value
  []
    | any ambiguous preparations ->
        Left (FunctionError
          "ambiguous argument bindings; supply identifiers to select the intended slots")
    | otherwise -> Left (FunctionError
        "no applicable function alternative; syntax-only alternatives require their AST pattern")
  [_] -> Left (FunctionError "this external adapter requires unevaluated AST captures")
  _ -> Left (FunctionError "ambiguous function sum application")
  where
    preparations = [(function, prepare function)
      | function <- functionAlternatives callable
      , maybe True snd (functionPattern function)]
    candidates = [function | (function, Right _) <- preparations]
    ambiguous (_, Left (OverloadError failure)) =
      overloadFailureIsAmbiguous failure
    ambiguous _ = False
    prepare function =
      case functionPrepare function of
        Just operation -> operation input
        Nothing -> input <$ validateFunctionInput input (functionDomain function)

externalValue :: InterpretedValue -> Either InterpretingError InterpretedValue
externalValue descriptor | CanonicalAsciiString symbol <- interpretedCanonicalResult descriptor = registeredExternal symbol
externalValue descriptor = do
  fields <- fieldsOf (interpretedCanonicalResult descriptor)
  if length (map fst fields) /= length (nub (map fst fields))
    then Left (FunctionError "duplicate external descriptor field") else pure ()
  if map fst fields `containsOnly` ["backend", "symbol"]
    then pure () else Left (FunctionError "unknown external descriptor field")
  backend <- required "backend" fields
  symbol <- required "symbol" fields
  if backend /= "haskell" then Left (FunctionError ("unknown external backend: " <> backend))
    else registeredExternal symbol
  where
    containsOnly actual expected = all (`elem` expected) actual
    required name fields = maybe (Left (FunctionError ("missing external field: " <> name))) Right (lookup name fields)
    fieldsOf (CanonicalMap _ members) = concat <$> traverse fieldsOf members
    fieldsOf (CanonicalConcatenation members) = concat <$> traverse fieldsOf members
    fieldsOf (CanonicalSimpleIdentifierType name (CanonicalAsciiString value)) = Right [(name,value)]
    fieldsOf (CanonicalAssignment name _ (CanonicalAsciiString value)) = Right [(name,value)]
    fieldsOf _ = Left (FunctionError "external requires a map of string fields")

registeredExternal :: String -> Either InterpretingError InterpretedValue
registeredExternal symbol = case symbol of
  "datra.Nat" -> naturalTypeValue
  "datra.Int" -> integerTypeValue
  "datra.String" -> Right stringTypeValue
  "datra.Iden" -> Right identifierValueTypeValue
  "datra.AST" -> Right astTypeValue
  "datra.Expr" -> Right (syntaxCategoryTypeValue "Expr")
  "datra.Block" -> Right (syntaxCategoryTypeValue "Block")
  "datra.Pages" -> Right (syntaxCategoryTypeValue "Pages")
  "datra.syntax.if" -> syntaxAdapter 3
  "datra.syntax.ifThen" -> syntaxAdapter 2
  "datra.syntax.begin" -> syntaxAdapter 2
  "datra.syntax.do" -> syntaxAdapter 2
  "datra.syntax.let" -> syntaxAdapter 1
  "datra.syntax.eval" -> syntaxAdapter 2
  "datra.StringTemplate" -> Right stringTemplateTypeValue
  "datra.NatRange" -> Right naturalRangeTypeValue
  "datra.IntRange" -> Right integerRangeTypeValue
  "datra.from" -> nativeRange True
  "datra.range" -> nativeRange False
  "datra.add" -> nativeFunction
    (ArgumentMap [optional "a" IntegerType, optional "b" IntegerType]) IntegerType $ \arguments -> do
      a <- lookupArgument "a" arguments
      b <- lookupArgument "b" arguments
      addValues a b
  "datra.abs" -> nativeFunction (optional "value" IntegerType) NaturalType $ \arguments -> do
    value <- lookupArgument "value" arguments
    integer <- requireFiniteInteger LeftOperand value
    pure (integerValue (abs integer))
  _ -> Left (FunctionError ("unknown registered external: " <> symbol))
  where
    concreteCanonical (CanonicalSpecification source _) = concreteCanonical source
    concreteCanonical value = value
    syntaxAdapter arity = pure (makeFunctionValue (EvaluatedFunction
      (if arity == 1 then astTypeValue else makeAtlasMap 2 (replicate arity astTypeValue)) astTypeValue Nothing
      (Just ("external " <> show symbol)) Nothing Nothing))
    nativeRange valued = do
      ints <- integerTypeValue
      up <- asciiStringValue "upwards"
      down <- asciiStringValue "downwards"
      wards <- eitherValue ints up >>= (`eitherValue` down)
      let domain = makeAtlasMap 2 [ints, wards]
      let invoke argument = do
            startValue <- accessValues argument (naturalValue 0)
            endValue <- accessValues argument (naturalValue 1)
            _ <- specifyValues startValue ints
            _ <- specifyValues endValue wards
            start <- requireFiniteInteger LeftOperand startValue
            case concreteCanonical (interpretedCanonicalResult endValue) of
              CanonicalAsciiString "upwards"
                | start >= 0 -> (if valued then valuedNaturalRangeUpwardsValue else naturalRangeUpwardsValue) (fromInteger start)
                | otherwise -> (if valued then valuedIntegerRangeUpwardsValue else integerRangeUpwardsValue) start
              CanonicalAsciiString "downwards" ->
                if valued then valuedIntegerRangeDownwardsValue start else integerRangeDownwardsValue start
              _ -> do
                end <- requireFiniteInteger RightOperand endValue
                if start >= 0 && end >= 0
                  then (if valued then valuedNaturalRangeValue else naturalRangeValue) (fromInteger start) (fromInteger end)
                  else (if valued then valuedIntegerRangeValue else integerRangeValue) start end
      pure (makeFunctionValue (EvaluatedFunction domain integerRangeTypeValue Nothing
        (Just ("external " <> show symbol))
        (Just (\argument -> argument <$ validateFunctionInput argument domain))
        (Just invoke)))
    optional name target = EitherType (IdentifierOperation (IdentifierString name) target Nothing) target
    lookupArgument name values = maybe (Left (FunctionError ("missing native argument " <> name))) Right (lookup name values)
    nativeFunction domain codomain implementation = do
      let evaluate = evalInScope [] []
      schema <- compileParameters evaluate domain
      input <- parameterDomain schema
      output <- evaluate codomain
      let invoke argument = do
            bindings <- matchArguments schema argument
            result <- implementation bindings
            _ <- specifyValues result output
            pure result
      pure (makeFunctionValue (EvaluatedFunction input output Nothing
        (Just ("external " <> show symbol))
        (Just (prepareArguments schema)) (Just invoke)))


importModule :: Scope -> (Bool, String) -> Either InterpretingError Scope
importModule scope (allNames, requested) = do
  (identity, exported) <- lookupModule scope requested >>= moduleExports
  let namespace = moduleIdentifier requested
  namespaceScope <- case lookup namespace scope of
    Nothing -> pure ((namespace, NamespaceBinding identity exported) : scope)
    Just (NamespaceBinding previous _) | previous == identity -> pure scope
    _ -> Left (IdentifierStringOverlap namespace)
  if allNames then foldM (insertExport identity) namespaceScope exported else pure namespaceScope
  where
    insertExport identity values entry@(name,_) = case lookup name values of
      Nothing -> Right (entry:values)
      -- Every file already has this exact implicit import.
      Just _ | identity == "standard_library" -> Right values
      _ -> Left (IdentifierStringOverlap name)

moduleExports :: ModuleSource -> Either InterpretingError (FilePath, Scope)
moduleExports StandardLibraryModule = do
  values <- standardLibraryScope
  pure ("standard_library", filter (not . isPrivateIdentifier . fst) values)
moduleExports moduleSource@(ModuleSource path expression _) = do
  scope <- moduleScope moduleSource
  exports <- moduleResult scope expression >>= exportedBindings
  pure (path, exports)

moduleExportNames :: ModuleSource -> Either InterpretingError [String]
moduleExportNames source = map fst . snd <$> moduleExports source

moduleResult :: Scope -> Expression -> Either InterpretingError InterpretedValue
moduleResult scope (Program _ result) = evalInScope scope [] result
moduleResult scope (Begin _ result) = evalInScope scope [] result
moduleResult _ _ = Left (FunctionError "an imported module must be a declaration block")

scopeValue :: Scope -> [String] -> Either InterpretingError InterpretedValue
scopeValue scope resolving = do
  let names = case lookup "\0this" scope of Just (ScopeMembers values) -> values; _ -> []
  members <- traverse (\name -> simpleIdentifierTypeValue name <$> resolveIdentifier scope resolving name)
    (filter (not . isPrivateIdentifier) names)
  pure (makeAtlasMap 2 members)

exportedBindings :: InterpretedValue -> Either InterpretingError Scope
exportedBindings value = filter (not . isPrivateIdentifier . fst) <$> namedBindings value

namedBindings :: InterpretedValue -> Either InterpretingError Scope
namedBindings value = case interpretedCanonicalResult value of
  CanonicalMap _ members -> traverse field members
  member@CanonicalAssignment {} -> (:[]) <$> field member
  member@CanonicalSimpleIdentifierType {} -> (:[]) <$> field member
  _ -> Left (FunctionError "an imported module must yield a scope or named map; use yield this")
  where
    field (CanonicalSimpleIdentifierType name _) = do
      selected <- namedAccessValue value name
      payload <- accessValues selected (naturalValue 1)
      pure (name, EvaluatedBinding payload)
    field (CanonicalAssignment name _ _) = do
      selected <- namedAccessValue value name
      payload <- accessValues selected (naturalValue 1)
      pure (name, EvaluatedBinding payload)
    field _ = Left (FunctionError "a module export must have an identifier")

lookupModule :: Scope -> String -> Either InterpretingError ModuleSource
lookupModule scope path
  | path `elem` ["standard_library", "standard_library.datra"] = Right StandardLibraryModule
  | Just (ModuleCatalog modules) <- lookup "\0imports" scope
  , Just value <- lookup path modules = Right value
  | otherwise = Left (FunctionError ("module was not loaded: " <> path))

moduleScope :: ModuleSource -> Either InterpretingError Scope
moduleScope StandardLibraryModule = standardLibraryInternalScope
moduleScope (ModuleSource _ expression dependencies) = do
  base <- standardScope
  entries <- case expression of
    Program declarations _ -> Right declarations
    Begin declarations _ -> Right declarations
    _ -> Left (FunctionError "an imported module must contain a declaration block")
  importScope (("\0imports", ModuleCatalog dependencies) : base) [] entries
