-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( ModuleSource (..)
  , EvaluationMode (..)
  , moduleName
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
  , interpretClosedExpression
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
import Data.List (nub, intercalate)
import FunctionClosure
import FunctionInference
import DatraLanguage.Identifier (public)
import RuntimeModules
  ( EvaluationMode (..)
  , ModuleSource (..)
  , expressionForMode
  , modulesForMode
  )
import StdLib
  ( isStandardLibraryRequest
  , standardLibraryFileName
  , standardLibraryIdentity
  )
import Control.Monad (foldM)
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , namedBeginBlock
  , normalizeExpression
  , mapExpressionChildren
  , yieldedIdentifier
  )
import DatraTypes
import Parsing (parseDatra, standardLibraryExpression)
import Rendering (renderCanonicalResult, renderInterpretedValue)
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (parseFailureMessage) )
import Numeric.Natural (Natural)
import DatraOrdinal (naturalAtOrdinal)

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

-- | Evaluate a closed reconstruction without importing Std or any modules.
interpretClosedExpression :: Expression -> Either InterpretingError InterpretedValue
interpretClosedExpression = evalInScope [] []

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
    (modulesForMode mode modules)
    (expressionForMode mode expression)


standardScope :: Either InterpretingError Scope
standardScope = do
  expression <- parsedStandardLibrary
  namespace <- declaredModuleName expression
  value <- standardLibraryValue
  exported <- exportedBindings value
  pure
    ((namespace,
      ImportedBinding standardLibraryIdentity value) : exported)

standardLibraryValue :: Either InterpretingError InterpretedValue
standardLibraryValue = do
  expression <- parsedStandardLibrary
  case namedBeginBlock expression of
    Just (_, bindings, result) ->
      evalInScope [] [] (Begin bindings result)
    Nothing -> Left (ModuleEvaluationFailed
      (StandardLibraryRequiresDeclarationBlock standardLibraryFileName))

standardLibraryInternalScope :: Either InterpretingError Scope
standardLibraryInternalScope =
  parsedStandardLibrary >>= standardLibraryInternalScopeFor

parsedStandardLibrary :: Either InterpretingError Expression
parsedStandardLibrary =
  either
    (Left . ModuleEvaluationFailed
      . StandardLibraryParseFailure standardLibraryFileName
      . parseFailureMessage)
    Right
    standardLibraryExpression

standardLibraryInternalScopeFor
  :: Expression
  -> Either InterpretingError Scope
standardLibraryInternalScopeFor expression =
  case namedBeginBlock expression of
    Just (_, bindings, _) -> importScope [] [] bindings
    Nothing -> Left (ModuleEvaluationFailed
      (StandardLibraryRequiresDeclarationBlock standardLibraryFileName))

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
  = DeferredBinding Scope (Maybe Expression) Expression
  | EvaluatedBinding InterpretedValue
  | RetainedBinding Scope (Maybe Expression) Expression InterpretedValue
  | ImportedBinding FilePath InterpretedValue
  | ModuleCatalog [(String, ModuleSource)]
  | ScopeMembers [String]
  | CanonicalNames [(String, String)]

evalInScope :: Scope -> [String] -> Interpreter
evalInScope scope resolving = interpretNormalizedExpression scope resolving . normalizeExpression

interpretNormalizedExpression :: Scope -> [String] -> Interpreter
interpretNormalizedExpression scope resolving expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    Skip -> Right skipValue
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
    Import _ _ -> Left (ModuleEvaluationFailed ImportOutsideScope)
    SyntaxType text ordinary signature -> do
      value <- interpret signature
      case interpretedFunction value of
        Just function -> pure (makeFunctionValue function { functionPattern = Just (text, ordinary) })
        Nothing -> Left (FunctionEvaluationFailed
          AstPatternRequiresFunctionSignature)
    FunctionType domain codomain -> do
      input <- compileParameters interpret domain >>= parameterDomain
      output <- interpret codomain
      signatureText <- signatureSource input output
      pure (makeFunctionValue
        (EvaluatedFunction input output Nothing Nothing signatureText Nothing Nothing True))
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
    NamedAccess
        (IdentifierReference (IdentifierString namespace))
        (IdentifierString name)
      | Just (ImportedBinding _ value) <- lookup namespace scope ->
          case namedAccessValue value name of
            Left (NamedAccessFailed (NamedFieldNotFound _)) ->
              Left (UnknownIdentifier name)
            result -> result
    -- Project one declared binding without forcing the whole scope map. This
    -- also permits projections next to recursive function declarations.
    NamedAccess This (IdentifierString name)
      | Just (ScopeMembers names) <- lookup "\0this" scope
      , name `elem` names ->
          simpleIdentifierTypeValue name <$> resolveIdentifier scope resolving name
    NamedAccess operand (IdentifierString name) -> interpret operand >>= (`namedAccessValue` name)
    MapAccess This insertionOperand -> do
      insertion <- interpret insertionOperand
      let names = case lookup "\0this" scope of
            Just (ScopeMembers values) -> values
            _ -> []
          shape = makeAtlasMap 2
            [simpleIdentifierTypeValue name (naturalValue 0) | name <- names]
      -- Validate the index against the declaration map before demanding values.
      _ <- accessValues shape insertion
      case interpretedExplicitOrdinal insertion >>= (naturalAtOrdinal . snd) of
        Just index | name : _ <- drop (fromIntegral index) names ->
          simpleIdentifierTypeValue name <$> resolveIdentifier scope resolving name
        _ -> scopeValue scope resolving >>= (`accessValues` insertion)
    MapAccess mapOperand insertionOperand ->
      binary accessValues mapOperand insertionOperand
    MapSpecification implementation (SyntaxType text ordinary signature) -> do
      value <- interpret (MapSpecification implementation signature)
      case interpretedFunction value of
        Just function -> pure (makeFunctionValue function { functionPattern = Just (text, ordinary) })
        Nothing -> Left (FunctionEvaluationFailed
          AstPatternRequiresFunctionImplementation)
    MapSpecification (FunctionBody bindings result) (FunctionType domain codomain) ->
      createFunction scope resolving (Just (domain, codomain)) bindings result
    MapSpecification sourceOperand targetOperand ->
      interpretSpecificationWith interpret sourceOperand targetOperand
    IdentifierOperation
        (IdentifierString identifierString)
        typeAnnotationExpression
        maybeGivenValueExpression -> do
      typeAnnotation <- interpret typeAnnotationExpression
      requireCanonicalTypeAnnotation typeAnnotation
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
      let origins = canonicalDependencyNames bindings result
          reconstructionScope = if null origins then scope
            else ("\0canonical", CanonicalNames origins) : scope
      imported <- importScope reconstructionScope resolving bindings
      withEvaluationSource source <$> evalInScope imported resolving result

resolveIdentifier
  :: Scope -> [String] -> String -> Either InterpretingError InterpretedValue
resolveIdentifier scope resolving name =
  case lookup name scope of
    Nothing -> Left (UnknownIdentifier name)
    Just (EvaluatedBinding value) -> Right value
    Just (RetainedBinding _ _ _ value) -> Right value
    Just (ImportedBinding _ value) -> Right value
    Just ScopeMembers {} -> Left (UnknownIdentifier name)
    Just CanonicalNames {} -> Left (UnknownIdentifier name)
    Just ModuleCatalog {} -> Left (UnknownIdentifier name)
    Just (DeferredBinding captured annotation expressionValue) -> do
      case annotation of
        Nothing -> pure ()
        Just typeExpression ->
          evalInScope captured resolving typeExpression
            >>= requireCanonicalTypeAnnotation
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
  let names = [name | (name, _, _, _) <- definitions]
      initial = ("\0this", ScopeMembers names) : predeclaredLets <> outer
      predeclaredLets =
        [ (name, DeferredBinding
            (scopeBefore position) annotation expressionValue)
        | (position, (name, strict, annotation, expressionValue)) <-
            zip [0..] definitions
        , strict
        ]
      scopeBefore position =
        foldl importOrdinary initial (take position definitions)
      importOrdinary scope (name, strict, annotation, expressionValue)
        | strict = scope
        | otherwise =
            (name, DeferredBinding scope annotation expressionValue) : scope
      deferred = foldl importOrdinary initial definitions
  evaluated <- traverse
    (\(name, _, _, _) -> (name,) <$> resolveIdentifier deferred resolving name)
    (filter (\(_, strict, _, _) -> strict) definitions)
  let imported = map replaceEvaluated deferred
      replaceEvaluated entry@(name, binding) = case (binding, lookup name evaluated) of
        (DeferredBinding lexical annotation expressionValue, Just value) ->
          (name, RetainedBinding lexical annotation expressionValue value)
        _ -> entry
  -- Anonymous let entries still have eager evaluation semantics.
  mapM_ (evalInScope imported resolving) eagerEntries
  pure imported
  where
    checkName names (name, _, _, _)
      | name `elem` names =
          Left (IdentifierStringOverlap name)
      | otherwise = Right (name : names)

-- Only declaration-shaped block entries create lexical bindings. Maps and map
-- operators remain values: identifier-shaped members inside them neither enter
-- the surrounding scope nor become visible to sibling members.
bindingImports
  :: Bool
  -> Expression
  -> ([(String, Bool, Maybe Expression, Expression)], [Expression])
bindingImports strict expressionValue =
  case expressionValue of
    Let binding -> bindingImports True binding
    IdentifierOperation (IdentifierString name) annotation given ->
      ([(name, strict, annotationToCheck annotation given, bindingValue)], [])
      where
        bindingValue = maybe annotation
          (\value -> if value == annotation
            then value
            else MapSpecification value annotation)
          given
        annotationToCheck typeAnnotation maybeImplementation =
          case maybeImplementation of
            Just implementation
              | implementation == typeAnnotation -> Nothing
            Just FunctionBody {}
              | FunctionType {} <- typeAnnotation -> Nothing
            Just _
              | SyntaxType {} <- typeAnnotation -> Nothing
            _ -> Just typeAnnotation
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
      pure (explicitPrimitives (AtlasMap (map parameter inferred)), Nothing)
  schema <- compileParameters evaluate domainExpression
  let parameters = parameterBindings schema
      names = map fst parameters
  case [ name
       | name <- names
       , name == "it"
          || name `elem` map fst captured
          || length (filter (== name) names) > 1
       ] of
    name : _ -> Left (IdentifierStringOverlap name)
    [] -> pure ()
  input <- parameterDomain schema
  let positionalInput = parameterPositionalDomain schema
  inferredOutput <-
    inferBody
      evaluateForInference
      (("it", positionalInput) : parameters)
      bindings
      result
  output <- case specifiedOutput of
    Nothing -> pure inferredOutput
    Just annotation -> do
      target <- evaluate annotation
      included <- subfederationValues inferredOutput target >>= booleanCondition
      if included then pure target else Left (FunctionEvaluationFailed
        FunctionBodyOutsideDeclaredResult)
  let invoke argument = do
        argumentValues <- parameterValues schema argument
        imported <- matchArguments schema argument
        let localScope =
              ("it", EvaluatedBinding argumentValues)
                : [(name, EvaluatedBinding value) | (name,value) <- imported]
                <> captured
        bodyScope <- importScope localScope [] bindings
        value <- evalInScope bodyScope [] result
        _ <- specifyValues value output
        pure value
  outputExpression <- maybe (valueExpression output) Right specifiedOutput
  signatureText <- signatureSource input output
  let definition = MapSpecification (FunctionBody bindings result)
        (FunctionType domainExpression outputExpression)
      self = case [bindingKey name expressionValue
                  | (name, binding) <- captured
                  , Just (_, _, expressionValue) <- [bindingDefinition binding]
                  , expressionValue == definition] of
        key : _ -> Just key
        [] -> Nothing
      closed = closeFunction (closureResolver captured) self definition
  pure (makeFunctionValue (EvaluatedFunction input output Nothing
    (Just (renderSourceExpression closed)) signatureText
    (Just (prepareArguments schema)) (Just invoke) True))
  where
    evaluate = evalInScope captured resolving
    -- A recursive call is checked against its declared signature. Evaluating
    -- the body here would demand the closure while it is still being checked.
    -- Ordinary cyclic values still go through resolveIdentifier's cycle check.
    evaluateForInference (IdentifierReference (IdentifierString name))
      | Just (DeferredBinding lexical _
          (MapSpecification (FunctionBody _ _) signature@FunctionType {})) <-
            lookup name captured =
          evalInScope lexical resolving signature
    evaluateForInference expression = evaluate expression

applyFunction :: InterpretedValue -> InterpretedValue -> Either InterpretingError InterpretedValue
applyFunction callable input =
  case selectFunctionCandidate preparations of
    Right (function, _) | Just invoke <- functionInvoke function -> do
      value <- invoke input
      _ <- if functionValidatesResult function
        then specifyValues value (functionCodomain function)
        else Right value
      pure value
    Right _ -> Left (FunctionEvaluationFailed
      ExternalAdapterRequiresAstCaptures)
    Left failure -> Left failure
  where
    preparations = [(function, prepare function)
      | function <- functionAlternatives callable
      , maybe True snd (functionPattern function)]
    prepare function =
      case functionPrepare function of
        Just operation -> operation input
        Nothing -> input <$ validateFunctionInput input (functionDomain function)

externalValue :: InterpretedValue -> Either InterpretingError InterpretedValue
externalValue descriptor | CanonicalAsciiString symbol <- interpretedCanonicalResult descriptor = registeredExternal symbol
externalValue descriptor = do
  fields <- fieldsOf (interpretedCanonicalResult descriptor)
  if length (map fst fields) /= length (nub (map fst fields))
    then Left (ExternalEvaluationFailed DuplicateExternalDescriptorField)
    else pure ()
  let unknownFields =
        filter (`notElem` ["backend", "symbol"]) (map fst fields)
  if null unknownFields
    then pure ()
    else Left (ExternalEvaluationFailed
      (UnknownExternalDescriptorFields unknownFields))
  backend <- required "backend" fields
  symbol <- required "symbol" fields
  if backend /= "haskell" then Left (ExternalEvaluationFailed
    (UnsupportedExternalBackend backend))
    else registeredExternal symbol
  where
    required name fields = maybe
      (Left (ExternalEvaluationFailed
        (MissingExternalDescriptorField name)))
      Right
      (lookup name fields)
    fieldsOf (CanonicalMap _ members) = concat <$> traverse fieldsOf members
    fieldsOf (CanonicalConcatenation members) = concat <$> traverse fieldsOf members
    fieldsOf (CanonicalSimpleIdentifierType name (CanonicalAsciiString value)) = Right [(name,value)]
    fieldsOf (CanonicalAssignment name _ (CanonicalAsciiString value)) = Right [(name,value)]
    fieldsOf _ = Left (ExternalEvaluationFailed
      ExternalDescriptorRequiresStringMap)

registeredExternal :: String -> Either InterpretingError InterpretedValue
registeredExternal symbol = case symbol of
  "datra.Any" -> Right anyTypeValue
  "datra.Nat" -> naturalTypeValue
  "datra.Int" -> integerTypeValue
  "datra.String" -> Right stringTypeValue
  "datra.IdenStr" -> Right identifierValueTypeValue
  "datra.public" -> do
    signatureText <- signatureSource anyTypeValue anyTypeValue
    pure (makeFunctionValue (EvaluatedFunction
      anyTypeValue anyTypeValue Nothing
      (Just ("external " <> show symbol)) signatureText
      (Just Right) (Just publicValue) False))
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
  "datra.NatValRange" -> Right naturalValuedRangeTypeValue
  "datra.IntValRange" -> Right integerValuedRangeTypeValue
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
  _ -> Left (ExternalEvaluationFailed (UnknownExternalSymbol symbol))
  where
    concreteCanonical (CanonicalSpecification source _) = concreteCanonical source
    concreteCanonical value = value
    syntaxAdapter arity = do
      let domain = if arity == 1 then astTypeValue else makeAtlasMap 2 (replicate arity astTypeValue)
      signatureText <- signatureSource domain astTypeValue
      pure (makeFunctionValue (EvaluatedFunction domain astTypeValue Nothing
        (Just ("external " <> show symbol)) signatureText Nothing Nothing True))
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
      let codomain =
            if valued then integerValuedRangeTypeValue else integerRangeTypeValue
      signatureText <- signatureSource domain codomain
      pure (makeFunctionValue (EvaluatedFunction domain codomain Nothing
        (Just ("external " <> show symbol)) signatureText
        (Just (\argument -> argument <$ validateFunctionInput argument domain))
        (Just invoke) True))
    optional name target = EitherType (IdentifierOperation (IdentifierString name) target Nothing) target
    lookupArgument name values = maybe
      (Left (ExternalEvaluationFailed (MissingNativeArgument name)))
      Right
      (lookup name values)
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
      signatureText <- signatureSource input output
      pure (makeFunctionValue (EvaluatedFunction input output Nothing
        (Just ("external " <> show symbol)) signatureText
        (Just (prepareArguments schema)) (Just invoke) True))


importModule :: Scope -> (Bool, String) -> Either InterpretingError Scope
importModule scope (allNames, requested) = do
  (identity, namespace, value) <-
    lookupModule scope requested >>= loadedModuleValue
  exported <- if allNames
    then importAllBindings value
    else requireTotalModuleValue value >> pure []
  namespaceScope <- case lookup namespace scope of
    Nothing -> pure ((namespace, ImportedBinding identity value) : scope)
    Just (ImportedBinding previous _) | previous == identity -> pure scope
    _ -> Left (IdentifierStringOverlap namespace)
  if allNames then foldM (insertExport identity) namespaceScope exported else pure namespaceScope
  where
    insertExport identity values entry@(name,_) = case lookup name values of
      Nothing -> Right (entry:values)
      -- Every file already has this exact implicit import.
      Just _ | identity == standardLibraryIdentity -> Right values
      _ -> Left (IdentifierStringOverlap name)

loadedModuleValue
  :: ModuleSource
  -> Either InterpretingError (FilePath, String, InterpretedValue)
loadedModuleValue StdLibModule = do
  name <- moduleName StdLibModule
  value <- standardLibraryValue
  pure (standardLibraryIdentity, name, value)
loadedModuleValue moduleSource@(ModuleSource path expression dependencies) = do
  name <- moduleName moduleSource
  (_, annotation, given) <- case yieldedIdentifier expression of
    Just binding -> Right binding
    Nothing -> Left (ModuleEvaluationFailed
      ImportedModuleRequiresSimpleIdentifierType)
  base <- standardScope
  scope <- importScope
    (("\0imports", ModuleCatalog dependencies) : base)
    []
    (resourceBindings expression)
  let yieldedExpression = case given of
        Nothing -> annotation
        Just value
          | value == annotation -> value
          | otherwise -> MapSpecification value annotation
  value <- evalInScope scope [] yieldedExpression
  pure (path, name, value)

moduleExportNames :: ModuleSource -> Either InterpretingError [String]
moduleExportNames source = do
  (_, _, value) <- loadedModuleValue source
  exported <- importAllBindings value
  pure (map fst exported)

moduleName :: ModuleSource -> Either InterpretingError String
moduleName StdLibModule = parsedStandardLibrary >>= declaredModuleName
moduleName (ModuleSource _ expression _) = declaredModuleName expression

declaredModuleName :: Expression -> Either InterpretingError String
declaredModuleName expression =
  case yieldedIdentifier expression of
    Just (IdentifierString name, _, _) -> Right name
    Nothing -> Left (ModuleEvaluationFailed
      ImportedModuleRequiresSimpleIdentifierType)

requireTotalModuleValue
  :: InterpretedValue
  -> Either InterpretingError ()
requireTotalModuleValue value
  | interpretedTypeIsTotal value = Right ()
  | otherwise = Left (ModuleEvaluationFailed
      ImportedModuleRequiresTotalValue)

importAllBindings
  :: InterpretedValue
  -> Either InterpretingError Scope
importAllBindings value
  | not (interpretedTypeIsTotal value) = invalid
  | not (all isSimpleIdentifier members) = invalid
  | otherwise =
      case namedBindings value of
        Right bindings -> Right bindings
        Left _ -> invalid
  where
    members = case interpretedCanonicalResult value of
      CanonicalMap _ values -> values
      CanonicalConcatenation values -> values
      _ -> []
    isSimpleIdentifier CanonicalSimpleIdentifierType {} = True
    isSimpleIdentifier CanonicalAssignment {} = True
    isSimpleIdentifier _ = False
    invalid = Left (ModuleEvaluationFailed
      ImportAllRequiresTotalMapOfSimpleIdentifierTypes)

scopeValue :: Scope -> [String] -> Either InterpretingError InterpretedValue
scopeValue scope resolving = do
  let names = case lookup "\0this" scope of Just (ScopeMembers values) -> values; _ -> []
  members <- traverse (\name -> simpleIdentifierTypeValue name <$> resolveIdentifier scope resolving name)
    names
  pure (makeAtlasMap 2 members)

exportedBindings :: InterpretedValue -> Either InterpretingError Scope
exportedBindings = namedBindings

publicValue :: InterpretedValue -> Either InterpretingError InterpretedValue
publicValue value = do
  members <- namedMembers value
  pure (makeAtlasMap 2 (map snd (public members)))

namedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
namedMembers value = case interpretedCanonicalResult value of
  CanonicalMap _ members -> traverse field members
  CanonicalConcatenation members -> traverse field members
  member@CanonicalAssignment {} -> (: []) <$> field member
  member@CanonicalSimpleIdentifierType {} -> (: []) <$> field member
  _ -> Left (ModuleEvaluationFailed ImportedModuleRequiresNamedExports)
  where
    field CanonicalSimpleIdentifierType { canonicalIdentifierString = name } =
      (name,) <$> namedAccessValue value name
    field CanonicalAssignment { canonicalAssignmentIdentifierString = name } =
      (name,) <$> namedAccessValue value name
    field _ = Left (ModuleEvaluationFailed ModuleExportRequiresIdentifier)

namedBindings :: InterpretedValue -> Either InterpretingError Scope
namedBindings value = namedMembers value >>= traverse field
  where
    field (name, selected) = do
      payload <- accessValues selected (naturalValue 1)
      pure (name, EvaluatedBinding payload)

lookupModule :: Scope -> String -> Either InterpretingError ModuleSource
lookupModule scope path
  | isStandardLibraryRequest path = Right StdLibModule
  | Just (ModuleCatalog modules) <- lookup "\0imports" scope
  , Just value <- lookup path modules = Right value
  | otherwise = Left (ModuleEvaluationFailed (ModuleNotLoaded path))

moduleScope :: ModuleSource -> Either InterpretingError Scope
moduleScope StdLibModule = standardLibraryInternalScope
moduleScope (ModuleSource _ expression dependencies) = do
  base <- standardScope
  _ <- declaredModuleName expression
  outer <- importScope
    (("\0imports", ModuleCatalog dependencies) : base)
    []
    (resourceBindings expression)
  case namedBeginBlock expression of
    Just (_, declarations, _) -> importScope outer [] declarations
    Nothing -> Right outer

resourceBindings :: Expression -> [Expression]
resourceBindings (Program bindings _) = bindings
resourceBindings _ = []

-- | Source provenance survives eager let evaluation. Ordinary definitions
-- already retain their lexical scope; both use the same reconstruction path.
bindingDefinition :: Binding -> Maybe (Scope, Maybe Expression, Expression)
bindingDefinition (DeferredBinding lexical annotation expressionValue) =
  Just (lexical, annotation, expressionValue)
bindingDefinition (RetainedBinding lexical annotation expressionValue _) =
  Just (lexical, annotation, expressionValue)
bindingDefinition _ = Nothing

bindingKey :: String -> Expression -> String
bindingKey name expressionValue = name <> ":" <> show expressionValue

closureResolver :: Scope -> Resolver
closureResolver scope = resolver
  where
    resolver = Resolver resolve moduleResolver scopeIndex
    scopeIndex expressionValue = do
      index <- either (const Nothing) Just (evalInScope scope [] expressionValue)
      ordinal <- interpretedExplicitOrdinal index >>= (naturalAtOrdinal . snd)
      ScopeMembers names <- lookup "\0this" scope
      case drop (fromIntegral ordinal) names of
        name : _ -> Just name
        [] -> Nothing
    moduleResolver path = case lookupModule scope path >>= moduleScope of
      Right imported -> Just (closureResolver imported)
      Left _ -> Nothing
    resolve [] = Nothing
    resolve ["\0this", name] = resolve [name]
    resolve (name : fields) = do
      binding <- lookup name scope
      case (fields, bindingDefinition binding) of
        ([], Just (lexical, _, expressionValue)) ->
          Just (Dependency (bindingKey name expressionValue)
            (originName name) expressionValue (closureResolver lexical))
        _ -> do
          value <- either (const Nothing) Just (resolveIdentifier scope [] name)
          selected <- either (const Nothing) Just
            (foldM namedAccessValue value fields)
          expressionValue <- either (const Nothing) Just (valueExpression selected)
          pure (Dependency
            (intercalate "." (name : fields) <> ":" <> show expressionValue)
            (intercalate "." (originName name : fields))
            expressionValue emptyResolver)
    originName name
      | Just original <- lookup name
          (concat [names | (_, CanonicalNames names) <- scope]) = original
      | name `elem` standardNames = "Std." <> name
      | otherwise = name
    standardNames =
      ["Any", "Nat", "Int", "String", "StringTemplate", "IdenStr"
      ,"Bool", "true", "false", "nothing", "AST", "Expr", "Block", "Pages"
      ,"NatRange", "IntRange", "NatValRange", "IntValRange", "public"
      ,"from", "range", "if", "begin", "do", "let"]

emptyResolver :: Resolver
emptyResolver = Resolver (const Nothing) (const Nothing) (const Nothing)

-- Primitive leaves name the host registration rather than assuming Std is in
-- scope. Compound values recursively replace the library names in their source.
valueExpression :: InterpretedValue -> Either InterpretingError Expression
valueExpression value = case parseDatra
    ("(" <> renderCanonicalResult (interpretedCanonicalResult value) <> "\n)") of
  Right expressionValue -> Right (explicitPrimitives (normalizeExpression expressionValue))
  Left _ -> Left NoCanonicalStringConversion

explicitPrimitives :: Expression -> Expression
explicitPrimitives expressionValue = case expressionValue of
  IdentifierReference (IdentifierString "true") -> booleanExpression True
  IdentifierReference (IdentifierString "false") -> booleanExpression False
  IdentifierReference (IdentifierString "nothing") -> nothingExpression
  IdentifierReference (IdentifierString "Bool") ->
    EitherType (booleanExpression False) (booleanExpression True)
  BooleanLiteral value -> booleanExpression value
  BooleanType -> EitherType (booleanExpression False) (booleanExpression True)
  NothingLiteral -> nothingExpression
  IdentifierReference (IdentifierString name)
    | name `elem` primitiveNames -> External (AsciiStringLiteral ("datra." <> name))
  NaturalType -> External (AsciiStringLiteral "datra.Nat")
  IntegerType -> External (AsciiStringLiteral "datra.Int")
  StringType -> External (AsciiStringLiteral "datra.String")
  IdentifierValueType -> External (AsciiStringLiteral "datra.IdenStr")
  _ -> mapExpressionChildren explicitPrimitives expressionValue
  where
    nothingExpression = IdentifierOperation (IdentifierString "Nothing") (AtlasMap []) Nothing
    booleanExpression value = IdentifierOperation
      (IdentifierString (if value then "True" else "False"))
      (EllipsisNatural (if value then 1 else 0)) Nothing
    primitiveNames =
      ["Any", "Nat", "Int", "String", "StringTemplate", "IdenStr"
      ,"AST", "Expr", "Block", "Pages", "NatRange", "IntRange"
      ,"NatValRange", "IntValRange", "range", "from", "public"]

-- Signatures themselves must not rely on implicit standard-library names.
signatureSource :: InterpretedValue -> InterpretedValue -> Either InterpretingError String
signatureSource input output = renderSourceExpression <$>
  (FunctionType <$> valueExpression input <*> valueExpression output)
