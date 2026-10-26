{-# LANGUAGE LambdaCase #-}

module DatraHost
  ( datraHostIdentifier
  , datraHostValue
  , namedMembers
  ) where

import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (..), SyntaxPiece (..), SyntaxTemplate (..) )
import DatraTypes
import DatraOrdinal (finiteOrdinalPositions)
import IntegerRange qualified
import NaturalRange qualified
import SyntaxDefinitions (absorbFunSequence)

datraHostIdentifier :: String
datraHostIdentifier = "'datra"

data RuntimeRangeEndpoint
  = FiniteRangeEndpoint IntegerLimit
  | DirectionRangeEndpoint String

valuedRangeArguments
  :: CanonicalResult
  -> Maybe (Integer, RuntimeRangeEndpoint)
valuedRangeArguments canonical = case canonical of
  CanonicalValuedNaturalRange origin target ->
    case target of
      NaturalRange.FiniteNaturalTarget endpoint -> Just
        ( toInteger origin
        , FiniteRangeEndpoint (FiniteInteger (toInteger endpoint))
        )
      NaturalRange.UpwardsTarget -> Just
        (toInteger origin, DirectionRangeEndpoint "up")
  CanonicalValuedIntegerRange origin target ->
    case target of
      IntegerRange.FiniteIntegerTarget endpoint -> Just
        (origin, FiniteRangeEndpoint (FiniteInteger endpoint))
      IntegerRange.UpwardsIntegerTarget -> Just
        (origin, DirectionRangeEndpoint "up")
      IntegerRange.DownwardsIntegerTarget -> Just
        (origin, DirectionRangeEndpoint "down")
      IntegerRange.AllIntegersTarget -> Nothing
  CanonicalCoalization
      (CanonicalConcatenation
        [finite, CanonicalAsciiString "PosInf"]) -> do
    (origin, DirectionRangeEndpoint "up") <- valuedRangeArguments finite
    Just (origin, FiniteRangeEndpoint PositiveInfinity)
  CanonicalCoalization
      (CanonicalConcatenation
        [finite, CanonicalAsciiString "NegInf"]) -> do
    (origin, DirectionRangeEndpoint "down") <- valuedRangeArguments finite
    Just (origin, FiniteRangeEndpoint NegativeInfinity)
  _ -> Nothing

datraHostValue :: Either InterpretingError InterpretedValue
datraHostValue = do
  natural <- naturalTypeValue
  integer <- integerTypeValue
  character <- charTypeValue
  ordinalMembers <- hostMap
    [ ordinalBinaryBody "sum" ordinalSumValues
    , ordinalBinaryBody "prod" ordinalProductValues
    , ordinalBinaryBody "minus" ordinalMinusValues
    , nativeBody "'datra.ordinal" "exp" $ \arguments -> do
        ordinalValue <- lookupArgument "x" arguments
        power <- lookupArgument "power" arguments
        ordinalExponentValues ordinalValue power
    , ordinalComparisonBody "lt" ordinalLTValues
    , ordinalComparisonBody "lte" ordinalLTEValues
    , ordinalComparisonBody "gt" ordinalGTValues
    , ordinalComparisonBody "gte" ordinalGTEValues
    ]
  hostMap
    [ ("Any", Right anyTypeValue)
    , ("never", Right neverValue)
    , ("Ordinal", Right ordinalTypeValue)
    , ("Nat", Right natural)
    , ("Int", Right integer)
    , ("Char", Right character)
    , ("IdenStr", Right identifierValueTypeValue)
    , ("Expr", Right expressionType)
    , ("DependentIdentifier", Right dependentIdentifierType)
    , ("DependentDeclaration", Right dependentDeclarationType)
    , ("Block", Right blockType)
    , ("FunctionBody", Right functionBodyType)
    , ("Template", Right templateTypeValue)
    , ("SyntaxTemplate", Right syntaxTemplateTypeValue)
    , ("NatRange", Right naturalRangeTypeValue)
    , ("IntRange", Right integerRangeTypeValue)
    , ("NatValRange", Right naturalValuedRangeTypeValue)
    , ("IntValRange", Right integerValuedRangeTypeValue)
    , suppliedBody "len_body" mapLengthValue
    , suppliedInsertionBody "from_body" (RuntimeFunctionInsertion
        (nativeRange ValuedIntegerRangeKind)
        valuedRangePreimage)
    , suppliedInsertionBody "range_body" (RuntimeFunctionInsertion
        (nativeBoundedRange IntegerRangeKind)
        integerLimitRangePreimage)
    , nativeBody "'datra" "add" $ \arguments -> do
        a <- lookupArgument "a" arguments
        b <- lookupArgument "b" arguments
        addValues a b
    , nativeBody "'datra" "abs" $ \arguments -> do
        value <- lookupArgument "value" arguments
        number <- requireFiniteInteger LeftOperand value
        pure (integerValue (abs number))
    , ("ordinal", Right ordinalMembers)
    , syntaxBody "let" (SyntaxFunctionInsertion
        (\case
          [entry] -> Just (Let (absorbAssignedConcatenation entry))
          _ -> Nothing)
        (\case
          Let entry -> Just [entry]
          _ -> Nothing))
    , syntaxBody "val" (SyntaxFunctionInsertion
        (\case
          [entry] -> Just (Val (absorbAssignedConcatenation entry))
          _ -> Nothing)
        (\case
          Val entry -> Just [entry]
          _ -> Nothing))
    , syntaxBody "assert" (SyntaxFunctionInsertion
        (\case
          [condition] -> Just (Assert False condition)
          [_, condition] -> Just (Assert True condition)
          _ -> Nothing)
        (\case
          Assert False condition -> Just [condition]
          _ -> Nothing))
    , syntaxFunction "begin" (SyntaxFunctionInsertion
        (\case
          [entries, result] -> Just (Begin (blockEntries entries) result)
          _ -> Nothing)
        (\case
          Begin entries result -> Just [AtlasMap entries, result]
          _ -> Nothing))
    , syntaxBody "do" (SyntaxFunctionInsertion
        (\case
          [entries, result] -> Just
            (FunctionBody (blockEntries entries) result)
          _ -> Nothing)
        (\case
          FunctionBody entries result -> Just [AtlasMap entries, result]
          _ -> Nothing))
    , syntaxBody "fun" (SyntaxFunctionInsertion
        (\case
          [entry] -> Just (Fun (absorbFunSequence entry))
          _ -> Nothing)
        (\case
          Fun entry -> Just [entry]
          _ -> Nothing))
    , syntaxBody "if" (SyntaxFunctionInsertion
        (\case
          [condition, yes, no] -> Just (Conditional condition yes no)
          [condition, yes] -> Just
            (Conditional condition yes (AtlasMap []))
          _ -> Nothing)
        (\case
          Conditional condition yes no -> Just [condition, yes, no]
          _ -> Nothing))
    , syntaxBody "import" (SyntaxFunctionInsertion
        (\case
          [paths, body@FunctionBody {}]
            | Just requested <- importPaths paths
            , not (null requested) -> Just (Import requested body)
          _ -> Nothing)
        (\case
          Import paths body -> Just
            [AtlasMap (map AsciiStringLiteral paths), body]
          _ -> Nothing))
    , syntaxBody "with" (SyntaxFunctionInsertion
        (\case
          [modules, FunctionBody bindings result] -> Just
            (ScopeAccess
              (ArgumentMap (withModuleOperands modules))
              (Begin bindings result))
          _ -> Nothing)
        (\case
          ScopeAccess (ArgumentMap modules) (Begin bindings result) -> Just
            [ArgumentMap modules, FunctionBody bindings result]
          _ -> Nothing))
    , syntaxBody "of" (SyntaxFunctionInsertion
        (\case
          [source, target] -> Just (Subfederation source target)
          _ -> Nothing)
        (\case
          Subfederation source target -> Just [source, target]
          _ -> Nothing))
    , syntaxBody "and" (SyntaxFunctionInsertion
        (\case
          [left, right] -> Just (BooleanAnd left right)
          _ -> Nothing)
        (\case
          BooleanAnd left right -> Just [left, right]
          _ -> Nothing))
    , syntaxBody "or" (SyntaxFunctionInsertion
        (\case
          [left, right] -> Just (BooleanOr left right)
          _ -> Nothing)
        (\case
          BooleanOr left right -> Just [left, right]
          _ -> Nothing))
    , syntaxBody "not" (SyntaxFunctionInsertion
        (\case
          [value] -> Just (BooleanNot value)
          _ -> Nothing)
        (\case
          BooleanNot value -> Just [value]
          _ -> Nothing))
    ]
  where
    expressionType = syntaxCategoryTypeValue ExpressionAST
    dependentIdentifierType = syntaxCategoryTypeValue DependentIdentifierAST
    dependentDeclarationType = syntaxCategoryTypeValue DeclarationAST
    blockType = syntaxCategoryTypeValue BlockAST
    functionBodyType = syntaxCategoryTypeValue FunctionBodyAST
    syntaxBody name insertion =
      (bodyName, Right (makeFunctionBodyValue
        (EvaluatedSyntaxFunctionBody source insertion)))
      where
        bodyName = name <> "_body"
        source = "'datra." <> bodyName
    syntaxFunction name insertion =
      (name, Right (makeFunctionValue (EvaluatedFunction
        anyTypeValue
        anyTypeValue
        (Just simpleSyntax)
        (Just simpleSyntax)
        (Just source)
        (Just (EvaluatedSyntaxFunctionBody source insertion))
        "Any -> Any"
        Nothing
        Nothing
        True
        Nothing)))
      where
        source = "'datra." <> name
        simpleSyntax :: FunctionSyntax value
        simpleSyntax = FunctionSyntax
          [SyntaxTemplate [SyntaxLiteral name]]
    nativeBody namespace name implementation =
      (name, runtimeBody source Nothing invoke)
      where
        source = namespace <> "." <> name
        invoke _ _ preparedCall = do
          result <- implementation (functionPreparedBindings preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    suppliedBody name implementation =
      suppliedFunctionBody name implementation Nothing
    suppliedInsertionBody name insertion =
      suppliedFunctionBody name
        (applyRuntimeFunction insertion) (Just insertion)
    suppliedFunctionBody name implementation insertion =
      (name, runtimeBody source insertion invoke)
      where
        source = "'datra." <> name
        invoke _ _ preparedCall = do
          result <- implementation (functionSuppliedArgument preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    runtimeBody source insertion invoke = Right (makeFunctionBodyValue
      (EvaluatedRuntimeFunctionBody source (EvaluatedFunction
        anyTypeValue anyTypeValue Nothing Nothing (Just source) Nothing
        "Any -> Any" Nothing (Just invoke) True insertion)))
    nativeRange kind argument = do
      startValue <- accessValues argument (naturalValue 0)
      endValue <- accessValues argument (naturalValue 1)
      integerLimitRangeValue kind startValue endValue
    nativeBoundedRange kind argument = do
      startValue <- accessValues argument (naturalValue 0)
      endValue <- accessValues argument (naturalValue 1)
      end <- requireIntegerLimit RightOperand endValue
      integerLimitRangeValue kind startValue (makeIntegerLimit end)
    valuedRangePreimage value = do
      (origin, endpoint) <- valuedRangeArguments
        (interpretedSemanticResult value)
      endpointValue <- case endpoint of
        FiniteRangeEndpoint limit -> Just (makeIntegerLimit limit)
        DirectionRangeEndpoint direction -> either (const Nothing) Just
          (asciiStringValue direction)
      either (const Nothing) Just
        (makeArgumentMapPreservingSingleton
          [integerValue origin, endpointValue])
    integerLimitRangePreimage value = case interpretedSemanticResult value of
      CanonicalIntegerLimitRange origin target ->
        either (const Nothing) Just
          (makeArgumentMapPreservingSingleton
            [makeIntegerLimit origin, makeIntegerLimit target])
      _ -> Nothing
    lookupArgument name values = maybe
      (Left (FunctionEvaluationFailed (MissingNativeArgument name)))
      Right
      (lookup name values)
    ordinalBinaryBody name operation = nativeBody
      "'datra.ordinal" name $ \arguments -> do
        left <- lookupArgument "x" arguments
        right <- lookupArgument "y" arguments
        operation left right
    ordinalComparisonBody name operation =
      ordinalBinaryBody name $ \left right ->
        booleanValue <$> operation left right
    blockEntries (AtlasMap entries) = entries
    blockEntries (SyntaxBoundary inner) = blockEntries inner
    blockEntries value = [value]
    importPaths value = case value of
      AsciiStringLiteral path -> Just [path]
      AtlasMap paths -> concat <$> traverse importPaths paths
      MapSequence paths -> concat <$> traverse importPaths paths
      MapConcatenation left right ->
        (<>) <$> importPaths left <*> importPaths right
      SyntaxBoundary inner -> importPaths inner
      _ -> Nothing
    withModuleOperands value = case value of
      AtlasMap modules -> modules
      MapSequence modules -> modules
      MapConcatenation left right ->
        withModuleOperands left <> withModuleOperands right
      SyntaxBoundary inner -> withModuleOperands inner
      _ -> [value]
    absorbAssignedConcatenation value = case value of
      MapConcatenation
          (IdentifierOperation name annotation (Just given)) right
        | annotation == given ->
            let assignedValue = MapConcatenation given right
            in IdentifierOperation name assignedValue (Just assignedValue)
      _ -> value

hostMap
  :: [(String, Either InterpretingError InterpretedValue)]
  -> Either InterpretingError InterpretedValue
hostMap entries = do
  fields <- traverse field entries
  pure (makeAtlasMap 2 fields)
  where
    field (name, value) = do
      underlying <- value
      pure (withTrailingIdentifierMarker canonicalValueMarker
        (inferredIdentifierAssignmentValue name underlying))

namedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
namedMembers value =
  case namedMapViewForValue value of
    Just named -> do
      orderType <- namedMapOrderType named
      positions <- maybe invalid Right (finiteOrdinalPositions orderType)
      members <- traverse
        (\position -> namedMapMemberAt named position >>= maybe invalid Right)
        positions
      pure
        [ (namedMemberName member, namedMemberValue member)
        | member <- members
        ]
    Nothing -> case argumentMapMembers value of
      Just members
        | Right named <- traverse field members -> Right named
      _ -> projectedMembers
  where
    projectedMembers = case simpleIdentifierName value of
      Just name -> Right [(name, value)]
      Nothing -> do
        positions <- maybe invalid Right
          (finiteOrdinalPositions
            (interpretedMapFinalOrderType (interpretedMap value)))
        members <- traverse memberAt positions
        traverse field members
    invalid = Left (ModuleEvaluationFailed
      ImportedModuleRequiresNamedExports)
    memberAt position = maybe invalid Right
      (interpretedMapValueAt (interpretedMap value) position)
    field member = case simpleIdentifierName member of
      Just name -> Right (name, member)
      Nothing -> Left (ModuleEvaluationFailed ModuleExportRequiresIdentifier)
