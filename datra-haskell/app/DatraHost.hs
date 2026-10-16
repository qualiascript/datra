{-# LANGUAGE LambdaCase #-}

module DatraHost
  ( datraHostIdentifier
  , datraHostValue
  , namedMembers
  , publicValue
  ) where

import DatraLanguage.AST
import DatraLanguage.Identifier (public)
import DatraTypes
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import SyntaxDefinitions (absorbFunSequence)

datraHostIdentifier :: String
datraHostIdentifier = "'datra"

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
    , ("public", Right publicFunction)
    , suppliedBody "len" mapLengthValue
    , suppliedBody "from" (nativeRange ValuedIntegerRangeKind)
    , suppliedBody "range" (nativeRange IntegerRangeKind)
    , nativeBody "'datra" "add" $ \arguments -> do
        a <- lookupArgument "a" arguments
        b <- lookupArgument "b" arguments
        addValues a b
    , nativeBody "'datra" "abs" $ \arguments -> do
        value <- lookupArgument "value" arguments
        number <- requireFiniteInteger LeftOperand value
        pure (integerValue (abs number))
    , ("ordinal", Right ordinalMembers)
    , syntaxBody "let" $ \case
        [entry] -> Just (Let (absorbAssignedConcatenation entry))
        _ -> Nothing
    , syntaxBody "val" $ \case
        [entry] -> Just (Val (absorbAssignedConcatenation entry))
        _ -> Nothing
    , syntaxBody "assert" $ \case
        [condition] -> Just (Assert False condition)
        _ -> Nothing
    , syntaxBody "assertHard" $ \case
        [_, condition] -> Just (Assert True condition)
        _ -> Nothing
    , syntaxBody "begin" $ \case
        [entries, result] -> Just (Begin (blockEntries entries) result)
        _ -> Nothing
    , syntaxBody "do" $ \case
        [entries, result] -> Just (FunctionBody (blockEntries entries) result)
        _ -> Nothing
    , syntaxBody "fun" $ \case
        [entry] -> Just (Fun (absorbFunSequence entry))
        _ -> Nothing
    , syntaxBody "if" $ \case
        [condition, yes, no] -> Just (Conditional condition yes no)
        _ -> Nothing
    , syntaxBody "ifThen" $ \case
        [condition, yes] -> Just (Conditional condition yes (AtlasMap []))
        _ -> Nothing
    , syntaxBody "import" $ \case
        [paths, body@FunctionBody {}]
          | Just requested <- importPaths paths
          , not (null requested) -> Just (Import requested body)
        _ -> Nothing
    , syntaxBody "with" $ \case
        [modules, FunctionBody bindings result] -> Just
          (ScopeAccess
            (ArgumentMap (withModuleOperands modules))
            (Begin bindings result))
        _ -> Nothing
    , syntaxBody "in" $ \case
        [value, body] -> Just (In value body)
        _ -> Nothing
    , syntaxBody "of" $ \case
        [source, target] -> Just (Subfederation source target)
        _ -> Nothing
    , syntaxBody "and" $ \case
        [left, right] -> Just (BooleanAnd left right)
        _ -> Nothing
    , syntaxBody "or" $ \case
        [left, right] -> Just (BooleanOr left right)
        _ -> Nothing
    , syntaxBody "not" $ \case
        [value] -> Just (BooleanNot value)
        _ -> Nothing
    ]
  where
    expressionType = syntaxCategoryTypeValue ExpressionAST
    dependentIdentifierType = syntaxCategoryTypeValue DependentIdentifierAST
    dependentDeclarationType = syntaxCategoryTypeValue DeclarationAST
    blockType = syntaxCategoryTypeValue BlockAST
    functionBodyType = syntaxCategoryTypeValue FunctionBodyAST
    syntaxBody name expand =
      (name, Right (makeFunctionBodyValue
        (EvaluatedSyntaxFunctionBody source expand)))
      where
        source = "'datra." <> name
    nativeBody namespace name implementation =
      (name, runtimeBody source invoke)
      where
        source = namespace <> "." <> name
        invoke _ _ preparedCall = do
          result <- implementation (functionPreparedBindings preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    suppliedBody name implementation =
      (name, runtimeBody source invoke)
      where
        source = "'datra." <> name
        invoke _ _ preparedCall = do
          result <- implementation (functionSuppliedArgument preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    runtimeBody source invoke = Right (makeFunctionBodyValue
      (EvaluatedRuntimeFunctionBody source (EvaluatedFunction
        anyTypeValue anyTypeValue Nothing Nothing (Just source) Nothing
        "Any -> Any" Nothing (Just invoke) True)))
    publicFunction = makeFunctionValue (EvaluatedFunction
      anyTypeValue anyTypeValue Nothing Nothing (Just "'datra.public") Nothing
      "Any -> Any"
      (Just (\argument -> Right
        (PreparedFunctionArgument argument argument [])))
      (Just (\_ _ preparedCall -> do
        value <- publicValue (functionPreparedArgument preparedCall)
        pure (EvaluatedFunctionInvocation value Nothing))) False)
    nativeRange kind argument = do
      startValue <- accessValues argument (naturalValue 0)
      endValue <- accessValues argument (naturalValue 1)
      integerLimitRangeValue kind startValue endValue
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

publicValue :: InterpretedValue -> Either InterpretingError InterpretedValue
publicValue value = case namedMapViewForValue value of
  Just named -> namedMapValue <$> selectPublicNamedMapView named
  Nothing -> do
    members <- namedMembers value
    pure (makeAtlasMap 2 (map snd (public members)))

namedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
namedMembers value =
  case namedMapViewForValue value of
    Just named -> do
      members <- namedMapDeclaredMembers named
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
        count <- maybe invalid Right
          (naturalAtOrdinal
            (interpretedMapFinalOrderType (interpretedMap value)))
        members <- traverse memberAt
          (if count == 0 then [] else [0 .. count - 1])
        traverse field members
    invalid = Left (ModuleEvaluationFailed
      ImportedModuleRequiresNamedExports)
    memberAt index = maybe invalid Right
      (interpretedMapValueAt (interpretedMap value) (finiteOrdinal index))
    field member = case simpleIdentifierName member of
      Just name -> Right (name, member)
      Nothing -> Left (ModuleEvaluationFailed ModuleExportRequiresIdentifier)
