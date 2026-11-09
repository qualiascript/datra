{-# LANGUAGE LambdaCase #-}

module DatraHost
  ( datraHostIdentifier
  , datraHostValue
  ) where

import DatraLanguage.AST
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.DependentDeclaration
  ( applyDeclarationModifier
  , removeDeclarationModifier
  )
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (..), SyntaxPiece (..), SyntaxTemplate (..) )
import DatraTypes

datraHostIdentifier :: String
datraHostIdentifier = "datra"

datraHostValue :: Either InterpretingError InterpretedValue
datraHostValue = do
  natural <- naturalTypeValue
  integer <- integerTypeValue
  character <- charTypeValue
  ordinalMembers <- hostMap
    [ ordinalBinaryBody "sum" ordinalSumValues
    , ordinalBinaryBody "prod" ordinalProductValues
    , ordinalBinaryBody "minus" ordinalMinusValues
    , nativeBody ["ordinal"] "exp"
        (binaryArgument ordinalExponentValues)
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
    , ("Infinity", Right (makeIntegerLimit PositiveInfinity))
    , ("Char", Right character)
    , ("Expr", Right expressionType)
    , ("DependentArgument", Right dependentArgumentType)
    , ("IdentifierLiteral", Right identifierLiteralType)
    , ("DependentDeclaration", Right dependentDeclarationType)
    , ("Block", Right blockType)
    , ("FunctionBody", Right functionBodyType)
    , ("NatRange", Right naturalRangeTypeValue)
    , ("IntRange", Right integerRangeTypeValue)
    , ("NatValRange", Right naturalValuedRangeTypeValue)
    , ("IntValRange", Right integerValuedRangeTypeValue)
    , suppliedBody "len_body" mapLengthValue
    , suppliedInsertionBody "from_body" valuedIntegerRangeInsertion
    , suppliedInsertionBody "range_body" boundedIntegerRangeInsertion
    , nativeBody [] "add" (binaryArgument addValues)
    , nativeBody [] "of_body" (binaryArgument subfederationValues)
    , nativeBody [] "and_body" (binaryArgument booleanAndValues)
    , nativeBody [] "or_body" (binaryArgument booleanOrValues)
    , nativeBody [] "not_body" (unaryArgument booleanNotValue)
    , nativeBody [] "abs" $ \argument -> do
        value <- argumentAt 0 argument
        number <- requireFiniteInteger value
        pure (integerValue (abs number))
    , ("ordinal", Right ordinalMembers)
    , syntaxBody "let_body" (modifierBody DeclarationLet)
    , syntaxBody "def_body" (modifierBody DeclarationDef)
    , syntaxBody "val_body" (modifierBody DeclarationVal)
    , syntaxFunction "begin" (SyntaxFunctionInsertion
        (\case
          [entries, result] -> Just
            (SyntaxBegin (blockExpressions entries) result)
          _ -> Nothing)
        (\case
          Begin entries result -> Just
            [AtlasMap (map DeclarationExpression entries), result]
          _ -> Nothing))
    , syntaxBody "do_body" (SyntaxFunctionInsertion
        (\case
          [entries, result] -> Just
            (SyntaxFunctionBody (blockExpressions entries) result)
          _ -> Nothing)
        (\case
          FunctionBody entries result -> Just
            [AtlasMap (map DeclarationExpression entries), result]
          _ -> Nothing))
    , syntaxBody "fun_body" (expressionSyntaxInsertion
        (\case
          [entry] -> Just (Fun entry)
          _ -> Nothing)
        (\case
          Fun entry -> Just [entry]
          _ -> Nothing))
    , syntaxBody "if_body" (expressionSyntaxInsertion
        (\case
          [condition, yes, no] -> Just (Conditional condition yes no)
          [condition, yes] -> Just
            (Conditional condition yes (AtlasMap []))
          _ -> Nothing)
        (\case
          Conditional condition yes no -> Just [condition, yes, no]
          _ -> Nothing))
    , syntaxBody "import_body" (expressionSyntaxInsertion
        (\case
          [paths, body@FunctionBody {}]
            | Just requested <- importPaths paths
            , not (null requested) -> Just (Import requested body)
          _ -> Nothing)
        (\case
          Import paths body -> Just
            [AtlasMap (map AsciiStringLiteral paths), body]
          _ -> Nothing))
    , syntaxBody "with_body" (expressionSyntaxInsertion
        (\case
          [modules, FunctionBody bindings result] -> Just
            (ScopeAccess
              (ArgumentativeMap (withModuleOperands modules))
              (Begin bindings result))
          _ -> Nothing)
        (\case
          ScopeAccess (ArgumentativeMap modules) (Begin bindings result) -> Just
            [ArgumentativeMap modules, FunctionBody bindings result]
          _ -> Nothing))
    ]
  where
    expressionSyntaxInsertion apply preimage = SyntaxFunctionInsertion
      (fmap SyntaxExpression . apply)
      preimage
    expressionType = syntaxCategoryTypeValue ExpressionAST
    dependentArgumentType = syntaxCategoryTypeValue DependentArgumentAST
    identifierLiteralType = syntaxCategoryTypeValue IdentifierLiteralAST
    dependentDeclarationType = syntaxCategoryTypeValue DeclarationAST
    blockType = syntaxCategoryTypeValue BlockAST
    functionBodyType = syntaxCategoryTypeValue FunctionBodyAST
    syntaxBody name insertion =
      (name, Right (makeFunctionBodyValue
        (EvaluatedSyntaxFunctionBody source insertion)))
      where
        source = datraMemberSource [name]
    syntaxFunction name insertion =
      (name, Right (makeFunctionValue (EvaluatedFunction
        anyTypeValue
        anyTypeValue
        (Just simpleSyntax)
        (Just simpleSyntax)
        (Just source)
        (Just (EvaluatedSyntaxFunctionBody source insertion))
        anyFunctionSource
        Nothing
        Nothing
        True
        Nothing)))
      where
        source = datraMemberSource [name]
        simpleSyntax :: FunctionSyntax value
        simpleSyntax = FunctionSyntax
          [SyntaxTemplate [SyntaxLiteral name]]
    nativeBody namespace name implementation =
      (name, runtimeBody source Nothing invoke)
      where
        source = datraMemberSource (namespace <> [name])
        invoke _ _ preparedCall = do
          result <- implementation (functionPreparedArgument preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    suppliedBody name implementation =
      suppliedFunctionBody name implementation Nothing
    suppliedInsertionBody name insertion =
      suppliedFunctionBody name
        (applyRuntimeFunction insertion) (Just insertion)
    suppliedFunctionBody name implementation insertion =
      (name, runtimeBody source insertion invoke)
      where
        source = datraMemberSource [name]
        invoke _ _ preparedCall = do
          result <- implementation (functionSuppliedArgument preparedCall)
          pure (EvaluatedFunctionInvocation result Nothing)
    runtimeBody source insertion invoke = Right (makeFunctionBodyValue
      (EvaluatedRuntimeFunctionBody source (EvaluatedFunction
        anyTypeValue anyTypeValue Nothing Nothing (Just source) Nothing
        anyFunctionSource Nothing (Just invoke) True insertion)))
    argumentAt position argument =
      accessValues argument (naturalValue position)
    binaryArgument operation argument = do
      left <- argumentAt 0 argument
      right <- argumentAt 1 argument
      operation left right
    unaryArgument operation argument =
      argumentAt 0 argument >>= operation
    ordinalBinaryBody name operation = nativeBody
      ["ordinal"] name (binaryArgument operation)
    ordinalComparisonBody name operation =
      ordinalBinaryBody name $ \left right ->
        booleanValue <$> operation left right
    blockExpressions (AtlasMap entries) = entries
    blockExpressions (SyntaxBoundary inner) = blockExpressions inner
    blockExpressions value = [value]
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
          (MapSpecification given (DependentArgument name Nothing)) right ->
            let assignedValue = MapConcatenation given right
            in MapSpecification assignedValue
              (DependentArgument name Nothing)
      _ -> value
    modifierBody modifier = expressionSyntaxInsertion
      (\case
        [entry] -> applyDeclarationModifier modifier
          (absorbAssignedConcatenation entry)
        _ -> Nothing)
      (removeDeclarationModifier modifier)

    -- Native identities are represented by the same structural access tree
    -- used by the surface language.  Rendering is presentation only; member
    -- lookup never parses or compares this text.
    datraMemberSource members = renderSourceExpression
      (foldl access
        (IdentifierReference (IdentifierString datraHostIdentifier))
        members)
      where
        access source name = ScopeAccess source
          (IdentifierReference (IdentifierString name))
    anyFunctionSource = renderSourceExpression
      (FunctionType anyMember anyMember)
      where
        anyMember = ScopeAccess
          (IdentifierReference (IdentifierString datraHostIdentifier))
          (IdentifierReference (IdentifierString "Any"))

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
