module DatraHost
  ( datraHostIdentifier
  , datraHostValue
  , resolveDatraHostSyntaxInsertion
  ) where

import DatraLanguage.AST
import DatraLanguage.Identifier
  ( canonicalNaturalValue
  )
import DatraHost.Syntax
  ( beginSyntaxInsertion
  , defSyntaxInsertion
  , doSyntaxInsertion
  , funSyntaxInsertion
  , ifSyntaxInsertion
  , letSyntaxInsertion
  , parseNaturalSyntaxInsertion
  , valSyntaxInsertion
  , withSyntaxInsertion
  )
import StringExpression
  ( FunctionSyntax (..)
  , StringExpression (LiteralString)
  )
import DatraTypes

datraHostIdentifier :: String
datraHostIdentifier = "datra"

data DatraHostSyntaxRuntime
  = SyntaxBodyRuntime
  | SyntaxFunctionRuntime

data DatraHostSyntaxDefinition = DatraHostSyntaxDefinition
  { datraHostSyntaxName :: String
  , datraHostSyntaxRuntime :: DatraHostSyntaxRuntime
  , datraHostSyntaxInsertion :: SyntaxFunctionInsertion
  }

datraHostSyntaxDefinitions :: [DatraHostSyntaxDefinition]
datraHostSyntaxDefinitions =
  [ definition "let_body" SyntaxBodyRuntime letSyntaxInsertion
  , definition "def_body" SyntaxBodyRuntime defSyntaxInsertion
  , definition "val_body" SyntaxBodyRuntime valSyntaxInsertion
  , definition "parse_natural" SyntaxBodyRuntime
      parseNaturalSyntaxInsertion
  , definition "begin" SyntaxFunctionRuntime beginSyntaxInsertion
  , definition "do_body" SyntaxBodyRuntime doSyntaxInsertion
  , definition "fun_body" SyntaxBodyRuntime funSyntaxInsertion
  , definition "if_body" SyntaxBodyRuntime ifSyntaxInsertion
  , definition "with_body" SyntaxBodyRuntime withSyntaxInsertion
  ]
  where
    definition = DatraHostSyntaxDefinition

datraHostSyntaxReference :: DatraHostSyntaxDefinition -> Expression
datraHostSyntaxReference definition = ScopeAccess
  (IdentifierReference (SimpleIdentifierString datraHostIdentifier))
  (literalIdentifierExpression (SimpleIdentifierString name))
  where
    name = datraHostSyntaxName definition

resolveDatraHostSyntaxInsertion
  :: Expression
  -> Maybe SyntaxFunctionInsertion
resolveDatraHostSyntaxInsertion source = case
    [ datraHostSyntaxInsertion definition
    | definition <- datraHostSyntaxDefinitions
    , datraHostSyntaxReference definition == source
    ] of
  insertion : _ -> Just insertion
  [] -> Nothing

datraHostValue :: Either InterpretingError InterpretedValue
datraHostValue = do
  natural <- naturalTypeValue
  integer <- integerTypeValue
  character <- charTypeValue
  let naturalLiteral = naturalLiteralValue natural
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
  hostMap $
    [ ("Any", Right anyTypeValue)
    , ("never", Right neverValue)
    , ("Ordinal", Right ordinalTypeValue)
    , ("Nat", Right natural)
    , ("Int", Right integer)
    , ("Infinity", Right (makeIntegerLimit PositiveInfinity))
    , ("Char", Right character)
    , ("Expr", Right expressionType)
    , ("DependentArgument", Right dependentArgumentType)
    , ("IdentifierExpr", Right identifierExpressionType)
    , ("NaturalLiteral", Right naturalLiteral)
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
    ] <> map syntaxEntry datraHostSyntaxDefinitions
  where
    expressionType = syntaxCategoryTypeValue ExpressionAST
    dependentArgumentType = syntaxCategoryTypeValue DependentArgumentAST
    identifierExpressionType = syntaxCategoryTypeValue IdentifierExpressionAST
    dependentDeclarationType = syntaxCategoryTypeValue DeclarationAST
    blockType = syntaxCategoryTypeValue BlockAST
    functionBodyType = syntaxCategoryTypeValue FunctionBodyAST
    syntaxEntry definition = case datraHostSyntaxRuntime definition of
      SyntaxBodyRuntime -> syntaxBody definition
      SyntaxFunctionRuntime -> syntaxFunction definition
    syntaxBody definition =
      (name, Right (makeFunctionBodyValue
        (EvaluatedSyntaxFunctionBody source insertion)))
      where
        name = datraHostSyntaxName definition
        insertion = datraHostSyntaxInsertion definition
        source = datraMemberSource [name]
    syntaxFunction definition =
      typedSyntaxFunction name anyTypeValue anyTypeValue insertion
      where
        name = datraHostSyntaxName definition
        insertion = datraHostSyntaxInsertion definition
    typedSyntaxFunction name domain codomain insertion =
      (name, Right (makeFunctionValue (EvaluatedFunction
        domain
        codomain
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
          [[StringTemplateInterpolation (LiteralString name)]]
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
    naturalLiteralValue natural =
      stringFederationValue naturalLiteralCodec natural

    naturalLiteralCodec = CanonicalStringCodec
      { renderCanonicalString = maybe "" show . interpretedInteger
      , decodeCanonicalString =
          maybe [] (pure . naturalValue) . canonicalNaturalValue
      }

    -- Native identities are represented by the same structural access tree
    -- used by the surface language.  Rendering is presentation only; member
    -- lookup never parses or compares this text.
    datraMemberSource members = FunctionSource
      (foldl access
        (IdentifierReference (SimpleIdentifierString datraHostIdentifier))
        members)
      where
        access source name = ScopeAccess source
          (literalIdentifierExpression (SimpleIdentifierString name))
    anyFunctionSource = FunctionSource
      (FunctionType AnyType AnyType)

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
