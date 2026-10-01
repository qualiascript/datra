{-# LANGUAGE LambdaCase #-}

-- | Scope-aware declarative syntax expansion over an already-read AST.
-- Source layout has disappeared at this boundary: application spines are
-- matched directly, while an 'AtlasMap' supplies the contextual boundary for
-- block captures.
module SyntaxRewriting
  ( SyntaxRewriteFailure (..)
  , rewriteExplicitSyntax
  , rewriteImplicitSyntax
  ) where

import BlockScope (bindingNames)
import DatraLanguage.AST
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , declarationRules
  )
import SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , matchSyntaxRulesWith
  )

data SyntaxRewriteFailure
  = MissingImplicitBlockResult
  | SyntaxRewriteMatchFailure SyntaxTemplateMatchFailure
  deriving (Eq, Show)

data RewriteEnvironment = RewriteEnvironment
  { rewriteRules :: [SyntaxRule]
  , rewriteDeclarations :: [Expression]
  , rewriteImports :: [(String, [SyntaxRule])]
  , rewriteStrictCaptures :: Bool
  }

type CaptureHole =
  Bool
  -> [Expression]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

rewriteExplicitSyntax
  :: CaptureHole
  -> [SyntaxRule]
  -> [Expression]
  -> [(String, [SyntaxRule])]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteExplicitSyntax capture initialRules initialDeclarations imports value =
  rewriteStandalone capture environment value
  where
    environment = RewriteEnvironment
      initialRules initialDeclarations imports True

rewriteImplicitSyntax
  :: CaptureHole
  -> [SyntaxRule]
  -> [Expression]
  -> [(String, [SyntaxRule])]
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
rewriteImplicitSyntax capture initialRules initialDeclarations imports entries = do
  resolveImplicitBlock capture initial [] entries
  where
    initial = RewriteEnvironment initialRules initialDeclarations imports True

resolveImplicitBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
resolveImplicitBlock capture initial = go initial
  where
    go environment rewrittenPrefix remaining =
      tryRules environment rewrittenPrefix remaining
        >>= \case
          Just expressionValue -> Right expressionValue
          Nothing -> case remaining of
            [] -> Left MissingImplicitBlockResult
            entry : rest -> do
              (rewritten, trailing) <-
                rewriteWithTail False capture environment entry rest
              let next = introduceDeclaration environment rewritten
              go next (rewrittenPrefix <> [rewritten]) trailing

    tryRules environment rewrittenPrefix remaining =
      firstSuccessful
        [ implicitRule environment rewrittenPrefix remaining rule shape
        | rule <- rewriteRules environment
        , Just shape <- [blockShape rule]
        ]

    firstSuccessful [] = Right Nothing
    firstSuccessful (candidate : rest) = do
      result <- candidate
      case result of
        Just value -> Right (Just value)
        Nothing -> firstSuccessful rest

    implicitRule environment rewrittenPrefix remaining rule
        (prefix, delimiter) =
      consumeBlock capture environment delimiter [] remaining >>= \case
        Nothing -> Right Nothing
        Just (rewrittenSuffix, nested, rawResult, trailing) -> do
          (result, finalTrailing) <-
            rewriteWithTail True capture nested rawResult trailing
          let block = rewrittenPrefix <> rewrittenSuffix
              candidate = applicationFrom
                (map literalExpression prefix
                  <> [ AtlasMap block
                     , literalExpression delimiter
                     , result
                     ])
              captureInScope kind captured =
                capture (rewriteStrictCaptures nested)
                  (rewriteDeclarations nested) kind captured
          case matchSyntaxRulesWith captureInScope [rule] candidate of
            Right (Begin bindings finalResult)
              | null finalTrailing ->
                  Right (Just (Program bindings finalResult))
            Right _ -> Right Nothing
            Left NoMatchingSyntaxTemplate -> Right Nothing
            Left failure -> Left (SyntaxRewriteMatchFailure failure)

rewriteSequence
  :: CaptureHole
  -> RewriteEnvironment
  -> [Expression]
  -> Either SyntaxRewriteFailure ([Expression], RewriteEnvironment)
rewriteSequence capture initial rawEntries = fixedPoint []
  where
    fixedPoint recursiveDeclarations = do
      let recursiveEnvironment strict = (foldl introduceDeclaration
            initial recursiveDeclarations)
              { rewriteStrictCaptures = strict }
      (rewritten, tentativeEnvironment) <-
        pass [] (recursiveEnvironment False) rawEntries
      let discovered = filter isLetDeclaration rewritten
      if discovered == recursiveDeclarations
        then if not (rewriteStrictCaptures initial)
          then Right (rewritten, tentativeEnvironment)
          else do
            (strictlyRewritten, strictEnvironment) <-
              strictPass rewritten 0 []
                (recursiveEnvironment True) rawEntries
            Right (strictlyRewritten, strictEnvironment)
        else fixedPoint discovered

      where
        -- Let declarations are visible throughout their block, but they retain
        -- their source positions when their lexical scopes are assembled.
        -- Moving them in front of preceding ordinary declarations makes a
        -- recursive target such as Int lose access to an earlier Maybe.
        strictPass _ _ reversed environment [] =
          Right (reverse reversed, environment)
        strictPass stable position reversed environment (entry : remaining) = do
          let scoped = environment
                { rewriteDeclarations = scopedDeclarations position stable
                }
          (rewrittenEntry, trailing) <-
            rewriteWithTail False capture scoped entry remaining
          let next = introduceDeclaration scoped rewrittenEntry
          strictPass stable (position + 1)
            (rewrittenEntry : reversed) next trailing

        declarationsAt position = map snd . filter visible . zip [0 :: Int ..]
          where
            visible (index, declaration) =
              index < position || isLetDeclaration declaration

        scopedDeclarations position stable =
          filter (not . shadowsOuter) (rewriteDeclarations initial) <> local
          where
            local = declarationsAt position stable
            localNames = concatMap bindingNames local
            shadowsOuter declaration = any (`elem` localNames)
              (bindingNames declaration)

    pass reversed environment [] = Right (reverse reversed, environment)
    pass reversed environment (entry : remaining) = do
      (rewritten, trailing) <-
        rewriteWithTail False capture environment entry remaining
      let next = introduceDeclaration environment rewritten
      pass (rewritten : reversed) next trailing

    isLetDeclaration Let {} = True
    isLetDeclaration _ = False

rewriteStandalone
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteStandalone capture environment value = do
  (rewritten, _) <- rewriteWithTail False capture environment value []
  pure rewritten

rewriteWithTail
  :: Bool
  -> CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
rewriteWithTail allowNestedContinuation capture environment value trailing = do
  blockMatch <- matchEmbeddedBlock capture environment value trailing
  case blockMatch of
    Just (rewritten, remaining) ->
      rewriteAfterBlock allowNestedContinuation capture environment
        rewritten remaining
    Nothing -> rewriteAfterBlock allowNestedContinuation capture environment
      value trailing

rewriteAfterBlock
  :: Bool
  -> CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
rewriteAfterBlock allowNestedContinuation capture environment value trailing =
  case value of
    IdentifierOperation name annotation given -> do
      let selected = maybe annotation id given
      (rewrittenValue, remaining) <-
        if allowNestedContinuation
          then rewriteWithTail True capture environment selected trailing
          else rewriteDeclaredValue selected
      let rewritten = case given of
            Nothing -> IdentifierOperation name rewrittenValue Nothing
            Just original
              | original == annotation ->
                  IdentifierOperation name rewrittenValue (Just rewrittenValue)
              | otherwise -> IdentifierOperation name annotation
                  (Just rewrittenValue)
      finish rewritten remaining
    IdentifierTemplateOperation parts annotation given -> do
      let selected = maybe annotation id given
      (rewrittenValue, remaining) <-
        if allowNestedContinuation
          then rewriteWithTail True capture environment selected trailing
          else rewriteDeclaredValue selected
      let rewritten = case given of
            Nothing -> IdentifierTemplateOperation parts rewrittenValue Nothing
            Just original
              | original == annotation ->
                  IdentifierTemplateOperation parts rewrittenValue
                    (Just rewrittenValue)
              | otherwise -> IdentifierTemplateOperation parts annotation
                  (Just rewrittenValue)
      finish rewritten remaining
    FunctionType domain codomain
      | allowNestedContinuation -> do
          rewrittenDomain <- rewriteStandalone capture environment domain
          (rewrittenCodomain, remaining) <-
            rewriteWithTail True capture environment codomain trailing
          finish (FunctionType rewrittenDomain rewrittenCodomain) remaining
    Fun signature
      | allowNestedContinuation -> do
          (rewrittenSignature, remaining) <-
            rewriteWithTail True capture environment signature trailing
          finish (Fun rewrittenSignature) remaining
    AtlasMap entries -> do
      rewritten <- traverse (rewriteStandalone capture environment) entries
      finish (sequenceExpression rewritten) trailing
    ArgumentMap entries -> do
      rewritten <- traverse (rewriteStandalone capture environment) entries
      finish (argumentExpression rewritten) trailing
    Begin bindings result -> do
      (rewrittenBindings, nested) <-
        rewriteSequence capture environment bindings
      rewrittenResult <- rewriteStandalone capture nested result
      pure (Begin rewrittenBindings rewrittenResult, trailing)
    FunctionBody bindings result -> do
      (rewrittenBindings, nested) <-
        rewriteSequence capture environment bindings
      rewrittenResult <- rewriteStandalone capture nested result
      pure (FunctionBody rewrittenBindings rewrittenResult, trailing)
    Program bindings result -> do
      (rewrittenBindings, nested) <-
        rewriteSequence capture environment bindings
      rewrittenResult <- rewriteStandalone capture nested result
      pure (Program rewrittenBindings rewrittenResult, trailing)
    _ -> finish value trailing
  where
    rewriteDeclaredValue selected
      | canReceiveFunctionBody selected = do
          (candidate, remaining) <-
            rewriteWithTail True capture environment selected trailing
          if length remaining < length trailing
              && containsFunctionImplementation candidate
            then pure (candidate, remaining)
            else standalone selected
      | otherwise = standalone selected
    standalone selected = do
      rewritten <- rewriteStandalone capture environment selected
      pure (rewritten, trailing)
    finish expressionValue remaining = do
      attached <- attachTrailingFunctionBody capture environment expressionValue
      matched <- matchOrdinarySyntax capture environment attached
      rewrittenChildren <- rewriteChildren capture environment matched
      final <- attachTrailingFunctionBody capture environment rewrittenChildren
      pure (final, remaining)

canReceiveFunctionBody :: Expression -> Bool
canReceiveFunctionBody FunctionType {} = True
canReceiveFunctionBody (Fun signature) = canReceiveFunctionBody signature
canReceiveFunctionBody _ = False

containsFunctionImplementation :: Expression -> Bool
containsFunctionImplementation MapSpecification {} = True
containsFunctionImplementation (Fun signature) =
  containsFunctionImplementation signature
containsFunctionImplementation _ = False

rewriteChildren
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteChildren capture environment value =
  case value of
    MapAccess (AtlasMap [binder, body]) insertion
      | Just declaration <- dependentBinderDeclaration binder -> do
          rewrittenBinder <- rewriteStandalone capture environment binder
          let nested = introduceDeclaration environment declaration
          rewrittenBody <- rewriteStandalone capture nested body
          rewrittenInsertion <-
            rewriteStandalone capture environment insertion
          pure (MapAccess
            (AtlasMap [rewrittenBinder, rewrittenBody])
            rewrittenInsertion)
    _ -> traverseExpressionChildren
      (rewriteStandalone capture environment) value

dependentBinderDeclaration :: Expression -> Maybe Expression
dependentBinderDeclaration binder = case binder of
  WithBinding name _ bound ->
    Just (IdentifierOperation name bound Nothing)
  ForBinding name _ bound ->
    Just (IdentifierOperation name bound Nothing)
  _ -> Nothing

attachTrailingFunctionBody
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
attachTrailingFunctionBody capture environment value =
  case value of
    FunctionType domain codomain ->
      case trailingFunctionBody codomain of
        Just (resultType, body) ->
          pure (MapSpecification body (FunctionType domain resultType))
        Nothing -> pure value
    Fun signature -> Fun <$>
      attachTrailingFunctionBody capture environment signature
    _ -> case applicationSpine value of
      (function, arguments)
        | not (null arguments)
        , body@FunctionBody {} <- last arguments -> do
            signature <- rewriteStandalone capture environment
              (applicationFrom (function : init arguments))
            pure (maybe value id (implementedFunction body signature))
      _ -> pure value

trailingFunctionBody :: Expression -> Maybe (Expression, Expression)
trailingFunctionBody value =
  case applicationSpine value of
    (function, arguments)
      | not (null arguments)
      , body@FunctionBody {} <- last arguments ->
          Just (applicationFrom (function : init arguments), body)
    _ -> Nothing

implementedFunction :: Expression -> Expression -> Maybe Expression
implementedFunction body (Fun signature)
  | acceptsFunctionBody signature =
      Just (Fun (MapSpecification body signature))
implementedFunction body signature
  | acceptsFunctionBody signature = Just (MapSpecification body signature)
implementedFunction _ _ = Nothing

acceptsFunctionBody :: Expression -> Bool
acceptsFunctionBody FunctionType {} = True
acceptsFunctionBody SyntaxType {} = True
acceptsFunctionBody _ = False

matchOrdinarySyntax
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
matchOrdinarySyntax capture environment value =
  case matchSyntaxRulesWith captureInScope (rewriteRules environment) value of
    Right rewritten -> Right rewritten
    Left NoMatchingSyntaxTemplate -> Right value
    Left failure -> Left (SyntaxRewriteMatchFailure failure)
  where
    captureInScope kind captured =
      capture (rewriteStrictCaptures environment)
        (rewriteDeclarations environment) kind captured

matchEmbeddedBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Maybe (Expression, [Expression]))
matchEmbeddedBlock capture environment = matchWithResult id
  where
    matchWithResult wrapResult value trailing = do
      direct <- firstSuccessful
        [ attempt wrapResult value trailing rule start
        | rule <- rewriteRules environment
        , Just (prefix, _) <- [blockShape rule]
        , start <- matchingStarts prefix (applicationPhrase value)
        ]
      case direct of
        Just result -> Right (Just result)
        Nothing -> case leftInfixContext value of
          Just (left, rebuildResult) ->
            matchWithResult (wrapResult . rebuildResult) left trailing
          Nothing -> Right Nothing

    firstSuccessful [] = Right Nothing
    firstSuccessful (candidate : rest) = do
      matched <- candidate
      case matched of
        Just result -> Right (Just result)
        Nothing -> firstSuccessful rest

    attempt wrapResult value trailing rule start =
      case blockShape rule of
        Nothing -> Right Nothing
        Just (prefix, delimiter) -> do
          let phrase = applicationPhrase value
              afterPrefix = drop (start + length prefix) phrase
              before = take start phrase
          consumeBlock capture environment delimiter afterPrefix trailing
            >>= \case
            Nothing -> Right Nothing
            Just (block, nested, rawResult, afterBlock) -> do
              (result, remaining) <-
                rewriteWithTail True capture nested
                  (wrapResult rawResult) afterBlock
              let candidate = applicationFrom
                    (map literalExpression prefix
                      <> [ AtlasMap block
                         , literalExpression delimiter
                         , result
                         ])
                  captureInScope kind captured =
                    capture (rewriteStrictCaptures nested)
                      (rewriteDeclarations nested) kind captured
              case matchSyntaxRulesWith captureInScope [rule] candidate of
                Left NoMatchingSyntaxTemplate -> Right Nothing
                Left failure -> Left (SyntaxRewriteMatchFailure failure)
                Right expanded -> Right (Just
                  (applicationFrom (before <> [expanded]), remaining))

-- Infix operators are read before syntax templates only as a temporary tree.
-- If a block begins in the left operand, everything to its right still belongs
-- to the block's result expression. Thread that context into the result rather
-- than allowing the provisional operator tree to become an AST boundary.
leftInfixContext
  :: Expression
  -> Maybe (Expression, Expression -> Expression)
leftInfixContext value = case value of
  EitherType left right -> Just (left, (`EitherType` right))
  MaybeThen left right -> Just (left, (`MaybeThen` right))
  Addition left right -> Just (left, (`Addition` right))
  Subtraction left right -> Just (left, (`Subtraction` right))
  Subfederation left right -> Just (left, (`Subfederation` right))
  Equality left right -> Just (left, (`Equality` right))
  Inequality left right -> Just (left, (`Inequality` right))
  LessThan left right -> Just (left, (`LessThan` right))
  LessThanOrEqual left right -> Just (left, (`LessThanOrEqual` right))
  GreaterThan left right -> Just (left, (`GreaterThan` right))
  GreaterThanOrEqual left right -> Just (left, (`GreaterThanOrEqual` right))
  BooleanAnd left right -> Just (left, (`BooleanAnd` right))
  BooleanOr left right -> Just (left, (`BooleanOr` right))
  Multiplication left right -> Just (left, (`Multiplication` right))
  Exponentiation left right -> Just (left, (`Exponentiation` right))
  MapConcatenation left right -> Just (left, (`MapConcatenation` right))
  MapAccess left right -> Just (left, (`MapAccess` right))
  MapSpecification left right -> Just (left, (`MapSpecification` right))
  Overload left right -> Just (left, (`Overload` right))
  SafeOverload left right -> Just (left, (`SafeOverload` right))
  MapExpansion left right -> Just (left, (`MapExpansion` right))
  SuperEllipsisRange left right -> Just (left, (`SuperEllipsisRange` right))
  SyntaxType left right -> Just (left, (`SyntaxType` right))
  FunctionType left right -> Just (left, (`FunctionType` right))
  _ -> Nothing

blockShape :: SyntaxRule -> Maybe ([String], String)
blockShape rule =
  case break isBlockHole
      (syntaxTemplatePieces (syntaxTemplate rule)) of
    (prefix, SyntaxHole BlockSyntaxHole
        : SyntaxLiteral delimiter
        : [SyntaxHole ExpressionSyntaxHole]) ->
      (, delimiter) <$> traverse literal prefix
    _ -> Nothing
  where
    isBlockHole (SyntaxHole BlockSyntaxHole) = True
    isBlockHole _ = False
    literal (SyntaxLiteral text) = Just text
    literal _ = Nothing

matchingStarts :: [String] -> [Expression] -> [Int]
matchingStarts prefix values =
  [ position
  | position <- [0 .. length values - length prefix]
  , and (zipWith matchesLiteral prefix (drop position values))
  ]

consumeBlock
  :: CaptureHole
  -> RewriteEnvironment
  -> String
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure
      (Maybe ([Expression], RewriteEnvironment, Expression, [Expression]))
consumeBlock capture initial = go [] initial
  where
    go reversed environment delimiter current trailing =
      case splitAtDelimiter delimiter current of
        Just (beforeDelimiter, resultTokens)
          | not (null resultTokens) -> do
              let prefix = maybe [] (: [])
                    (applicationFromMaybe beforeDelimiter)
                  collected = reverse reversed <> prefix
              (rewrittenBlock, finalNested) <-
                rewriteSequence capture initial collected
              Right (Just
                ( rewrittenBlock
                , finalNested
                , applicationFrom resultTokens
                , trailing
                ))
        _ -> case applicationFromMaybe current of
          Just entry -> do
            let tentative = environment { rewriteStrictCaptures = False }
            (rewritten, remaining) <-
              rewriteWithTail False capture tentative entry trailing
            let consumedCount = length trailing - length remaining
                consumed = entry : take consumedCount trailing
                nested = introduceDeclaration tentative rewritten
            go (reverse consumed <> reversed) nested delimiter [] remaining
          Nothing -> case trailing of
            [] -> Right Nothing
            entry : remaining ->
              go reversed environment delimiter
                (applicationPhrase entry) remaining

splitAtDelimiter
  :: String
  -> [Expression]
  -> Maybe ([Expression], [Expression])
splitAtDelimiter literal = go []
  where
    go _ [] = Nothing
    go reversed (value : remaining) =
      case stripLeadingLiteral literal value of
        Just suffix -> Just (reverse reversed, suffix <> remaining)
        Nothing -> go (value : reversed) remaining

-- A delimiter begins a source expression even when the neutral reader has
-- already folded a following symbolic infix operator around it. Recovering
-- that left edge keeps block matching independent of the old operator
-- precedence tree; the operator itself remains around the captured result and
-- is interpreted only after the declarative syntax has been expanded.
stripLeadingLiteral :: String -> Expression -> Maybe [Expression]
stripLeadingLiteral literal value =
  case applicationSpine value of
    (IdentifierReference (IdentifierString name), arguments)
      | name == literal -> Just arguments
    _ -> do
      (left, rebuild) <- leftInfixContext value
      suffix <- stripLeadingLiteral literal left
      case suffix of
        [] -> Nothing
        values -> Just [rebuild (applicationFrom values)]

introduceDeclaration :: RewriteEnvironment -> Expression -> RewriteEnvironment
introduceDeclaration environment entry = environment
  { rewriteRules = retained <> introduced
  , rewriteDeclarations = retainedDeclarations <> [entry]
  }
  where
    names = bindingNames entry
    retained = filter ((`notElem` names) . syntaxName)
      (rewriteRules environment)
    introduced = declarationRules entry <> aliasRules entry
      <> importRules entry
    retainedDeclarations = filter
      (null . filter (`elem` names) . bindingNames)
      (rewriteDeclarations environment)
    aliasRules expressionValue = case expressionValue of
      IdentifierOperation (IdentifierString name) _ (Just
          (IdentifierReference (IdentifierString target))) ->
        [ rule { syntaxName = name }
        | rule <- rewriteRules environment
        , syntaxName rule == target
        ]
      _ -> []
    importRules (Import True path) =
      maybe [] id (lookup path (rewriteImports environment))
    importRules _ = []

sequenceExpression :: [Expression] -> Expression
sequenceExpression [] = AtlasMap []
sequenceExpression [value] = value
sequenceExpression values = AtlasMap values

argumentExpression :: [Expression] -> Expression
argumentExpression [] = AtlasMap []
argumentExpression [value] = value
argumentExpression values = ArgumentMap values

applicationPhrase :: Expression -> [Expression]
applicationPhrase value =
  case applicationSpine value of
    (function, arguments) -> function : arguments

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining

applicationFromMaybe :: [Expression] -> Maybe Expression
applicationFromMaybe [] = Nothing
applicationFromMaybe values = Just (applicationFrom values)

literalExpression :: String -> Expression
literalExpression = IdentifierReference . IdentifierString

matchesLiteral :: String -> Expression -> Bool
matchesLiteral literal (IdentifierReference (IdentifierString value)) =
  literal == value
matchesLiteral _ _ = False
