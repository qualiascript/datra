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

import Control.Applicative ((<|>))
import BlockScope (bindingNames)
import Data.List (nub)
import DatraLanguage.AST
import DatraLanguage.Identifier (public)
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import SyntaxDefinitions
  ( SyntaxRule (..)
  , declarationRules
  , syntaxTemplateLiteralPrefix
  )
import SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , matchSyntaxRulesWith
  )

data SyntaxRewriteFailure
  = MissingImplicitBlockResult
  | InvalidPrivateOptionalArgumentName
  | SyntaxRewriteMatchFailure SyntaxTemplateMatchFailure
  deriving (Eq, Show)

data RewriteEnvironment = RewriteEnvironment
  { rewriteRules :: [SyntaxRule]
  , rewriteDeclarations :: [Expression]
  , rewriteStrictCaptures :: Bool
  }

type CaptureHole =
  Bool
  -> [Expression]
  -> [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

rewriteExplicitSyntax
  :: CaptureHole
  -> [SyntaxRule]
  -> [Expression]
  -> Expression
  -> Either SyntaxRewriteFailure Expression
rewriteExplicitSyntax capture initialRules initialDeclarations value =
  rewriteStandalone capture environment value
  where
    environment = RewriteEnvironment
      initialRules initialDeclarations True

rewriteImplicitSyntax
  :: CaptureHole
  -> [SyntaxRule]
  -> [Expression]
  -> [Expression]
  -> Either SyntaxRewriteFailure Expression
rewriteImplicitSyntax capture initialRules initialDeclarations entries = do
  resolveImplicitBlock capture initial [] entries
  where
    initial = RewriteEnvironment initialRules initialDeclarations True

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
            [] -> Right (Program rewrittenPrefix (AtlasMap []))
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
              captureInScope previous kind captured =
                capture (rewriteStrictCaptures nested)
                  (rewriteDeclarations nested) previous kind captured
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
    SyntaxBoundary inner -> do
      rewritten <- rewriteStandalone capture environment inner
      pure (rewritten, trailing)
    MapSpecification source target
      | canReceiveFunctionBody target -> do
          let continuation = boundaryValue source : trailing
          (candidate, remaining) <-
            rewriteWithTail True capture environment target continuation
          if length remaining < length continuation
              && containsFunctionImplementation candidate
            then finish candidate remaining
            else finish value trailing
    IdentifierOperation name annotation given -> do
      let (rawAnnotation, rawGiven) =
            normalizeTrailingAssignment annotation given
      case rawGiven of
        Nothing -> do
          (rewrittenAnnotation, remaining) <-
            rewriteDeclarationPart rawAnnotation
          finish
            (IdentifierOperation name rewrittenAnnotation Nothing)
            remaining
        Just original
          | original == rawAnnotation -> do
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart original
              finish
                (IdentifierOperation name rewrittenValue
                  (Just rewrittenValue))
                remaining
          | otherwise -> do
              rewrittenAnnotation <-
                rewriteStandalone capture environment rawAnnotation
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart original
              finish
                (IdentifierOperation name rewrittenAnnotation
                  (Just rewrittenValue))
                remaining
    IdentifierTemplateOperation parts annotation given -> do
      let (rawAnnotation, rawGiven) =
            normalizeTrailingAssignment annotation given
      case rawGiven of
        Nothing -> do
          (rewrittenAnnotation, remaining) <-
            rewriteDeclarationPart rawAnnotation
          finish
            (IdentifierTemplateOperation parts rewrittenAnnotation Nothing)
            remaining
        Just original
          | original == rawAnnotation -> do
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart original
              finish
                (IdentifierTemplateOperation parts rewrittenValue
                  (Just rewrittenValue))
                remaining
          | otherwise -> do
              rewrittenAnnotation <-
                rewriteStandalone capture environment rawAnnotation
              (rewrittenValue, remaining) <-
                rewriteDeclarationPart original
              finish
                (IdentifierTemplateOperation parts rewrittenAnnotation
                  (Just rewrittenValue))
                remaining
    ListUncons operand -> do
      rewrittenOperand <- rewriteStandalone capture environment operand
      finish (ListUncons rewrittenOperand) trailing
    FunctionType domain codomain
      | allowNestedContinuation || containsBlockStart environment codomain -> do
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
      (rewritten, _) <- rewriteSequence capture environment entries
      finish (sequenceExpression rewritten) trailing
    ArgumentMap entries -> do
      rewritten <- traverse (rewriteStandalone capture environment) entries
      if all validArgumentMember rewritten
        then finish (argumentExpression rewritten) trailing
        else Left InvalidPrivateOptionalArgumentName
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
    rewriteDeclarationPart selected =
      if allowNestedContinuation
        then rewriteWithTail True capture environment selected trailing
        else rewriteDeclaredValue selected
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
      (matched, afterSyntax) <-
        matchOrdinarySyntaxWithTail capture environment attached remaining
      rewrittenChildren <- rewriteChildren capture environment matched
      final <- attachTrailingFunctionBody capture environment rewrittenChildren
      pure (final, afterSyntax)
    boundaryValue (SyntaxBoundary inner) = inner
    boundaryValue inner = inner

normalizeTrailingAssignment
  :: Expression
  -> Maybe Expression
  -> (Expression, Maybe Expression)
normalizeTrailingAssignment annotation Nothing =
  case stripTrailingLiteralAssignment annotation of
    (rewritten, given) : _ -> (rewritten, Just given)
    [] -> (annotation, Nothing)
normalizeTrailingAssignment annotation given = (annotation, given)

canReceiveFunctionBody :: Expression -> Bool
canReceiveFunctionBody FunctionType {} = True
canReceiveFunctionBody SyntaxType {} = True
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
    _ | Just (left, rebuild) <- leftInfixContext value -> do
      embedded <- rewriteEmbeddedApplication capture environment left
      case embedded of
        Just rewritten -> pure (rebuild rewritten)
        Nothing -> traverseExpressionChildren
          (rewriteStandalone capture environment) value
    FunctionApplication {} -> do
      embedded <- rewriteEmbeddedApplication capture environment value
      case embedded of
        Just rewritten -> pure rewritten
        Nothing -> traverseExpressionChildren
          (rewriteStandalone capture environment) value
    _ -> traverseExpressionChildren
      (rewriteStandalone capture environment) value

-- A neutral application spine does not know where one declared application
-- ends and its enclosing application resumes. Rewrite a literal-headed suffix
-- first when it is itself a complete syntax expression. The enclosing pass
-- can then flatten that rewritten value contextually and match its own rule.
-- This is what makes composition such as @with i from 0 to 3 do ...@ depend
-- on the declared @from@ rule rather than on a parser-level range grammar.
rewriteEmbeddedApplication
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure (Maybe Expression)
rewriteEmbeddedApplication capture environment value =
  firstChanged candidatePositions
  where
    phrase = applicationPhrase value
    candidatePositions =
      [ position
      | position <- [1 .. length phrase - 1]
      , literalHeadAt position
      ]
    literalHeadAt position = case drop position phrase of
      IdentifierReference (IdentifierString literal) : _ ->
        any ((== [literal]) . take 1 . syntaxTemplateLiteralPrefix)
          (rewriteRules environment)
      _ -> False
    firstChanged [] = Right Nothing
    firstChanged (position : remaining) = do
      let (prefix, suffix) = splitAt position phrase
          candidate = applicationFrom suffix
      rewritten <- rewriteStandalone capture environment candidate
      if rewritten == candidate
        then firstChanged remaining
        else Right (Just (applicationFrom (prefix <> [rewritten])))

dependentBinderDeclaration :: Expression -> Maybe Expression
dependentBinderDeclaration binder = case binder of
  WithBinding name _ bound ->
    Just (IdentifierOperation name bound Nothing)
  ForBinding name _ bound ->
    Just (IdentifierOperation name bound Nothing)
  _ -> Nothing

validArgumentMember :: Expression -> Bool
validArgumentMember (ForBinding (IdentifierString name) True _) =
  not (null (public [(name, ())]))
validArgumentMember (WithBinding (IdentifierString name) True _) =
  not (null (public [(name, ())]))
validArgumentMember _ = True

attachTrailingFunctionBody
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> Either SyntaxRewriteFailure Expression
attachTrailingFunctionBody capture environment value =
  case value of
    MapSpecification body (Fun signature)
      | acceptsFunctionBody signature ->
          pure (Fun (MapSpecification body signature))
    MapSpecification body (FunctionType (Fun domain) codomain) ->
      pure (Fun (MapSpecification body (FunctionType domain codomain)))
    FunctionType (Fun domain) codomain ->
      pure (Fun (FunctionType domain codomain))
    SyntaxType templates (MapSpecification body signature)
      | isFunctionImplementation body ->
          pure (MapSpecification body (SyntaxType templates signature))
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

isFunctionImplementation :: Expression -> Bool
isFunctionImplementation FunctionBody {} = True
isFunctionImplementation External {} = True
isFunctionImplementation _ = False

trailingFunctionBody :: Expression -> Maybe (Expression, Expression)
trailingFunctionBody value =
  case applicationSpine value of
    (function, arguments)
      | not (null arguments)
      , body@FunctionBody {} <- last arguments ->
          Just (applicationFrom (function : init arguments), body)
    (function, arguments)
      | not (null arguments)
      , body@External {} <- last arguments ->
          Just (applicationFrom (function : init arguments), body)
    (function, arguments)
      | not (null arguments)
      , Begin bindings result <- last arguments ->
          Just
            ( applicationFrom (function : init arguments)
            , FunctionBody bindings result
            )
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

containsBlockStart :: RewriteEnvironment -> Expression -> Bool
containsBlockStart environment value = any starts (rewriteRules environment)
  where
    starts rule = case blockShape rule of
      Just (prefix, _) -> not (null (matchingStarts prefix (applicationPhrase value)))
      Nothing -> False

matchOrdinarySyntaxWithTail
  :: CaptureHole
  -> RewriteEnvironment
  -> Expression
  -> [Expression]
  -> Either SyntaxRewriteFailure (Expression, [Expression])
matchOrdinarySyntaxWithTail capture environment value trailing =
  firstRule (rewriteRules environment)
  where
    captureInScope previous kind captured =
      capture (rewriteStrictCaptures environment)
        (rewriteDeclarations environment) previous kind captured
    firstRule [] = Right (value, trailing)
    firstRule (rule : remaining)
      | not (ruleLiteralsPresent rule (applicationFrom (value : trailing))) =
          firstRule remaining
      | otherwise =
          firstExtent rule [0 .. length trailing] >>= \case
            Just matched -> Right matched
            Nothing -> firstRule remaining
    firstExtent _ [] = Right Nothing
    firstExtent rule (consumed : remaining) =
      let combined = applicationFrom
            (value : take consumed trailing)
      in firstCandidate rule (syntaxCandidates combined) >>= \case
        Just rewritten -> Right (Just
          (rewritten, drop consumed trailing))
        Nothing -> firstExtent rule remaining
    firstCandidate _ [] = Right Nothing
    firstCandidate rule (candidate : remaining) =
      case matchSyntaxRulesWith captureInScope [rule] candidate of
        Right rewritten -> Right (Just rewritten)
        Left NoMatchingSyntaxTemplate -> firstCandidate rule remaining
        Left failure -> Left (SyntaxRewriteMatchFailure failure)

syntaxCandidates :: Expression -> [Expression]
syntaxCandidates value = value : contextualClosure [value] [value]
  where
    contextualClosure _ [] = []
    contextualClosure seen frontier =
      let fresh = filter (`notElem` seen)
            (nub (concatMap contextualStep frontier))
      in fresh <> contextualClosure (seen <> fresh) fresh

    contextualStep current = directCandidates current
      <> oneChildCandidates directCandidates current

    directCandidates current =
      signedArgumentCandidates current
        <> declarationBoundaryCandidates current
        <> rightApplicationCandidates current
        <> leftBoundaryCandidates current
        <> rightBoundaryCandidates current

ruleLiteralsPresent :: SyntaxRule -> Expression -> Bool
ruleLiteralsPresent rule value = all (`elem` identifiers)
  [ literal
  | SyntaxLiteral literal <- syntaxTemplatePieces (syntaxTemplate rule)
  ]
  where
    identifiers = collect value
    collect expressionValue = case expressionValue of
      IdentifierReference (IdentifierString name) -> name : nested
      _ -> nested
      where
        nested = concatMap collect (expressionChildren expressionValue)

data OneChild a = OneChild a [a]

instance Functor OneChild where
  fmap function (OneChild original changed) =
    OneChild (function original) (map function changed)

instance Applicative OneChild where
  pure value = OneChild value []
  OneChild originalFunction changedFunctions
      <*> OneChild originalValue changedValues =
    OneChild
      (originalFunction originalValue)
      ( map ($ originalValue) changedFunctions
          <> map originalFunction changedValues
      )

oneChildCandidates
  :: (Expression -> [Expression])
  -> Expression
  -> [Expression]
oneChildCandidates candidates value = changed
  where
    OneChild _ changed = traverseExpressionChildren
      (\child -> OneChild child (candidates child)) value

-- Provisional infix reassociation can leave a source-adjacent phrase on the
-- right of an application. Promote that phrase back into the enclosing
-- application spine so later template literals remain visible. An explicit
-- parenthesized argument is still wrapped in 'SyntaxBoundary' at this stage
-- and therefore cannot be flattened here.
rightApplicationCandidates :: Expression -> [Expression]
rightApplicationCandidates value = case value of
  FunctionApplication function argument@FunctionApplication {} ->
    [applicationFrom (applicationPhrase function <> applicationPhrase argument)]
  _ -> []

-- Once a literal syntax head has been read as an ordinary operand, a written
-- signed argument is provisionally represented as binary addition or
-- subtraction. Re-form that first right-hand phrase member as the unary value
-- the template hole receives; matching the declaration still decides whether
-- this interpretation is valid.
signedArgumentCandidates :: Expression -> [Expression]
signedArgumentCandidates value = binarySign <> embeddedSigns
  where
    binarySign = case value of
      Addition left right -> withSign Plus left right
      Subtraction left right -> withSign Minus left right
      _ -> []
    withSign sign left right = case applicationPhrase right of
      first : remaining ->
        [applicationFrom
          (applicationPhrase left <> (sign first : remaining))]
      [] -> []
    phrase = applicationPhrase value
    embeddedSigns =
      [ applicationFrom (before <> (sign first : rest) <> after)
      | (before, current, after) <- contexts phrase
      , (sign, operand) <- case current of
          Plus inner -> [(Plus, inner)]
          Minus inner -> [(Minus, inner)]
          _ -> []
      , first : rest <- [applicationPhrase operand]
      , not (null rest)
      ]
    contexts [] = []
    contexts (current : after) = ([], current, after) :
      [ (current : before, nested, remaining)
      | (before, nested, remaining) <- contexts after
      ]

-- The neutral reader associates a trailing assignment with the final literal
-- identifier in an annotation.  A declared syntax rule can prove that the
-- identifier belongs to the annotation instead: in @a : from 0 up := 2@,
-- @up@ is the final literal of @from $Int up@ and the assignment therefore
-- belongs to @a@.  Re-form that boundary as a candidate; the template matcher
-- still has to accept the stripped annotation, so this does not reserve any
-- particular literal or syntax shape.
declarationBoundaryCandidates :: Expression -> [Expression]
declarationBoundaryCandidates value = case value of
  IdentifierOperation name annotation Nothing ->
    [ IdentifierOperation name rewritten (Just given)
    | (rewritten, given) <- stripTrailingLiteralAssignment annotation
    ]
  IdentifierTemplateOperation parts annotation Nothing ->
    [ IdentifierTemplateOperation parts rewritten (Just given)
    | (rewritten, given) <- stripTrailingLiteralAssignment annotation
    ]
  _ -> []

stripTrailingLiteralAssignment
  :: Expression
  -> [(Expression, Expression)]
stripTrailingLiteralAssignment value = case value of
  FunctionApplication function
      (IdentifierOperation name annotation (Just given))
    | annotation == given ->
        [ ( FunctionApplication function (IdentifierReference name)
          , given
          )
        ]
  _ -> []

-- A declarative template may begin inside the provisional left operand of an
-- operator tree while its final hole extends to the enclosing expression
-- boundary. Preserve the written prefix and move the remaining operator
-- context into that final capture. Explicit container boundaries never reach
-- this function, so reassociation remains local to one parsed expression.
leftBoundaryCandidates :: Expression -> [Expression]
leftBoundaryCandidates = descend id
  where
    descend wrap current =
      case leftInfixContext current of
        Just (left, rebuild) ->
          reassociate (wrap . rebuild) left
            <> descend (wrap . rebuild) left
        Nothing -> []
    reassociate wrap current =
      let phrase = applicationPhrase current
      in [ applicationFrom (prefix <> [wrap (applicationFrom suffix)])
         | position <- [1 .. length phrase - 1]
         , let (prefix, suffix) = splitAt position phrase
         ]

-- Conversely, a hole-led infix template such as @$_Expr of $_Expr@ may begin
-- in the provisional right operand. Fold everything preceding its literal
-- back into the first capture, which gives declarative word operators their
-- precedence without teaching the parser their names.
rightBoundaryCandidates :: Expression -> [Expression]
rightBoundaryCandidates = descend id
  where
    descend wrap current =
      case rightInfixContext current of
        Just (right, rebuild) ->
          reassociate (wrap . rebuild) right
            <> descend (wrap . rebuild) right
        Nothing -> []
    reassociate wrap current =
      let phrase = applicationPhrase current
      in [ applicationFrom
            (wrap (applicationFrom prefix) : suffix)
         | position <- [1 .. length phrase - 1]
         , let (prefix, suffix) = splitAt position phrase
         ]

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
        Nothing -> case value of
          FunctionType domain codomain ->
            matchWithResult wrapResult codomain trailing >>= \case
              Just (rewritten, remaining) -> Right (Just
                (FunctionType domain rewritten, remaining))
              Nothing -> Right Nothing
          MapSpecification (SyntaxBoundary source) target ->
            matchWithResult id source trailing >>= \case
              Just (rewritten, remaining) -> Right (Just
                (wrapResult (MapSpecification rewritten target), remaining))
              Nothing -> Right Nothing
          _ -> case leftInfixContext value of
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
                  captureInScope previous kind captured =
                    capture (rewriteStrictCaptures nested)
                      (rewriteDeclarations nested) previous kind captured
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
  ListUncons inner -> Just (inner, ListUncons)
  EitherType left right -> Just (left, (`EitherType` right))
  MaybeThen left right -> Just (left, (`MaybeThen` right))
  Addition left right -> Just (left, (`Addition` right))
  Subtraction left right -> Just (left, (`Subtraction` right))
  Equality left right -> Just (left, (`Equality` right))
  Inequality left right -> Just (left, (`Inequality` right))
  LessThan left right -> Just (left, (`LessThan` right))
  LessThanOrEqual left right -> Just (left, (`LessThanOrEqual` right))
  GreaterThan left right -> Just (left, (`GreaterThan` right))
  GreaterThanOrEqual left right -> Just (left, (`GreaterThanOrEqual` right))
  Multiplication left right -> Just (left, (`Multiplication` right))
  Exponentiation left right -> Just (left, (`Exponentiation` right))
  MapAccess left right -> Just (left, (`MapAccess` right))
  MapSpecification left right -> Just (left, (`MapSpecification` right))
  Overload left right -> Just (left, (`Overload` right))
  SafeOverload left right -> Just (left, (`SafeOverload` right))
  SuperEllipsisRange left right -> Just (left, (`SuperEllipsisRange` right))
  _ -> Nothing

rightInfixContext
  :: Expression
  -> Maybe (Expression, Expression -> Expression)
rightInfixContext value = case value of
  EitherType left right -> Just (right, EitherType left)
  MaybeThen left right -> Just (right, MaybeThen left)
  Addition left right -> Just (right, Addition left)
  Subtraction left right -> Just (right, Subtraction left)
  Equality left right -> Just (right, Equality left)
  Inequality left right -> Just (right, Inequality left)
  LessThan left right -> Just (right, LessThan left)
  LessThanOrEqual left right -> Just (right, LessThanOrEqual left)
  GreaterThan left right -> Just (right, GreaterThan left)
  GreaterThanOrEqual left right -> Just (right, GreaterThanOrEqual left)
  Multiplication left right -> Just (right, Multiplication left)
  Exponentiation left right -> Just (right, Exponentiation left)
  MapAccess left right -> Just (right, MapAccess left)
  MapSpecification left right -> Just (right, MapSpecification left)
  Overload left right -> Just (right, Overload left)
  SafeOverload left right -> Just (right, SafeOverload left)
  SuperEllipsisRange left right -> Just (right, SuperEllipsisRange left)
  _ -> Nothing

blockShape :: SyntaxRule -> Maybe ([String], String)
blockShape rule =
  case break isBlockHole
      (syntaxTemplatePieces (syntaxTemplate rule)) of
    (prefix, SyntaxHole BlockSyntaxHole {}
        : SyntaxLiteral delimiter
        : [SyntaxHole ExpressionSyntaxHole {}]) ->
      (, delimiter) <$> traverse literal prefix
    _ -> Nothing
  where
    isBlockHole (SyntaxHole BlockSyntaxHole {}) = True
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
      case splitAtLiteral literal value of
        Just (before, suffix) -> Just
          (reverse reversed <> maybe [] (: []) before, suffix <> remaining)
        Nothing -> go (value : reversed) remaining

-- The neutral reader may place a template delimiter inside the right edge of
-- the AST immediately before it. For example, @a : 5 yield a + 1@ initially
-- has @yield@ inside the annotation of @a@. Split that source-order boundary
-- structurally: retain the declaration before the delimiter and rebuild the
-- provisional operator context around the expression after it.
splitAtLiteral
  :: String
  -> Expression
  -> Maybe (Maybe Expression, [Expression])
splitAtLiteral literal value =
  directApplicationSplit literal value
    <|> splitInfix
    <|> splitDeclaration
    <|> splitOptional
  where
    splitInfix = do
      (left, rebuildRight) <- leftInfixContext value
      case splitAtLiteral literal left of
        Just (before, suffix) -> Just
          (before, [rebuildRight (applicationFrom suffix)])
        Nothing -> do
          (right, rebuildLeft) <- rightInfixContext value
          (before, suffix) <- splitAtLiteral literal right
          pure
            ( rebuildLeft <$> before
            , suffix
            )

    splitDeclaration = case value of
      IdentifierOperation name annotation given ->
        splitIdentifierOperation IdentifierOperation name annotation given
      IdentifierTemplateOperation parts annotation given ->
        splitIdentifierOperation IdentifierTemplateOperation
          parts annotation given
      _ -> Nothing

    splitIdentifierOperation constructor name annotation given =
      case given >>= splitAtLiteral literal of
        Just (before, suffix) ->
          let rewrittenAnnotation = case given of
                Just original
                  | original == annotation ->
                      maybe annotation id before
                _ -> annotation
          in Just
            ( Just (constructor name rewrittenAnnotation before)
            , suffix
            )
        Nothing -> do
          (before, suffix) <- splitAtLiteral literal annotation
          pure
            ( (\beforeAnnotation ->
                constructor name beforeAnnotation given) <$> before
            , suffix
            )

    splitOptional = case value of
      OptionalType inner -> do
        (before, suffix) <- splitAtLiteral literal inner
        pure (OptionalType <$> before, suffix)
      _ -> Nothing

directApplicationSplit
  :: String
  -> Expression
  -> Maybe (Maybe Expression, [Expression])
directApplicationSplit literal value =
  case break (isLiteral literal) (applicationPhrase value) of
    (_, []) -> Nothing
    (before, _ : after) -> Just (applicationFromMaybe before, after)
  where
    isLiteral expected expressionValue = case expressionValue of
      IdentifierReference (IdentifierString actual) -> actual == expected
      _ -> False

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
