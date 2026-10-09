{-# LANGUAGE PatternSynonyms #-}

-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( ModuleSource (..)
  , EvaluationMode (..)
  , moduleName
  , moduleExportNames
  , moduleSyntaxRules
  , importInvocation
  , parseDatraSourceLocatedWithImportsAndStandardLibrary
  , interpretLocatedWithImports
  , interpretLocatedWithImportsInMode
  , interpretLocatedWithImportsInModeAndStandardLibrary
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
import Data.List (nub, intercalate, partition)
import BlockScope
import FunctionClosure
import DatraLanguage.Identifier
  ( isPrivateIdentifier
  , public
  , requiresShadowingConsistency
  )
import IdentifierValueType (isIdentifierValue)
import RuntimeModules
  ( EvaluationMode (..)
  , ModuleSource (..)
  , expressionForMode
  , modulesForMode
  )
import LibraryFiles
  ( standardLibraryFileName
  , requiredBundledLibrarySource
  )
import Control.Applicative ((<|>))
import Control.Monad (foldM)
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.AST
  ( Expression (..)
  , pattern FunctionType
  , GenericBinder (..)
  , GenericIdentifier (..)
  , GenericIntroduction (..)
  , GenericPolarity (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , namedBeginBlock
  , normalizeExpression
  , optionalIdentifierExpression
  , isContextualAccessOf
  , mapExpressionChildren
  , yieldedIdentifier
  )
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (FunctionSyntax)
  , SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , mapSyntaxHoleKind
  , syntaxHoleValue
  , traverseSyntaxTemplate
  )
import DatraTypes
import Parsing
  ( FunctionTypeIdentifier (..)
  , forwardGenericBoundReference
  , functionTypeIdentifiers
  , prepareFunctionDomainExpression
  , prepareGenericExpression
  , parseDatra
  , parseDatraRawLocatedWithSourceName
  , sourceImportInvocations
  , ResourceEnvelope (..)
  )
import SyntaxRewriting
  ( SyntaxRewriteFailure (..)
  , rewriteExplicitSyntax
  , rewriteImplicitSyntax
  )
import Rendering (renderCanonicalResult, renderInterpretedValue)
import GenericScopeProtection
import ScopeProtection
import SyntaxDefinitions
  ( SyntaxFunctionBody
  , SyntaxRule (..)
  , SyntaxTemplateCompilationFailure (..)
  , compileSyntaxTemplatesFromExpression
  , contextualSyntaxRules
  , qualifySyntaxRule
  , syntaxFunctionBodyForSymbol
  )
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (..) )
import Numeric.Natural (Natural)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal, omega, ordinalGT)

interpretExpression
  :: Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretExpression =
  Bifunctor.first withoutSourceSpan . interpretExpressionReason

-- | Production source parsing is deliberately split into two phases. The
-- lexical parser first reads a neutral AST without consulting declarations;
-- this pass then applies the syntax functions visible through Std, explicit
-- imports, and declarations introduced by the resource itself.
parseDatraSourceLocatedWithImportsAndStandardLibrary
  :: Bool
  -> [(String, ModuleSource)]
  -> FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseDatraSourceLocatedWithImportsAndStandardLibrary
    includeStandardLibrary modules sourceName source = do
  (envelope, Located sourceSpan raw) <-
    parseDatraRawLocatedWithSourceName sourceName source
  (base, standardRules) <- Bifunctor.first interpretingParseFailure
    (if includeStandardLibrary
      then defaultModuleEnvironment
      else Right ([], []))
  importInvocations <- sourceImportInvocations source
  let importedRules =
        [ (requested, namespace, rules)
        | (requested, moduleSource) <- modules
        , Right namespace <- [moduleName moduleSource]
        , Right rules <- [moduleSyntaxRules requested moduleSource]
        ]
      qualifiedImportedRules = concat
        [ [ qualified
          | rule <- rules
          , Just qualified <- [qualifySyntaxRule namespace rule]
          ]
        | (_, namespace, rules) <- importedRules
        ]
      explicitlyImportedRules = concat
        [ rules
        | (True, requested) <- importInvocations
        , (imported, _, rules) <- importedRules
        , imported == requested
        ]
      initialRules =
        contextualSyntaxRules
          <> standardRules <> qualifiedImportedRules <> explicitlyImportedRules
      classify = classifySyntaxHole base modules
      capture = captureSyntaxHole base modules
      rewrite = case (envelope, raw) of
        (ExplicitMapEnvelope, expressionValue) ->
          rewriteExplicitSyntax classify capture initialRules [] expressionValue
        (ImplicitBlockEnvelope, Program entries _) ->
          rewriteImplicitSyntax classify capture initialRules [] entries
        _ -> Left MissingImplicitBlockResult
  expressionValue <- Bifunctor.first rewriteParseFailure rewrite
  pure (Located sourceSpan expressionValue)
  where
    interpretingParseFailure = ParseFailure . show
    rewriteParseFailure = ParseFailure . show

-- Every syntax hole follows evaluation followed by selection. For AST
-- categories the evaluator is the identity function and selection validates
-- the unchanged syntax node; ordinary value holes use lexical evaluation
-- before specification.
captureSyntaxHole
  :: Scope
  -> [(String, ModuleSource)]
  -> Bool
  -> [Expression]
  -> [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression
captureSyntaxHole base modules strict declarations previous kind captured =
  case kind of
    ExpressionSyntaxHole target -> identityEvaluationCapture target
    BlockSyntaxHole target -> identityEvaluationCapture target
    IdentifierExpressionSyntaxHole target -> identityEvaluationCapture target
    ValueSyntaxHole target ->
      literalCapture target captured
        <|> if strict then valueEvaluationCapture target else tentativeCapture
  where
    literalCapture (AsciiStringLiteral literal)
        (IdentifierReference (IdentifierString capturedLiteral))
      | literal == capturedLiteral = Just (AsciiStringLiteral literal)
    literalCapture target value
      | target == value = Just value
    literalCapture _ _ = Nothing
    tentativeCapture = case captured of
      IdentifierReference (IdentifierString name)
        | name `notElem` concatMap bindingNames declarations ->
            Just (AsciiStringLiteral name)
      _ -> Just captured
    identityEvaluationCapture = captureInScopes $ \_ target ->
      captureSyntaxExpression target captured
    valueEvaluationCapture targetExpression =
      captureInScopes selectValue targetExpression
      where
        selectValue scope _ =
          let interpret = evalInScope scope []
          in if identifierCaptureIsSubtype
              scope scopedDeclarations targetExpression captured
            then Just captured
            else case canonicalValueCapture
                interpret targetExpression captured of
              Right canonical -> Just canonical
              Left _ -> Nothing
    captureInScopes select targetExpression =
      enclosingSyntaxCapture <|> scopedCapture
      where
        enclosing = ("\0imports", ModuleCatalog modules) : base
        enclosingSyntaxCapture = do
          target <- either (const Nothing) Just
            (evalInScope enclosing [] targetExpression)
          captureSyntaxExpression target captured
        scopedCapture = do
          (scope, _, _) <- either (const Nothing) Just
            (declareScope enclosing
              (map syntaxValidationDeclaration scopedDeclarations))
          target <- either (const Nothing) Just
            (evalInScope scope [] targetExpression)
          select scope target
    scopedDeclarations = declarations <> binderDeclarations previous

classifySyntaxHole
  :: Scope
  -> [(String, ModuleSource)]
  -> [Expression]
  -> SyntaxHoleKind Expression
  -> SyntaxHoleKind Expression
classifySyntaxHole base modules declarations kind =
  case kind of
    ValueSyntaxHole target ->
      either (const kind) (`specializeSyntaxHoleKind` kind) $ do
        (scope, _, _) <- declareScope enclosing
          (map syntaxValidationDeclaration declarations)
        evalInScope scope [] target
    _ -> kind
  where
    enclosing = ("\0imports", ModuleCatalog modules) : base

binderDeclarations
  :: [(SyntaxHoleKind Expression, Expression)]
  -> [Expression]
binderDeclarations
    ((IdentifierExpressionSyntaxHole {}, binder) : (_, bound) : remaining) =
  maybe id (:) (binderDeclaration binder bound)
    (binderDeclarations remaining)
binderDeclarations (_ : remaining) = binderDeclarations remaining
binderDeclarations [] = []

binderDeclaration :: Expression -> Expression -> Maybe Expression
binderDeclaration binder bound = case binder of
  IdentifierReference name -> Just (IdentifierOperation name bound Nothing)
  OptionalType (IdentifierReference name) ->
    Just (IdentifierOperation name bound Nothing)
  AsciiStringLiteral name
    | isIdentifierValue name ->
        Just (IdentifierOperation (IdentifierString name) bound Nothing)
  OptionalType (AsciiStringLiteral name)
    | isIdentifierValue name ->
        Just (IdentifierOperation (IdentifierString name) bound Nothing)
  _ -> Nothing

canonicalValueCapture
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Expression
  -> Either InterpretingError Expression
canonicalValueCapture interpret targetExpression captured = do
  target <- interpret targetExpression
  case captureSyntaxExpression target captured of
    Just syntaxCapture -> Right syntaxCapture
    Nothing -> case interpret captured of
      Right value -> captured <$ specifyValues value target
      Left failure -> case captured of
        IdentifierReference (IdentifierString name) -> do
          source <- asciiStringValue name
          _ <- evalValues canonicalStringCodec source target
          Right (AsciiStringLiteral name)
        _ -> Left failure

-- A recursive function body is the fixed-point seed already used by ordinary
-- evaluation while its public signature is being assembled. Syntax-hole
-- validation can reach that function through another recursive let before the
-- direct self-cycle guard fires, so construct its validation-only declaration
-- from the same seed. The completed declaration remains unchanged everywhere
-- outside this scope and is still checked against its full signature.
syntaxValidationDeclaration :: Expression -> Expression
syntaxValidationDeclaration declaration = case declaration of
  Let (IdentifierOperation name _ (Just definition))
    | Just implementation <- recursiveFunctionImplementation definition ->
        Let (IdentifierOperation name implementation (Just implementation))
  _ -> declaration

identifierCaptureIsSubtype
  :: Scope
  -> [Expression]
  -> Expression
  -> Expression
  -> Bool
identifierCaptureIsSubtype scope declarations
    target (IdentifierReference (IdentifierString name)) =
  case
      [ annotation
      | declaration <- reverse declarations
      , Just details <- [blockDeclaration declaration]
      , declarationName details == name
      , Just annotation <- [declarationAnnotation details]
      ] of
    annotation : _ -> either (const False) id $ do
      source <- evalInScope scope [] annotation
      destination <- evalInScope scope [] target
      subfederationValues source destination >>= booleanCondition
    [] -> False
identifierCaptureIsSubtype _ _ _ _ = False

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
  interpretLocatedWithImportsInModeAndStandardLibrary
    True mode modules (Located sourceSpan expression)

interpretLocatedWithImportsInModeAndStandardLibrary
  :: Bool
  -> EvaluationMode
  -> [(String, ModuleSource)]
  -> Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedWithImportsInModeAndStandardLibrary
    includeStandardLibrary mode modules (Located sourceSpan expression) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretWithImportsInModeAndStandardLibrary
      includeStandardLibrary mode modules expression)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason = interpretWithImports []

-- | Evaluate a closed reconstruction without importing Std or any modules.
interpretClosedExpression :: Expression -> Either InterpretingError InterpretedValue
interpretClosedExpression = evalInScope [] []

interpretWithImports :: [(String, ModuleSource)] -> Expression -> Either InterpretingError InterpretedValue
interpretWithImports modules expression = do
  scope <- defaultImportScope
  evalInScope (("\0imports", ModuleCatalog modules) : scope) [] expression

interpretWithImportsInMode
  :: EvaluationMode
  -> [(String, ModuleSource)]
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithImportsInMode mode modules expression =
  interpretWithImportsInModeAndStandardLibrary True mode modules expression

interpretWithImportsInModeAndStandardLibrary
  :: Bool
  -> EvaluationMode
  -> [(String, ModuleSource)]
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithImportsInModeAndStandardLibrary
    includeStandardLibrary mode modules expression = do
  base <- if includeStandardLibrary then defaultImportScope else Right []
  evalInScope
    (("\0imports", ModuleCatalog (modulesForMode mode modules)) : base)
    []
    (expressionForMode mode expression)


defaultImportScope :: Either InterpretingError Scope
defaultImportScope = fst <$> defaultModuleEnvironment

-- Parsing and evaluation consume two views of the same imported module.
-- Build them from one module instance so syntax discovery cannot recursively
-- instantiate Std independently of the scope used to evaluate those rules.
defaultModuleEnvironment
  :: Either InterpretingError (Scope, [SyntaxRule])
defaultModuleEnvironment = do
  source <- defaultModuleSource
  let base = [("\0imports", ModuleCatalog
        [(standardLibraryFileName, source)])]
  scope <- importLoadedModule base True source
  namespace <- moduleName source
  value <- case lookup namespace scope of
    Just (ImportedBinding _ _ importedValue _) -> Right importedValue
    _ -> Left (ModuleEvaluationFailed (ModuleNotLoaded standardLibraryFileName))
  rules <- moduleSyntaxRulesFromValue standardLibraryFileName value
  let qualifiedRules =
        [ qualified
        | rule <- rules
        , Just qualified <- [qualifySyntaxRule namespace rule]
        ]
  pure (scope, rules <> qualifiedRules)

retainExportDefinition :: Binding -> Binding -> Binding
retainExportDefinition evaluated source =
  case (evaluated, bindingDefinition source) of
    (EvaluatedBinding value, Just (lexical, annotation, expressionValue)) ->
      RetainedBinding lexical annotation expressionValue value
    (ShadowingConsistentBinding binding, _) ->
      ShadowingConsistentBinding (retainExportDefinition binding source)
    (NamedBinding dependency binding, _) ->
      NamedBinding dependency (retainExportDefinition binding source)
    _ -> evaluated

parsedDefaultModule :: Either InterpretingError Expression
parsedDefaultModule = do
  (envelope, Located _ raw) <- either parseFailure Right
    (parseDatraRawLocatedWithSourceName standardLibraryFileName
      (requiredBundledLibrarySource standardLibraryFileName))
  let capture = captureSyntaxHole [] []
      classify = classifySyntaxHole [] []
      rewritten = case (envelope, raw) of
        (ExplicitMapEnvelope, expressionValue) ->
          rewriteExplicitSyntax
            classify capture contextualSyntaxRules [] expressionValue
        (ImplicitBlockEnvelope, Program entries _) ->
          rewriteImplicitSyntax
            classify capture contextualSyntaxRules [] entries
        _ -> Left MissingImplicitBlockResult
  either
    (parseFailure . ParseFailure . show)
    Right
    rewritten
  where
    parseFailure = Left . ModuleEvaluationFailed
      . StandardLibraryParseFailure standardLibraryFileName
      . parseFailureMessage

defaultModuleSource :: Either InterpretingError ModuleSource
defaultModuleSource =
  ModuleSource standardLibraryFileName <$> parsedDefaultModule <*> pure []

canonicalStringCodec :: CanonicalStringCodec
canonicalStringCodec =
  CanonicalStringCodec
    { renderCanonicalString = renderInterpretedValue
    , decodeCanonicalString = canonicalStringCandidates
    }

evaluateFunctionSyntax
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError (FunctionSyntax InterpretedValue)
evaluateFunctionSyntax interpret templatesExpression = do
  templates <- validatedSyntaxTemplates templatesExpression
  evaluated <- traverse (traverseSyntaxTemplate interpret) templates
  pure (FunctionSyntax (map specializeTemplate evaluated))
  where
    specializeTemplate (SyntaxTemplate pieces) =
      SyntaxTemplate (map specializePiece pieces)
    specializePiece (SyntaxHole kind@(ValueSyntaxHole target)) =
      SyntaxHole (specializeSyntaxHoleKind target kind)
    specializePiece piece = piece

sourceFunctionSyntax
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError (FunctionSyntax String)
sourceFunctionSyntax interpret templatesExpression = do
  templates <- validatedSyntaxTemplates templatesExpression
  FunctionSyntax <$> traverse sourceTemplate templates
  where
    sourceTemplate (SyntaxTemplate pieces) =
      SyntaxTemplate <$> traverse sourcePiece pieces
    sourcePiece (SyntaxLiteral literal) = pure (SyntaxLiteral literal)
    sourcePiece (SyntaxHole kind) = do
      target <- interpret (syntaxHoleValue kind)
      pure (SyntaxHole
        (mapSyntaxHoleKind renderSourceExpression
          (specializeSyntaxHoleKind target kind)))

validatedSyntaxTemplates
  :: Expression
  -> Either InterpretingError [SyntaxTemplate Expression]
validatedSyntaxTemplates templatesExpression =
  case compileSyntaxTemplatesFromExpression templatesExpression of
    Left ExpectedSyntaxTemplateOperand ->
      Left InvalidSyntaxTemplateOperand
    Left (ForbiddenSyntaxTemplateCharacter invalid) ->
      Left (InvalidSyntaxTemplateCharacter invalid)
    Right templates -> Right templates

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
                        canonicalExpressionCandidates
                          (normalizeExpression expressionValue)
                    , Right interpreted <-
                        [interpretExpressionReason candidateExpression]
                    , candidate <- evaluatedIdentifierCandidates
                        candidateExpression interpreted
                    ]
            _ -> []

    -- A canonical identifier can name a non-total value.  Its parsed AST then
    -- has no Either node to split, unlike explicit optional/Either syntax.
    -- Expand only that identifier case: explicit structural expressions
    -- already retain the selected-branch witness needed by specification.
    evaluatedIdentifierCandidates (IdentifierReference _) interpreted =
      case argumentPresentations interpreted of
        Right alternatives ->
          [ alternative
          | alternative <- alternatives
          , canonicalSpelling characters
              (renderInterpretedValue alternative)
          ]
        Left _ -> []
    evaluatedIdentifierCandidates _ interpreted = [interpreted]

    -- Parentheses are canonical when a rendered value is embedded as one
    -- component of a larger expression. No other alternate spelling is
    -- accepted by the inverse.
    canonicalSpelling actual rendered =
      actual == rendered || actual == "(" <> rendered <> ")"

-- Canonical Either and map syntax can retain the unselected branches that
-- explain a value's type. Decode those contexts into their concrete member
-- expressions before asking the semantic federation to select one.
canonicalExpressionCandidates :: Expression -> [Expression]
canonicalExpressionCandidates expressionValue
  | Just (present, missing) <- optionalIdentifierExpression expressionValue =
      canonicalExpressionCandidates present
        <> canonicalExpressionCandidates missing
  | otherwise =
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

shadowingConsistencyFuel :: Int
shadowingConsistencyFuel = 64

type Scope = [(String, Binding)]

data Binding
  = DeferredBinding Scope (Maybe Expression) Expression
  | EvaluatedBinding InterpretedValue
  | PrivateParameterBinding InterpretedValue
  | ContextualBinding String Bool
      (ReductionContext -> Either InterpretingError InterpretedValue)
  | ShadowingConsistentBinding Binding
  | NamedBinding PresentationDependency Binding
  | QualifiedBinding String Binding
  | RetainedBinding Scope (Maybe Expression) Expression InterpretedValue
  | ImportedBinding
      PresentationDependency FilePath InterpretedValue Scope
  | ModuleCatalog [(String, ModuleSource)]
  | ScopeMembers [String]
  | CanonicalNames [(String, String)]
  | LexicalScope PresentationDependency

data ImportPresentation
  = TransparentImportPresentation
  | ModularImportPresentation

data ModuleExport = ModuleExport String ImportPresentation Binding

moduleExportName :: ModuleExport -> String
moduleExportName (ModuleExport name _ _) = name

scopeBinding :: String -> Binding -> (String, Binding)
scopeBinding name binding =
  ( name
  , if requiresShadowingConsistency name
      then ShadowingConsistentBinding binding
      else binding
  )

bindingHasUnrestrictedShadowing :: Binding -> Bool
bindingHasUnrestrictedShadowing binding =
  case binding of
    ShadowingConsistentBinding {} -> False
    NamedBinding _ target -> bindingHasUnrestrictedShadowing target
    QualifiedBinding _ target -> bindingHasUnrestrictedShadowing target
    _ -> True

contextualBinding
  :: Binding
  -> Maybe
      ( Bool
      , ReductionContext -> Either InterpretingError InterpretedValue
      )
contextualBinding binding =
  case binding of
    ContextualBinding _ includesDependencies value ->
      Just (includesDependencies, value)
    ShadowingConsistentBinding target -> contextualBinding target
    NamedBinding _ target -> contextualBinding target
    QualifiedBinding _ target -> contextualBinding target
    _ -> Nothing

contextualBindings
  :: String
  -> Bool
  -> (ReductionContext -> Either InterpretingError InterpretedValue)
  -> Scope
contextualBindings surface includesDependencies value =
  [scopeBinding ("_" <> surface)
    (ContextualBinding surface includesDependencies value)]

constantContextualBindings :: String -> InterpretedValue -> Scope
constantContextualBindings surface value =
  contextualBindings surface False (const (Right value))

type ContextualLevel =
  (Bool, ReductionContext -> Either InterpretingError InterpretedValue)

-- | A contextual function's private, coalized map. Its name is @_inner_this@
-- or @_inner_it@, but it lives only in the native function closure and never
-- enters a Datra lexical scope.
data ContextualMap = ContextualMap String [ContextualLevel]

-- | Collect same-kind contextual bindings from current to outermost.  The
-- environment retained for a declaration-scope level begins at the previous
-- same-kind boundary, so declarations belonging to that outer scope remain
-- visible. Scopes which introduce no binding of this kind add no hole.
contextualLevels
  :: Bool
  -> [String]
  -> String
  -> Scope
  -> [ContextualLevel]
contextualLevels includesPrivate resolving surface scope = go scope scope
  where
    key = "_" <> surface

    go _ [] = []
    go environment ((name, binding) : remaining)
      | name == key
      , Just level <- contextualLevel environment binding =
          level : go remaining remaining
      | otherwise = go environment remaining

    contextualLevel environment binding =
      case binding of
        ContextualBinding _ includesDependencies value ->
          Just (includesDependencies, value)
        ScopeMembers names ->
          Just (False, \reduction -> declarationMap names
            (resolveIdentifierAccess
              includesPrivate reduction environment resolving))
        ShadowingConsistentBinding target ->
          contextualLevel environment target
        NamedBinding dependency target -> do
          (includesDependencies, value) <- contextualLevel environment target
          pure (includesDependencies, \reduction ->
            withCanonicalReference [dependency] key <$> value reduction)
        QualifiedBinding _ target -> do
          (includesDependencies, value) <- contextualLevel environment target
          pure (includesDependencies, \reduction ->
            withoutCanonicalPresentation <$> value reduction)
        _ -> Nothing

-- | A contextual function has the exact valued-natural domain of its
-- available same-kind lexical levels. @_this n@ and @_it n@ lower inside the
-- native closure to @_inner_this @ n@ and @_inner_it @ n@ respectively.
contextualFunction
  :: String
  -> [ContextualLevel]
  -> Either InterpretingError InterpretedValue
contextualFunction surface levels@(_ : _) = do
  domain <- valuedNaturalRangeValue 0 maximumDepth
  let schema = argumentSlotSchema Nothing False domain (Just (naturalValue 0))
  pure (makeFunctionValue (EvaluatedFunction
    domain
    anyTypeValue
    (Just valueSyntax)
    (Just sourceSyntax)
    Nothing
    signatureSource
    (Just (prepare schema))
    (Just invoke)
    False))
  where
    maximumDepth = fromIntegral (length levels - 1)
    domainExpression = ValuedNaturalRange 0 maximumDepth
    signatureSource = renderSourceExpression
      (FunctionType domainExpression (External (AsciiStringLiteral "datra.Any")))
    innerMap = ContextualMap ("_inner_" <> surface) levels

    -- The surface spelling has no holes and therefore supplies the empty map.
    -- Contextual depth zero is the function's ordinary default; explicit
    -- @_this n@ and @_it n@ calls overload that default with @n@.
    prepare schema supplied = do
      (depth, bindings) <- overloadArgumentSchemaComplete schema supplied
      pure (PreparedFunctionArgument supplied depth bindings)

    invoke reduction prepared = do
      depth <- requireFiniteInteger LeftOperand
        (functionPreparedArgument prepared)
      accessContextualMap reduction depth innerMap

    valueSyntax :: FunctionSyntax InterpretedValue
    valueSyntax = FunctionSyntax [SyntaxTemplate [SyntaxLiteral surface]]
    sourceSyntax :: FunctionSyntax String
    sourceSyntax = FunctionSyntax [SyntaxTemplate [SyntaxLiteral surface]]
contextualFunction surface [] = Left (UnknownIdentifier ("_" <> surface))

-- | Access the closure-local @_inner_this@ or @_inner_it@ map without forcing
-- unrelated recursive levels.
accessContextualMap
  :: ReductionContext
  -> Integer
  -> ContextualMap
  -> Either InterpretingError InterpretedValue
accessContextualMap reduction depth (ContextualMap _ levels)
  | depth < 0 = unavailable
  | otherwise = select depth levels
  where
    select _ [] = unavailable
    select 0 ((_, value) : _) = value reduction
    select remaining (_ : outer) = select (remaining - 1) outer
    unavailable = Left
      (FunctionEvaluationFailed NoApplicableFunctionAlternative)

scopeMembersBinding :: Binding -> Maybe [String]
scopeMembersBinding binding =
  case binding of
    ScopeMembers names -> Just names
    ShadowingConsistentBinding target -> scopeMembersBinding target
    NamedBinding _ target -> scopeMembersBinding target
    QualifiedBinding _ target -> scopeMembersBinding target
    _ -> Nothing

-- Whole recursive scope values do not have a finite semantic normal form that
-- a proposed shadow can be reduced against. This is a property of the binding
-- representation, independent of the identifier used to reach it.
bindingHasNoFiniteShadowingNormalForm :: Binding -> Bool
bindingHasNoFiniteShadowingNormalForm binding =
  case (contextualBinding binding, scopeMembersBinding binding) of
    (Just _, _) -> True
    (_, Just _) -> True
    _ -> False

data RecursivePrefix
  = RecursiveConcatenation Expression
  | RecursiveAtlasSequence [Expression]
  | RecursiveMapSequence [Expression]

-- A finite access into a productive recursive map only needs finitely many
-- unfoldings. Both comma concatenation and semicolon sequencing delegate back
-- to their ordinary evaluators after the recursive tail has been removed.
lazyRecursivePrefix :: Scope -> Expression -> Maybe (Scope, RecursivePrefix)
lazyRecursivePrefix scope expression = case expression of
  Fun value -> (scope,) <$> recursivePrefixFor
    (isContextualAccessOf (IdentifierString "_this")) value
  IdentifierReference (IdentifierString name) -> do
    binding <- lookup name scope
    (captured, _, definition) <- bindingDefinition binding
    let isSelf value = value == IdentifierReference (IdentifierString name)
    prefix <- case definition of
      Fun value -> recursivePrefixFor
        (isContextualAccessOf (IdentifierString "_this")) value
      value -> recursivePrefixFor isSelf value
    pure (captured, prefix)
  _ -> Nothing

recursivePrefixFor :: (Expression -> Bool) -> Expression -> Maybe RecursivePrefix
recursivePrefixFor isSelf expression = case expression of
  MapConcatenation prefix suffix
    | isSelf suffix -> Just (RecursiveConcatenation prefix)
  AtlasMap members -> RecursiveAtlasSequence <$> sequencePrefix members
  MapSequence members -> RecursiveMapSequence <$> sequencePrefix members
  _ -> Nothing
  where
    sequencePrefix members = case reverse members of
      suffix : reversedPrefix
        | isSelf suffix
        , not (null reversedPrefix) -> Just (reverse reversedPrefix)
      _ -> Nothing

accessRepeatedPrefix
  :: Scope
  -> [String]
  -> RecursivePrefix
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessRepeatedPrefix captured resolving recursivePrefix insertion = do
  prefix <- evalInScope captured resolving (prefixExpression recursivePrefix)
  case (selectionMaximum insertion, naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap prefix))) of
    (Just maximumPosition, Just prefixLength)
      | prefixLength > 0 -> do
          repeated <- unfold (maximumPosition `div` prefixLength + 1) prefix
          accessValues repeated insertion
    _ -> accessValues prefix insertion
  where
    prefixExpression (RecursiveConcatenation value) = value
    prefixExpression (RecursiveAtlasSequence values) = AtlasMap values
    prefixExpression (RecursiveMapSequence values) = MapSequence values

    unfold copies value = case recursivePrefix of
      RecursiveConcatenation _ -> repeatValue value copies
      RecursiveAtlasSequence values ->
        evalInScope captured resolving (AtlasMap (repeatExpressions copies values))
      RecursiveMapSequence values ->
        evalInScope captured resolving (MapSequence (repeatExpressions copies values))

    repeatValue value copies = go copies value
      where
        go remaining accumulated
          | remaining <= 1 = Right accumulated
          | otherwise = concatenateValues accumulated value >>= go (remaining - 1)

    repeatExpressions copies values = go copies
      where
        go remaining
          | remaining <= 0 = []
          | otherwise = values <> go (remaining - 1)

selectionMaximum :: InterpretedValue -> Maybe Natural
selectionMaximum insertion = do
  count <- naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap insertion))
  positions <- traverse selected (if count == 0 then [] else [0 .. count - 1])
  pure (if null positions then 0 else maximum positions)
  where
    selected position = do
      value <- interpretedMapValueAt (interpretedMap insertion) (finiteOrdinal position)
      (_, ordinal) <- interpretedExplicitOrdinal value
      naturalAtOrdinal ordinal

evalInScope :: Scope -> [String] -> Interpreter
evalInScope = evalInScopeWith UnrestrictedReduction

evalInScopeWith :: ReductionContext -> Scope -> [String] -> Interpreter
evalInScopeWith reduction scope resolving expressionValue =
  evalInScopeWithProtection
    (initialProtectionContext expressionValue)
    reduction scope resolving expressionValue

evalInScopeWithProtection
  :: EvaluationProtectionContext
  -> ReductionContext
  -> Scope
  -> [String]
  -> Interpreter
evalInScopeWithProtection protection reduction scope resolving =
  interpretNormalizedExpressionWith protection reduction scope resolving
    . normalizeExpression

interpretNormalizedExpressionWith
  :: EvaluationProtectionContext
  -> ReductionContext
  -> Scope
  -> [String]
  -> Interpreter
interpretNormalizedExpressionWith protection reduction scope resolving expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    Skip -> Right skipValue
    AsciiStringLiteral value -> asciiStringValue value
    NothingLiteral -> Right nothingValue
    StringTemplate parts ->
      interpretStringTemplateWith protection interpret parts
    IdentifierValueType -> Right identifierValueTypeValue
    AtlasMap expressions -> interpretContainer
      (interpretProtectedAtlasMap makeAtlasMap expressions)
      (AtlasMap expressions)
      expressions
    ArgumentMap expressions -> interpretContainer
      (interpretProtectedValues expressions makeArgumentMapPreservingSingleton)
      (ArgumentMap expressions)
      expressions
    MapSequence expressions -> interpretContainer
      (interpretProtectedAtlasMap makeAtlasMap expressions)
      (MapSequence expressions)
      expressions
    SyntaxBoundary inner -> interpret inner
    ReverseMapSpecification target source ->
      interpret (MapSpecification source target)
    ReverseOverload supplied defaults ->
      interpret (Overload defaults supplied)
    ReverseSafeOverload supplied defaults ->
      interpret (SafeOverload defaults supplied)
    MapExpansion left right ->
      interpretProtectedAtlasMap
        makeAtlasExpansion
        [ensureMapLevel left, ensureMapLevel right]
    SuperEllipsisRange lower upper ->
      binary boundedRangeValue lower upper
    SuperEllipsisRangePlus lower ->
      unary openPlusRangeValue lower
    SuperEllipsisRangeMinus upper ->
      unary openMinusRangeValue upper
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
      case optionalIdentifierExpression expressionValue of
        Just (present, missing) -> binary eitherValue present missing
        Nothing -> interpret
          (FunctionApplication
            (IdentifierReference (IdentifierString "Maybe"))
            operand)
    ListUncons operand -> unary unconsList operand
    MaybeThen optional branch -> do
      optionalResult <- interpret optional
      runProtectedOperation protection [optionalResult] $ \actuals ->
        case actuals of
          [actualOptional] ->
            case interpretedSemanticResult actualOptional of
              CanonicalAssignment "Just" _ _ -> do
                result <- evalInScopeWithProtection protection reduction
                  (constantContextualBindings "it" actualOptional <> scope)
                  resolving
                  branch
                liftMaybeResult result
              _ -> do
                absent <- isStandardNothing actualOptional
                if absent
                  then standardNothingValue
                  else Left (FunctionEvaluationFailed
                    NoApplicableFunctionAlternative)
          _ -> Right neverValue
    Conditional condition consequent alternative -> do
      conditionValue <- interpret condition
      runProtectedOperation protection [conditionValue] $ \actuals ->
        case actuals of
          [actualCondition] -> do
            conditionFlag <- booleanCondition actualCondition
            interpret (if conditionFlag then consequent else alternative)
          _ -> Right neverValue
    Addition left right ->
      binary addValues left right
    Subtraction left right ->
      binary subtractValues left right
    Plus operand -> unary plusValue operand
    Minus operand -> unary minusValue operand
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
      runProtectedOperation protection [equal] $ \actuals ->
        case actuals of
          [actual] -> booleanNotValue actual
          _ -> Right neverValue
    LessThan left right ->
      binaryComparison (== LT) left right
    LessThanOrEqual left right ->
      binaryComparison (/= GT) left right
    GreaterThan left right ->
      binaryComparison (== GT) left right
    GreaterThanOrEqual left right ->
      binaryComparison (/= LT) left right
    BooleanAnd left right ->
      binary booleanAndValues left right
    BooleanOr left right ->
      binary booleanOrValues left right
    BooleanNot operand -> unary booleanNotValue operand
    Coalization operand -> unary (Right . coalizeValue) operand
    Modular operand -> unary modularValue operand
    Fun operand ->
      case recursiveListElement operand of
        Just element -> do
          elementType <- interpret element
          runProtectedOperation protection [elementType] $ \actuals ->
            case actuals of
              [actualElement] -> pure (listTypeValue
                (renderSourceExpression expressionValue) actualElement)
              _ -> Right neverValue
        Nothing -> recursive reduction
      where
        recursive activeReduction = evalInScopeWithProtection protection activeReduction
          (contextualBindings "this"
            (case operand of Begin {} -> True; _ -> False)
            recursive <> scope)
          resolving
          operand
    WithBinding _ _ _ -> Left (DependentBinderOutsideContainer "with")
    ForBinding _ _ _ -> Left (DependentBinderOutsideContainer "for")
    GenericIntroductionExpression introduction ->
      Left (DependentBinderOutsideContainer
        (case genericIntroductionPolarity introduction of
          GenericProduct -> "&"
          GenericSum -> "^"))
    GenericReferenceExpression {} ->
      Left (FunctionEvaluationFailed ExpectedFunctionType)
    InModule path body -> do
      imported <- lookupModuleDefinitionScope scope path
      evalInScopeWithProtection protection reduction imported resolving body
    Import _ _ -> Left (ModuleEvaluationFailed ImportOutsideScope)
    SyntaxType templates signature -> do
      syntax <- evaluateFunctionSyntax interpret templates
      sourceSyntax <- sourceFunctionSyntax interpret templates
      value <- interpret signature
      runProtectedOperation protection [value] $ \actuals ->
        case actuals of
          [actualValue] -> case interpretedFunction actualValue of
            Just function -> pure (makeFunctionValue function
              { functionSyntax = Just syntax
              , functionSyntaxSource = Just sourceSyntax
              })
            Nothing -> Left (FunctionEvaluationFailed
              AstPatternRequiresFunctionSignature)
          _ -> Right neverValue
    FunctionTypeExpression [] domain codomain -> do
      evaluateFunctionType expressionValue domain codomain
    FunctionTypeExpression generics domain codomain -> do
      validateGenericFunctionType interpret generics domain codomain
      let preparedDomain = prepareFunctionDomainExpression generics domain
          preparedCodomain = prepareGenericExpression generics codomain
      evaluateFunctionType expressionValue preparedDomain preparedCodomain
    FunctionBody {} -> Left (FunctionEvaluationFailed ExpectedFunctionType)
    FunctionApplication function argument -> do
      callable <- interpret function
      supplied <- interpret argument
      runProtectedOperation protection [callable, supplied] $ \actuals ->
        case actuals of
          [actualCallable, actualSupplied] -> do
            input <- functionArgumentValue actualSupplied
            applyFunction reduction actualCallable input
          _ -> Right neverValue
    External descriptor -> unary (externalValue scope) descriptor
    Program bindings result -> evaluateBlock Nothing bindings result
    Begin bindings result ->
      evaluateBlock (Just (renderSourceExpression expressionValue)) bindings result
    Let _ -> Left LetOutsideBegin
    IdentifierReference (IdentifierString name) ->
      resolveIdentifierWith reduction scope resolving name
    Assert _ condition -> do
      conditionValue <- interpret condition
      runProtectedOperation protection [conditionValue] $ \actuals ->
        case actuals of
          [actualCondition] -> do
            accepted <- booleanCondition actualCondition
            if accepted
              then Right (makeAtlasMap 0 [])
              else Left AssertionFailed
          _ -> Right neverValue
    MapConcatenation left right ->
      binary concatenateValues left right
    Overload defaults supplied ->
      binary overloadValues defaults supplied
    SafeOverload defaults supplied ->
      binary safeOverloadValues defaults supplied
    NamedAccess
        (IdentifierReference (IdentifierString namespace))
        (IdentifierString name)
      | Just (ImportedBinding dependency identity value _) <- lookup namespace scope ->
          case namedAccessValue value name of
            Left (NamedAccessFailed (NamedFieldNotFound _)) ->
              Left (UnknownIdentifier name)
            result -> do
              selected <- result
              if hasTrailingIdentifierMarker modularMarker selected
                then do
                  payload <- accessValues selected (naturalValue 1)
                  pure (withCanonicalNamedAccess
                    [modularPresentationDependency identity]
                    (CanonicalReference namespace) name payload)
                else withCanonicalNamedAccess
                  [dependency] (CanonicalReference namespace) name
                    <$> transparentEitherAlias selected
    -- Project one declared binding without forcing the whole scope map. This
    -- also permits projections next to recursive function declarations.
    NamedAccess
        thisValue
        (IdentifierString name)
      | isContextualAccessOf (IdentifierString "_this") thisValue
      , Just (_, value) <- lookup "_this" scope >>= contextualBinding ->
          value reduction >>= \contextual ->
            runProtectedOperation protection [contextual] $ \actuals ->
              case actuals of
                [actual] -> namedAccessValue actual name
                _ -> Right neverValue
      | isContextualAccessOf (IdentifierString "_this") thisValue
      , Just names <- lookup "_this" scope >>= scopeMembersBinding
      , name `elem` names ->
          simpleIdentifierTypeValue name
            <$> resolveIdentifierWith reduction scope resolving name
    NamedAccess operand (IdentifierString name) ->
      unary (`namedAccessValue` name) operand
    MapAccess
        (NamedAccess
          thisValue
          (IdentifierString name))
        (EllipsisNatural 1)
      | isContextualAccessOf (IdentifierString "_this") thisValue ->
          resolveIdentifierIncludingPrivate reduction scope resolving name
    MapAccess
        thisValue
        insertionOperand
      | isContextualAccessOf (IdentifierString "_this") thisValue -> do
          insertion <- interpret insertionOperand
          case lookup "_this" scope >>= contextualBinding of
            Just (_, value) -> do
              contextual <- value reduction
              runProtectedOperation
                protection [contextual, insertion] $ \actuals ->
                  case actuals of
                    [actualContextual, actualInsertion] ->
                      accessValues actualContextual actualInsertion
                    _ -> Right neverValue
            _ -> projectDeclaration
              (scopeMemberNames scope)
              (resolveIdentifierWith reduction scope resolving)
              insertion
    MapAccess mapOperand insertionOperand ->
      case lazyRecursivePrefix scope mapOperand of
        Just (captured, prefix) -> do
          insertion <- interpret insertionOperand
          accessRepeatedPrefix captured resolving prefix insertion
        Nothing -> binary accessValues mapOperand insertionOperand
    MapSpecification implementation syntaxType@(SyntaxType
        templates signature)
      | not (syntaxImplementationExpression implementation) ->
          interpretSpecificationWith protection interpret implementation syntaxType
      | External descriptorExpression <- implementation -> do
          syntax <- evaluateFunctionSyntax interpret templates
          sourceSyntax <- sourceFunctionSyntax interpret templates
          descriptor <- interpret descriptorExpression
          target <- interpret signature
          value <- resolveExternal scope descriptor
          functionValue <- case value of
            ResolvedFunctionBody _ ->
              case interpretedFunction target of
                Just function -> pure (makeFunctionValue function
                  { functionSource = Just
                      (renderSourceExpression implementation) })
                Nothing -> Left (FunctionEvaluationFailed
                  AstPatternRequiresFunctionImplementation)
            ResolvedExternalValue external ->
              case linkExternalAdapter external target of
                Just linked -> linked
                Nothing -> contextuallySpecify external target
          case interpretedFunction functionValue of
            Just function -> pure (makeFunctionValue function
              { functionSyntax = Just syntax
              , functionSyntaxSource = Just sourceSyntax
              })
            Nothing -> Left (FunctionEvaluationFailed
              AstPatternRequiresFunctionImplementation)
      | otherwise -> do
          syntax <- evaluateFunctionSyntax interpret templates
          sourceSyntax <- sourceFunctionSyntax interpret templates
          value <- interpret (MapSpecification implementation signature)
          case interpretedFunction value of
            Just function -> pure (makeFunctionValue function
              { functionSyntax = Just syntax
              , functionSyntaxSource = Just sourceSyntax
              })
            Nothing -> Left (FunctionEvaluationFailed
              AstPatternRequiresFunctionImplementation)
    MapSpecification
        (FunctionBody bindings result)
        signature@(FunctionTypeExpression [] domain codomain) ->
      createFunction protection reduction scope resolving signature
        domain codomain bindings result
    MapSpecification
        (FunctionBody bindings result)
        signature@(FunctionTypeExpression generics domain codomain) -> do
      validateGenericFunctionType interpret generics domain codomain
      let preparedDomain = prepareFunctionDomainExpression generics domain
          preparedCodomain = prepareGenericExpression generics codomain
      createFunctionWithGenerics protection reduction scope resolving
        signature preparedDomain preparedCodomain bindings result
        generics
    MapSpecification sourceOperand targetOperand ->
      interpretSpecificationWith protection interpret sourceOperand targetOperand
    IdentifierOperation
        (IdentifierString identifierString)
        typeAnnotationExpression
        maybeGivenValueExpression ->
      interpretIdentifierOperation
        identifierString typeAnnotationExpression maybeGivenValueExpression
    IdentifierTemplateOperation
        parts
        typeAnnotationExpression
        maybeGivenValueExpression -> do
      typeAnnotation <- interpret typeAnnotationExpression
      requireCanonicalTypeAnnotation typeAnnotation
      let identifierExpression = StringTemplate parts
          familyKey = renderSourceExpression identifierExpression
          nameFamily supplied =
            interpretStringTemplateWith protection
              (evalInScopeWithProtection protection reduction
                (constantContextualBindings "it" supplied <> scope)
                resolving)
              parts
      identifier <- nameFamily typeAnnotation
      case datraCanonicalType (interpretedDatraType identifier) of
        Just _ -> pure ()
        Nothing -> Left NoCanonicalStringConversion
      case asciiStringFromInterpretedMap (interpretedMap identifier) of
        Just identifierString
          | interpretedValueHasTotalMap identifier
          , isIdentifierValue identifierString ->
          interpretIdentifierOperation
            identifierString typeAnnotationExpression maybeGivenValueExpression
        _ ->
          let target = dependentIdentifierTemplateTypeValue
                familyKey identifier nameFamily typeAnnotation
          in case maybeGivenValueExpression of
            Nothing -> Right target
            Just givenExpression -> do
              given <- interpret givenExpression
              _ <- specifyValues given typeAnnotation
              givenIdentifier <- nameFamily given
              case asciiStringFromInterpretedMap
                  (interpretedMap givenIdentifier) of
                Just identifierString
                  | interpretedValueHasTotalMap givenIdentifier
                  , isIdentifierValue identifierString ->
                      assignIdentifierValues
                        identifierString typeAnnotation given
                _ ->
                  let source = dependentIdentifierTemplateTypeValue
                        familyKey givenIdentifier nameFamily given
                  in specifyValues source target

  where
    interpret = evalInScopeWithProtection protection reduction scope resolving
    transparentEitherAlias value =
      case stripOuterIdentifierType value of
        Right underlying
          | interpretedValueKind underlying == EitherValueKind -> Right underlying
        _ -> Right value
    interpretIdentifierOperation
        identifierString typeAnnotationExpression maybeGivenValueExpression = do
      typeAnnotation <- interpret typeAnnotationExpression
      case maybeGivenValueExpression of
        Nothing ->
          runProtectedOperation protection [typeAnnotation] $ \actuals ->
            case actuals of
              [actualAnnotation] -> do
                requireCanonicalTypeAnnotation actualAnnotation
                if identifierString == "False"
                    && interpretedValueKind actualAnnotation
                      == NaturalValueKind
                    && interpretedInteger actualAnnotation == Just 0
                  then Right (booleanValue False)
                  else if identifierString == "True"
                    && interpretedValueKind actualAnnotation
                      == NaturalValueKind
                    && interpretedInteger actualAnnotation == Just 1
                  then Right (booleanValue True)
                  else Right (simpleIdentifierTypeValue
                    identifierString actualAnnotation)
              _ -> Right neverValue
        Just givenValueExpression -> do
          givenValue <- interpret givenValueExpression
          runProtectedOperation
            protection [typeAnnotation, givenValue] $ \actuals ->
              case actuals of
                [actualAnnotation, actualGiven] -> do
                  requireCanonicalTypeAnnotation actualAnnotation
                  case assignIdentifierValues
                      identifierString actualAnnotation actualGiven of
                    Left _
                      | typeAnnotationExpression == givenValueExpression ->
                          Right (inferredIdentifierAssignmentValue
                            identifierString actualGiven)
                    Left
                        (AtlasMapFederationOperationRefuted
                          AtlasMapFederationSpecificationHasNoMatchingMember) ->
                      Left
                        (GivenValueOutsideTypeAnnotation
                          { expectedTypeAnnotation =
                              renderInterpretedValue actualAnnotation
                          , givenValue = renderInterpretedValue actualGiven
                          })
                    result -> result
                _ -> Right neverValue
    unary operation operand = do
      value <- interpret operand
      runProtectedOperation protection [value] $ \actuals ->
        case actuals of
          [actual] -> operation actual
          _ -> Right neverValue
    binary operation left right = do
      leftValue <- interpret left
      rightValue <- interpret right
      runProtectedOperation protection [leftValue, rightValue] $ \actuals ->
        case actuals of
          [actualLeft, actualRight] -> operation actualLeft actualRight
          _ -> Right neverValue
    interpretProtectedValues expressions operation = do
      values <- traverse interpret expressions
      runProtectedOperation protection values operation
    interpretProtectedAtlasMap buildMap expressions = do
      values <- traverse interpret expressions
      runProtectedOperation protection values $ \actuals ->
        Right (buildAtlasMapFromValues buildMap expressions actuals)
    binaryComparison predicate left right = do
      leftValue <- interpret left
      rightValue <- interpret right
      runProtectedOperation protection [leftValue, rightValue] $ \actuals ->
        case actuals of
          [actualLeft, actualRight] -> do
            ordering <- compareIntegerLimitValues actualLeft actualRight
            pure (booleanValue (predicate ordering))
          _ -> Right neverValue
    liftMaybeResult result = case interpretedSemanticResult result of
      CanonicalAssignment "Just" _ _ -> pure result
      _ -> do
        absent <- isStandardNothing result
        if absent
          then standardNothingValue
          else standardOptionalValue result >>= contextuallySpecify result
    unconsList value = do
      count <- maybe
        (Left (FunctionEvaluationFailed FunctionArgumentsRequireFinitePages))
        Right
        (naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap value)))
      if count == 0
        then standardNothingValue
        else do
          headValue <- accessValues value (naturalValue 0)
          tailRange <- naturalRangeUpwardsValue 1
          tailValue <- accessValues value tailRange
          let pair = makeAtlasMap 2
                (map (coalizeMapMemberAt 2) [headValue, tailValue])
          standardOptionalValue pair >>= contextuallySpecify pair
    standardNothingValue =
      interpret (IdentifierReference (IdentifierString "nothing"))
    isStandardNothing value = do
      target <- standardNothingValue
      subfederationValues value target >>= booleanCondition
    standardOptionalValue value = do
      constructor <- interpret (IdentifierReference (IdentifierString "Maybe"))
      input <- functionArgumentValue value
      applyFunction reduction constructor input
    evaluateBlock source bindings result = do
      let origins = canonicalDependencyNames bindings result
          reconstructionScope = if null origins then scope
            else ("\0canonical", CanonicalNames origins) : scope
      imported <- importScope reconstructionScope resolving bindings
      value <- evalInScopeWithProtection protection reduction imported resolving result
      pure (withEvaluationSource source
        (withoutCanonicalDependencies
          (maybe [] pure (scopePresentationDependency imported)) value))

    interpretContainer ordinary container expressions =
      case firstDependentBindingPolarity expressions of
        Nothing -> ordinary
        Just GenericSum -> createDependentSum scope resolving container
        Just GenericProduct -> createDependentProduct scope resolving container
    evaluateFunctionType written preparedDomain preparedCodomain = do
      let (staticDomain, substitutions) =
            staticDependentDomain preparedDomain
          staticCodomain = substituteDependent substitutions preparedCodomain
      input <- compileParameters interpret staticDomain >>= parameterDomain
      output <- interpret staticCodomain
      let signatureText = renderSourceExpression written
      runProtectedOperation protection [input, output] $ \actuals ->
        case actuals of
          [actualInput, actualOutput] -> pure (makeFunctionValue
            (EvaluatedFunction actualInput actualOutput Nothing Nothing Nothing
              signatureText Nothing Nothing True))
          _ -> Right neverValue

syntaxImplementationExpression :: Expression -> Bool
syntaxImplementationExpression FunctionBody {} = True
syntaxImplementationExpression External {} = True
syntaxImplementationExpression _ = False

data DependentBinding = DependentBinding
  { dependentBindingPolarity :: GenericPolarity
  , dependentBindingName :: IdentifierString
  , dependentBindingOptional :: Bool
  , dependentBindingBound :: Expression
  }

dependentBinding :: Expression -> Maybe DependentBinding
dependentBinding expressionValue =
  case expressionValue of
    WithBinding name optional bound ->
      Just (DependentBinding GenericSum name optional bound)
    ForBinding name optional bound ->
      Just (DependentBinding GenericProduct name optional bound)
    _ -> Nothing

firstDependentBindingPolarity
  :: [Expression]
  -> Maybe GenericPolarity
firstDependentBindingPolarity [] = Nothing
firstDependentBindingPolarity (entry : remaining) =
  case dependentBinding entry of
    Just binder -> Just (dependentBindingPolarity binder)
    Nothing -> firstDependentBindingPolarity remaining

duplicateGenericIdentifier
  :: [GenericBinder Expression]
  -> Maybe String
duplicateGenericIdentifier = go []
  where
    go _ [] = Nothing
    go seen (binder : remaining)
      | name `elem` seen = Just name
      | otherwise = go (name : seen) remaining
      where
        GenericIdentifier (IdentifierString name) _ =
          genericBinderIdentifier binder

validateGenericFunctionType
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> [GenericBinder Expression]
  -> Expression
  -> Expression
  -> Either InterpretingError ()
validateGenericFunctionType evaluate generics domain codomain = do
  case duplicateGenericIdentifier generics of
    Just name -> Left (DuplicateGenericIdentifier name)
    Nothing -> pure ()
  case forwardGenericBoundReference generics of
    Just (IdentifierString owner, IdentifierString referenced) ->
      Left (ForwardGenericBoundReference owner referenced)
    Nothing -> pure ()
  let introduced =
        functionTypeIdentifiers domain <> functionTypeIdentifiers codomain
  mapM_ (validateBinder introduced) generics
  where
    validateBinder introduced binder =
      mapM_ (validateIdentifier name) introduced
      where
        GenericIdentifier (IdentifierString name) _ =
          genericBinderIdentifier binder
    validateIdentifier genericName introduced =
      case introduced of
        SimpleFunctionTypeIdentifier (IdentifierString name)
          | name == genericName -> Left (GenericIdentifierOverlap genericName)
          | otherwise -> pure ()
        DependentFunctionTypeIdentifier expressionValue -> do
          identifier <- evaluate expressionValue
          case identifierNameDisjointness genericName identifier of
            IdentifierNameDisjoint -> pure ()
            IdentifierNameOverlap ->
              Left (GenericIdentifierOverlap genericName)
            IdentifierNameDisjointnessUndecidable ->
              Left (GenericIdentifierDisjointnessUndecidable genericName)

resolveIdentifier
  :: Scope -> [String] -> String -> Either InterpretingError InterpretedValue
resolveIdentifier = resolveIdentifierWith UnrestrictedReduction

resolveIdentifierWith
  :: ReductionContext
  -> Scope
  -> [String]
  -> String
  -> Either InterpretingError InterpretedValue
resolveIdentifierWith = resolveIdentifierAccess False

resolveIdentifierIncludingPrivate
  :: ReductionContext
  -> Scope
  -> [String]
  -> String
  -> Either InterpretingError InterpretedValue
resolveIdentifierIncludingPrivate = resolveIdentifierAccess True

resolveIdentifierAccess
  :: Bool
  -> ReductionContext
  -> Scope
  -> [String]
  -> String
  -> Either InterpretingError InterpretedValue
resolveIdentifierAccess includesPrivate reduction scope resolving name =
  case canonicalAlias of
    Just generated -> resolveIdentifierAccess
      includesPrivate reduction scope resolving generated
    Nothing -> case lookup name scope of
      Just binding -> resolve binding
      Nothing -> Left (UnknownIdentifier name)
  where
    canonicalAlias = unique exactAliases `orElse` unique qualifiedAliases
    aliases = concat [names | (_, CanonicalNames names) <- scope]
    exactAliases = [generated | (generated, original) <- aliases, original == name]
    qualifiedAliases =
      [ generated
      | (generated, original) <- aliases
      , reverse (takeWhile (/= '.') (reverse original)) == name
      ]
    unique values = case nub values of
      [value] -> Just value
      _ -> Nothing
    orElse value fallback = case value of
      Just _ -> value
      Nothing -> fallback

    resolve (NamedBinding dependency binding) =
      withCanonicalReference [dependency] name <$> resolve binding
    -- An import-all binding keeps its qualified origin for dependency
    -- reconstruction, but ordinary unqualified lookup denotes the exported
    -- value itself. Retaining the nested NamedBinding presentation here makes
    -- @yield x@ render as @x@ instead of the value exported by the module.
    resolve (QualifiedBinding _ binding) =
      withoutCanonicalPresentation <$> resolve binding
    resolve (ShadowingConsistentBinding binding) = resolve binding
    resolve (EvaluatedBinding value) = Right value
    resolve (PrivateParameterBinding value)
      | includesPrivate = Right value
      | otherwise = Left (UnknownIdentifier name)
    resolve (ContextualBinding surface _ _) =
      contextualFunction surface
        (contextualLevels includesPrivate resolving surface scope)
    resolve (RetainedBinding captured annotation _ value) =
      Right (withCanonicalReference (scopePresentationDependencies captured) name
        (resolveInferredEitherAlias annotation value))
    resolve (ImportedBinding dependency _ value _) =
      Right (withCanonicalReference [dependency] name value)
    resolve ScopeMembers {} =
      contextualFunction "this"
        (contextualLevels includesPrivate resolving "this" scope)
    resolve CanonicalNames {} = Left (UnknownIdentifier name)
    resolve ModuleCatalog {} = Left (UnknownIdentifier name)
    resolve LexicalScope {} = Left (UnknownIdentifier name)
    resolve (DeferredBinding captured annotation expressionValue) =
      withCanonicalReference (scopePresentationDependencies captured) name <$>
        evaluateBindingDefinitionWith reduction
          captured resolving name annotation expressionValue

evaluateBindingDefinitionWith
  :: ReductionContext
  -> Scope
  -> [String]
  -> String
  -> Maybe Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateBindingDefinitionWith reduction captured resolving name annotation expressionValue
  | resolutionKey `elem` resolving =
      case recursiveFunctionImplementation expressionValue of
        Just implementation ->
          evalInScopeWith reduction captured resolving implementation
        Nothing -> Left (CyclicIdentifierReference
          (reverse
            (name : map resolutionName
              (takeWhile (/= resolutionKey) resolving))
            <> [name]))
  | otherwise = do
      case annotation of
        Nothing -> pure ()
        Just typeExpression ->
          evalInScopeWith reduction captured
            (resolutionKey : resolving) typeExpression
            >>= requireCanonicalTypeAnnotation
      resolveInferredEitherAlias annotation
        <$> evaluateDefinition
  where
    resolutionKey = bindingKey name expressionValue
    resolutionName = takeWhile (/= ':')
    evaluateDefinition =
      case expressionValue of
        contextual
          | isContextualAccessOf (IdentifierString "_this") contextual
          , Just _ <- lookup "_this" captured >>= scopeMembersBinding ->
              declarationMap
                (visibleScopeMembers "_this" captured)
                (resolveIdentifierWith reduction captured
                  (resolutionKey : resolving))
        IdentifierReference (IdentifierString reference)
          | Just _ <- lookup reference captured >>= scopeMembersBinding ->
              declarationMap
                (visibleScopeMembers reference captured)
                (resolveIdentifierWith reduction captured
                  (resolutionKey : resolving))
        _ -> evalInScopeWith reduction captured
          (resolutionKey : resolving) expressionValue

-- A declaration-scope reference is a first-class value. When it is aliased,
-- preserve the lexical snapshot at that declaration rather than exposing
-- declarations that occur later in the same block. The binding constructor,
-- not a particular identifier spelling, identifies this implicit reference.
visibleScopeMembers :: String -> Scope -> [String]
visibleScopeMembers reference scope =
  case break isReferencedScope scope of
    (visible, (_, binding) : _)
      | Just names <- scopeMembersBinding binding ->
      let visibleNames = map fst visible
      in [name | name <- names, name `elem` visibleNames]
    _ -> []
  where
    isReferencedScope (name, binding) =
      name == reference && case scopeMembersBinding binding of
        Just _ -> True
        Nothing -> False

resolveInferredEitherAlias
  :: Maybe Expression
  -> InterpretedValue
  -> InterpretedValue
resolveInferredEitherAlias Nothing value =
  case stripOuterIdentifierType value of
    Right underlying
      | interpretedValueKind underlying == EitherValueKind -> underlying
    _ -> value
resolveInferredEitherAlias (Just _) value = value

-- A recursive let-bound function can be used while its public signature is
-- being assembled. The unrefined implementation is the fixed-point seed;
-- once the surrounding definition finishes, normal signature validation
-- replaces it with the fully typed function value.
recursiveFunctionImplementation :: Expression -> Maybe Expression
recursiveFunctionImplementation expressionValue =
  case expressionValue of
    MapSpecification implementation SyntaxType {} -> Just implementation
    MapSpecification implementation FunctionTypeExpression {}
      | External {} <- implementation -> Just implementation
    Begin _ result -> recursiveFunctionImplementation result
    Program _ result -> recursiveFunctionImplementation result
    Let value -> recursiveFunctionImplementation value
    EitherType left right ->
      case recursiveFunctionImplementation left of
        Just implementation -> Just implementation
        Nothing -> recursiveFunctionImplementation right
    OptionalType operand -> recursiveFunctionImplementation operand
    _ -> Nothing

-- A block imports declarations from left to right. Ordinary definitions capture
-- only earlier ordinary definitions, while every let definition is predeclared
-- throughout the block. Lets are forced before yield and their results replace
-- the deferred definitions. Names are checked before evaluating any binding.
importScope :: Scope -> [String] -> [Expression] -> Either InterpretingError Scope
importScope enclosing resolving entries = do
  (rebuild, eagerNames, eagerEntries, validateConsistency) <-
    scopeBuilder enclosing entries
  let deferred = rebuild []
      forced =
        [ name
        | name <- eagerNames
        , maybe True (not . productiveRecursiveBinding name) (lookup name deferred)
        ]
      (seeded, ordinary) = partition
        (maybe False bindingHasRecursiveFunctionSeed . (`lookup` deferred))
        forced
      retainLet retained name = do
        value <- resolveIdentifier (rebuild retained) resolving name
        pure ((name, value) : retained)
  retained <- foldM retainLet [] (seeded <> ordinary)
  let imported = rebuild retained
  validateConsistency resolving imported
  -- Anonymous let entries still have eager evaluation semantics.
  mapM_ (evalInScope imported resolving) eagerEntries
  pure imported

scopePresentationDependency :: Scope -> Maybe PresentationDependency
scopePresentationDependency scope =
  case [dependency | (_, LexicalScope dependency) <- scope] of
    dependency : _ -> Just dependency
    [] -> Nothing

scopePresentationDependencies :: Scope -> [PresentationDependency]
scopePresentationDependencies = maybe [] pure . scopePresentationDependency

childPresentationDependency
  :: Scope
  -> [Expression]
  -> PresentationDependency
childPresentationDependency enclosing entries = PresentationDependency
  (parent <> "/" <> show entries)
  where
    parent = case scopePresentationDependency enclosing of
      Just (PresentationDependency identity) -> identity
      Nothing -> "<root>"

bindingHasRecursiveFunctionSeed :: Binding -> Bool
bindingHasRecursiveFunctionSeed binding =
  case bindingDefinition binding of
    Just (_, _, definition) ->
      case recursiveFunctionImplementation definition of
        Just _ -> True
        Nothing -> False
    Nothing -> False

productiveRecursiveBinding :: String -> Binding -> Bool
productiveRecursiveBinding name binding =
  case bindingDefinition binding of
    Just (_, _, definition) ->
      case recursivePrefixFor
          (== IdentifierReference (IdentifierString name))
          definition of
        Just _ -> True
        Nothing -> False
    _ -> False

-- Source reconstruction needs definitions without forcing native implementations
-- while their signatures are themselves being reconstructed.
declareScope
  :: Scope
  -> [Expression]
  -> Either InterpretingError (Scope, [String], [Expression])
declareScope enclosing entries = do
  (rebuild, eagerNames, eagerEntries, _) <- scopeBuilder enclosing entries
  pure (rebuild [], eagerNames, eagerEntries)

-- Rebuild a declaration scope from its finite source declarations whenever an
-- eager let becomes available.  Recursive lets make their captured scopes
-- cyclic; recursively walking those scopes to replace a binding can therefore
-- black-hole.  Re-running 'buildScopeBindings' ties one fresh, shared knot and
-- places retained values into every lexical snapshot without traversing it.
scopeBuilder
  :: Scope
  -> [Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      )
scopeBuilder enclosing entries = do
  let dependency = childPresentationDependency enclosing entries
      scopedEnclosing = ("\0scope", LexicalScope dependency) : enclosing
  outer <- foldM importModule scopedEnclosing
    [ imported | Just imported <- map importInvocation entries ]
  let (definitions, eagerEntries) = foldMap (bindingImports False) entries
      names = map declarationName definitions
      blockOuter = case lookup "_this" outer >>= contextualBinding of
        Just _ -> outer
        Nothing ->
          scopeBinding "_this" (ScopeMembers names) : outer
      rebuild retained = buildScopeBindings (makeBinding retained)
        blockOuter definitions
      consistencyNames =
        [ name
        | declaration <- definitions
        , let name = declarationName declaration
        , Just binding <- [lookup name blockOuter]
        , not (bindingHasUnrestrictedShadowing binding)
        ]
      validateConsistency resolving imported =
        mapM_ (validateConsistencyName resolving imported) consistencyNames
      validateConsistencyName resolving imported name =
        case lookup name blockOuter of
          -- Whole recursive scope values have no finite normal form to
          -- compare. Consistency cannot be established at this boundary.
          Just binding | bindingHasNoFiniteShadowingNormalForm binding ->
            Left (InconsistentShadowing name)
          _ -> do
            let bounded = ShadowingConsistencyReduction
                  name shadowingConsistencyFuel
            original <- resolveIdentifierWith bounded blockOuter resolving name
            replacement <- resolveIdentifierWith
              bounded
              imported
              resolving
              name
            if interpretedSemanticResult original
                == interpretedSemanticResult replacement
              then Right ()
              else Left (InconsistentShadowing name)
      makeBinding retained captured declaration =
        let name = declarationName declaration
            annotation = declarationAnnotation declaration
            expressionValue = declarationValue declaration
        in case lookup name retained of
          Just value ->
            scopeBinding name
              (RetainedBinding captured annotation expressionValue value)
          Nothing ->
            scopeBinding name
              (DeferredBinding captured annotation expressionValue)
  _ <- foldM (checkName blockOuter) [] definitions
  pure
    ( rebuild
    , [declarationName value | value <- definitions, declarationIsLet value]
    , eagerEntries
    , validateConsistency
    )
  where
    checkName blockOuter declared declaration
      | declarationIsLet declaration
      , Just binding <- lookup name blockOuter
      , not (bindingHasUnrestrictedShadowing binding) =
          Left (LetBindingCannotShadowConsistentIdentifier name)
      | name `elem` declared = Left (IdentifierStringOverlap name)
      | otherwise = Right (name : declared)
      where name = declarationName declaration

importInvocation :: Expression -> Maybe (Bool, String)
importInvocation expressionValue =
  case expressionValue of
    Import allNames path -> Just (allNames, path)
    _ -> Nothing

-- Only declaration-shaped block entries create lexical bindings. Maps and map
-- operators remain values: identifier-shaped members inside them neither enter
-- the surrounding scope nor become visible to sibling members.
bindingImports :: Bool -> Expression -> ([Declaration], [Expression])
bindingImports strict expressionValue =
  case blockDeclaration (if strict then Let expressionValue else expressionValue) of
    Just declaration -> ([declaration], [])
    Nothing -> case expressionValue of
      Let value -> bindingImports True value
      Assert {} -> ([], [expressionValue])
      _ -> ([], [expressionValue | strict])

interpretStringTemplateWith
  :: EvaluationProtectionContext
  -> Interpreter
  -> [StringTemplatePart Expression]
  -> Either InterpretingError InterpretedValue
interpretStringTemplateWith protection interpret parts = do
  values <- traverse interpretPart parts
  case values of
    [] -> asciiStringValue ""
    firstValue : remaining -> do
      result <- foldM concatenateTemplateValues firstValue remaining
      pure (templateValue result)
  where
    interpretPart (StringTemplateLiteral value) = asciiStringValue value
    interpretPart (StringTemplateInterpolation expressionValue) = do
      value <- interpret expressionValue
      runProtectedOperation protection [value] $ \actuals ->
        case actuals of
          [actual] -> toStringValue canonicalStringCodec actual
          _ -> Right neverValue

    concatenateTemplateValues left right =
      case runProtectedOperation protection [left, right] $ \actuals ->
          case actuals of
            [actualLeft, actualRight] ->
              concatenateValues actualLeft actualRight
            _ -> Right neverValue of
        Right value -> Right value
        Left _ -> Left AmbiguousStringTemplate

interpretSpecificationWith
  :: EvaluationProtectionContext
  -> Interpreter
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretSpecificationWith protection interpret sourceExpression targetExpression = do
  source <- interpret sourceExpression
  target <- interpret targetExpression
  let operation = runProtectedOperation protection [source, target] $ \actuals ->
        case actuals of
          [actualSource, actualTarget] ->
            case sourceExpression of
              External _ -> case linkExternalAdapter actualSource actualTarget of
                Just linked -> linked
                Nothing -> specifyValues actualSource actualTarget
              _ -> specifyValues actualSource actualTarget
          _ -> Right neverValue
  case operation of
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

-- External function symbols are callable before a recursive let-bound public
-- signature has finished resolving. Specification links that implementation
-- to the exact source-declared domain and codomain; the adapter itself carries
-- only its calling convention, never a second copy of the public type.
linkExternalAdapter
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (Either InterpretingError InterpretedValue)
linkExternalAdapter source target = do
  implementation <- interpretedFunction source
  signature <- interpretedFunction target
  invoke <- functionInvoke implementation
  Just (Right (makeFunctionValue signature
      { functionSource = functionSource implementation
      , functionPrepare = Just (\argument -> do
          preparedCall <- case functionPrepare implementation of
            Just prepare -> prepare argument
            Nothing -> pure (PreparedFunctionArgument argument argument [])
          preparedCall <$ validateFunctionInput
            (functionPreparedArgument preparedCall) (functionDomain signature))
      , functionInvoke = Just invoke
      , functionValidatesResult = True
      }))

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
    givenValueFor (interpretedSemanticResult source)
  (expectedString, expectedResult) <-
    identifierExpectedValue (interpretedSemanticResult target)
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

buildAtlasMapFromValues
  :: (Natural -> [InterpretedValue] -> InterpretedValue)
  -> [Expression]
  -> [InterpretedValue]
  -> InterpretedValue
buildAtlasMapFromValues buildMap expressions values =
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  in buildMap cardinality (map (coalizeMapMemberAt cardinality) values)

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

-- The ordinary fixed-point spelling of homogeneous finite Atlas maps.  Both
-- explicit concatenation and an explicitly grouped sequence denote the same
-- functor; recognizing it here prevents construction from forcing its tail.
recursiveListElement :: Expression -> Maybe Expression
recursiveListElement expressionValue =
  case expressionValue of
    EitherType (AtlasMap [])
        (MapConcatenation element self)
      | isSelf self ->
      Just element
    EitherType (AtlasMap [])
        (MapSequence [element, self])
      | isSelf self ->
      Just element
    EitherType (AtlasMap [])
        (AtlasMap [element, self])
      | isSelf self ->
      Just element
    MapSequence
        [ EitherType (AtlasMap []) element
        , self
        ] | isSelf self -> Just element
    AtlasMap
        [ EitherType (AtlasMap []) element
        , self
        ] | isSelf self -> Just element
    _ -> Nothing
  where
    isSelf = isContextualAccessOf (IdentifierString "_this")

-- Dependent binders are scoped by their enclosing domain and are introduced
-- strictly from left to right.  Static checking uses each binder's upper
-- bound; invocation repeats the checks with the actual witnesses.
staticDependentDomain :: Expression -> (Expression, [(String, Expression)])
staticDependentDomain expressionValue =
  case expressionValue of
    ArgumentMap entries ->
      let (values, substitutions) = staticEntries [] entries
      in (ArgumentMap values, substitutions)
    AtlasMap entries ->
      let (values, substitutions) = staticEntries [] entries
      in (AtlasMap values, substitutions)
    MapSequence entries ->
      let (values, substitutions) = staticEntries [] entries
      in (MapSequence values, substitutions)
    _ -> staticEntry [] expressionValue
  where
    staticEntries substitutions [] = ([], substitutions)
    staticEntries substitutions (entry : remaining) =
      let (staticValue, afterEntry) = staticEntry substitutions entry
          (staticRemaining, finalSubstitutions) =
            staticEntries afterEntry remaining
      in (staticValue : staticRemaining, finalSubstitutions)
    staticEntry substitutions entry =
      case dependentBinding entry of
        Just binder ->
          let staticBound = substituteDependent substitutions bound
              IdentifierString name = dependentBindingName binder
              optional = dependentBindingOptional binder
              bound = dependentBindingBound binder
          in ( ForBinding (IdentifierString name) optional staticBound
             , (name, staticBound) : substitutions
             )
        Nothing -> (substituteDependent substitutions entry, substitutions)

substituteDependent :: [(String, Expression)] -> Expression -> Expression
substituteDependent substitutions expressionValue =
  case expressionValue of
    IdentifierReference (IdentifierString name) ->
      maybe expressionValue id (lookup name substitutions)
    _ -> mapExpressionChildren
      (substituteDependent substitutions)
      expressionValue

domainEntries :: Expression -> [Expression]
domainEntries expressionValue =
  case expressionValue of
    ArgumentMap entries -> entries
    AtlasMap entries -> entries
    MapSequence entries -> entries
    MapConcatenation left right -> domainEntries left <> domainEntries right
    _ -> [expressionValue]

createDependentSum
  :: Scope
  -> [String]
  -> Expression
  -> Either InterpretingError InterpretedValue
createDependentSum captured resolving written = do
  let evaluate = evalInScope captured resolving
      staticExpression = fst (staticDependentDomain written)
      compiledSchema = compileParameters evaluate staticExpression
  (staticTarget, specify) <- case compiledSchema of
    Right schema -> do
      target <- parameterDomain schema
      pure (target, \source -> do
        supplied <- matchArguments schema source
        _ <- validateDependentMapArguments captured resolving written supplied
        pure source)
    Left symbolicFailure ->
      case representativeDependentTarget captured resolving written of
        Right target -> pure
          (target, \source -> source <$ specifyValues source target)
        Left _ -> Left symbolicFailure
  domain <- dependentSumDomain captured resolving written
  let project insertion =
        projectDependentSum
          captured resolving written staticTarget insertion
      dependent = makeDependentSumValue
        (renderSourceExpression written) staticTarget specify
  pure
    (withDependentSumFamily domain project
      (withDependentSumAccess project dependent))

dependentSumDomain
  :: Scope
  -> [String]
  -> Expression
  -> Either InterpretingError InterpretedValue
dependentSumDomain captured resolving written =
  case domainEntries written of
    WithBinding _ _ boundExpression : _ ->
      evalInScope captured resolving boundExpression
    _ -> Left (DependentBinderOutsideContainer "with")

-- | Interpret a dependent product as its indexed Atlas family. Page zero is
-- the index domain and page one is a lazy map of fibres, so the surface
-- @for i in A do B@ projection uses the same ordinary @[1]@ machinery as
-- every other Atlas value.
createDependentProduct
  :: Scope
  -> [String]
  -> Expression
  -> Either InterpretingError InterpretedValue
createDependentProduct captured resolving written =
  case domainEntries written of
    ForBinding (IdentifierString name) _ boundExpression : entries -> do
      bound <- evalInScope captured resolving boundExpression
      let orderType = interpretedMapFinalOrderType (interpretedMap bound)
          fibreAt position = do
            witness <- maybe
              (Left (FunctionEvaluationFailed
                (FunctionArgumentPageUnavailable 0)))
              Right
              (interpretedMapValueAt (interpretedMap bound) position)
            values <- instantiateDependentEntries
              captured resolving written name witness entries
            case values of
              [] -> Right (makeAtlasMap 0 [])
              [value] -> Right value
              _ -> Right (makeAtlasMap 2 values)
      fibres <- case naturalAtOrdinal orderType of
        Just count -> makeAtlasMap 2 <$> traverse
          (fibreAt . finiteOrdinal)
          (if count == 0 then [] else [0 .. count - 1])
        Nothing -> pure (makeLazyMapValue orderType
          (either (const Nothing) Just . fibreAt))
      pure (makeAtlasMap 2 [bound, fibres])
    _ -> Left (DependentBinderOutsideContainer "for")

-- | Some dependent value expressions cannot be approximated by replacing a
-- binder with its whole upper bound (for example, a range endpoint).  In that
-- case use the first member of the binder federation as a structural fibre;
-- exact checking still happens against the concrete fibre selected later.
representativeDependentTarget
  :: Scope
  -> [String]
  -> Expression
  -> Either InterpretingError InterpretedValue
representativeDependentTarget captured resolving written =
  case domainEntries written of
    WithBinding (IdentifierString name) _ boundExpression : entries -> do
      bound <- evalInScope captured resolving boundExpression
      witness <- maybe
        (Left (FunctionEvaluationFailed
          (FunctionArgumentPageUnavailable 0)))
        Right
        (interpretedMapValueAt
          (interpretedMap bound)
          (finiteOrdinal 0))
      values <- instantiateDependentEntries
        captured resolving written name witness entries
      pure (makeAtlasMap 2 (witness : values))
    _ -> Left (OverloadError OverloadNoMatch)

-- | Project a dependent family by instantiating each fibre only when its
-- Atlas page is demanded.  This is deliberately unaware of clients such as
-- @Args@: the binder's own ordered federation supplies the indices, and the
-- ordinary argument-map machinery decides membership in each projected
-- fibre.
projectDependentSum
  :: Scope
  -> [String]
  -> Expression
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
projectDependentSum captured resolving written staticTarget insertion =
  case domainEntries written of
    WithBinding (IdentifierString name) _ boundExpression : entries -> do
      bound <- evalInScope captured resolving boundExpression
      reservationTarget <-
        case instantiateDependentEntries
            captured resolving written name bound entries of
          Right values -> Right (makeAtlasMap 2 values)
          Left _
            | not (ordinalGT
                (interpretedMapFinalOrderType (interpretedMap bound))
                omega)
            , Right values <- instantiateDependentEntries
                captured resolving written name bound
                (map (dependentFamilyEnvelope name) entries) ->
                  Right (makeAtlasMap 2 values)
          Left _ -> Right staticTarget
      let memberAt witness = do
            values <- instantiateDependentEntries
              captured resolving written name witness entries
            pure (makeAtlasMap 2 (witness : values))
      let orderType = interpretedMapFinalOrderType (interpretedMap bound)
          fibreAtOrdinal position = do
            witness <- maybe
              (Left (FunctionEvaluationFailed
                (FunctionArgumentPageUnavailable 0)))
              Right
              (interpretedMapValueAt (interpretedMap bound) position)
            memberAt witness >>= (`accessValues` insertion)
          lazyMap = makeLazyMapValue orderType
            (either (const Nothing) Just . fibreAtOrdinal)
          projectedMemberAt witness =
            memberAt witness >>= (`accessValues` insertion)
          projection = makeDependentSumValue
            (renderSourceExpression written
              <> "[" <> renderInterpretedValue insertion <> "]")
            lazyMap
            (omegaArgumentValuesComplete
              bound reservationTarget projectedMemberAt)
      pure
        (withDependentSumReservationTarget reservationTarget
          (withDependentSumFamily bound projectedMemberAt
            (withDependentSumAccess (accessValues lazyMap) projection)))
    _ -> accessValues staticTarget insertion

-- | The empty prefix is an exact candidate and therefore has no identifier
-- slots.  For the family-wide named pass, however, a bounded prefix whose
-- upper endpoint is the dependent witness has the ordinary open prefix as
-- its envelope.  This retains the projected dependency without attributing
-- any of its identifiers to the empty candidate itself.
dependentFamilyEnvelope :: String -> Expression -> Expression
dependentFamilyEnvelope name expressionValue =
  case expressionValue of
    SuperEllipsisRange lower
        (IdentifierReference (IdentifierString upperName))
      | upperName == name ->
          SuperEllipsisRangePlus (dependentFamilyEnvelope name lower)
    _ -> mapExpressionChildren
      (dependentFamilyEnvelope name)
      expressionValue

instantiateDependentEntries
  :: Scope
  -> [String]
  -> Expression
  -> String
  -> InterpretedValue
  -> [Expression]
  -> Either InterpretingError [InterpretedValue]
instantiateDependentEntries captured resolving written name witness =
  go [scopeBinding name (EvaluatedBinding witness)]
  where
    go _ [] = Right []
    go dependentScope pending@(entry : remaining) =
      case dependentBinding entry of
        Just _ -> do
          value <- evalInScope (dependentScope <> captured) resolving
            (withDomainEntries written pending)
          pure [value]
        Nothing -> do
          value <- evalInScope (dependentScope <> captured) resolving entry
          later <- go dependentScope remaining
          pure (value : later)

withDomainEntries :: Expression -> [Expression] -> Expression
withDomainEntries written entries =
  case written of
    ArgumentMap _ -> ArgumentMap entries
    MapSequence _ -> MapSequence entries
    _ -> AtlasMap entries

-- | Validate every dependent binder with the same left-to-right scope,
-- independently of whether an entry is a sum or product. Polarity affects
-- the value constructed from the map, not telescope name resolution.
validateDependentMapArguments
  :: Scope
  -> [String]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError Scope
validateDependentMapArguments captured resolving domain supplied =
  validateDependentMapArgumentsExcept [] captured resolving domain supplied

validateDependentMapArgumentsExcept
  :: [String]
  -> Scope
  -> [String]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError Scope
validateDependentMapArgumentsExcept trusted captured resolving domain supplied =
  go [] (domainEntries domain)
  where
    go dependentScope [] = Right dependentScope
    go dependentScope (entry : remaining) =
      case dependentBinding entry of
        Just binder -> do
          let IdentifierString name = dependentBindingName binder
              bound = dependentBindingBound binder
          witness <- maybe (Left (UnknownIdentifier name)) Right
            (lookup name supplied)
          target <- evalInScope (dependentScope <> captured) resolving bound
          _ <- if name `elem` trusted
            then Right witness
            else specifyValues witness target
          go (scopeBinding name (EvaluatedBinding witness) : dependentScope)
            remaining
        Nothing -> case entry of
          IdentifierOperation (IdentifierString name) annotation _ -> do
            validateNamed dependentScope name annotation
            go dependentScope remaining
          optional
            | Just
                (IdentifierOperation (IdentifierString name) annotation _, _)
                <- optionalIdentifierExpression optional -> do
                validateNamed dependentScope name annotation
                go dependentScope remaining
          _ -> go dependentScope remaining
    validateNamed dependentScope name annotation =
      case lookup name supplied of
        Nothing -> Right ()
        Just value -> do
          target <- evalInScope (dependentScope <> captured) resolving annotation
          () <$ specifyValues value target

inferGenericArgument
  :: Scope
  -> [String]
  -> Expression
  -> GenericArgumentBinder
  -> InterpretedValue
  -> [InterpretedValue]
  -> [(GenericArgumentBinder, InterpretedValue)]
  -> Either InterpretingError InterpretedValue
inferGenericArgument captured resolving domain binder _ evidence prior = do
  boundExpression <- maybe
    (Left (UnknownIdentifier name))
    Right
    (dependentBound name (domainEntries domain))
  let currentScope =
        [ scopeBinding (genericArgumentName priorBinder)
            (EvaluatedBinding value)
        | (priorBinder, value) <- prior
        ] <> captured
  bound <- evalInScope currentScope resolving boundExpression
  admissible <- keepSuccessful (`specifyValues` bound) evidence
  case admissible of
    [] -> Left (OverloadError OverloadNoMatch)
    first : remaining -> foldM combineInferenceEvidence first remaining
  where
    name = genericArgumentName binder

    dependentBound _ [] = Nothing
    dependentBound target (entry : remaining) =
      case dependentBinding entry of
        Just dependent
          | dependentBindingName dependent == IdentifierString target ->
              Just (dependentBindingBound dependent)
        _ -> dependentBound target remaining

    keepSuccessful operation = go
      where
        go [] = Right []
        go (value : remaining) = do
          later <- go remaining
          pure (case operation value of
            Right _ -> value : later
            Left _ -> later)

    isSubfederation source target =
      case subfederationValues source target >>= booleanCondition of
        Right included -> Right included
        Left _ -> Right False

    combineInferenceEvidence left right = do
      leftInRight <- isSubfederation left right
      rightInLeft <- isSubfederation right left
      if leftInRight
        then Right right
        else if rightInLeft
          then Right left
          else eitherValue left right


createFunction :: EvaluationProtectionContext -> ReductionContext -> Scope -> [String]
  -> Expression -> Expression -> Expression
  -> [Expression] -> Expression -> Either InterpretingError InterpretedValue
createFunction protection reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result =
  createFunctionWithGenerics protection reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result []

createFunctionWithGenerics
  :: EvaluationProtectionContext
  -> ReductionContext
  -> Scope
  -> [String]
  -> Expression
  -> Expression
  -> Expression
  -> [Expression]
  -> Expression
  -> [GenericBinder Expression]
  -> Either InterpretingError InterpretedValue
createFunctionWithGenerics protection reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result
    generics = do
  let (domainExpression, substitutions) =
        staticDependentDomain writtenDomainExpression
      specifiedOutput = substituteDependent substitutions writtenOutput
  schema <- compileParametersWithGenerics generics evaluate
    writtenDomainExpression domainExpression
  let inferredGenericNames = argumentSchemaInferredGenericNames schema
  let parameters = parameterBindings schema
      names = map fst parameters
      consistencyScope =
        constantContextualBindings "it" anyTypeValue <> captured
      bodyDeclarations =
        [ declaration
        | entry <- bindings
        , Just declaration <- [blockDeclaration entry]
        ]
  -- Reject an unprovable recursive-scope shadow before invocation. Finite
  -- bindings still use the ordinary fixed-point comparison once parameter
  -- values are available.
  case [ name
       | declaration <- bodyDeclarations
       , let name = declarationName declaration
       , Just binding <- [lookup name captured]
       , not (bindingHasUnrestrictedShadowing binding)
       , bindingHasNoFiniteShadowingNormalForm binding
       ] of
    name : _ -> Left (InconsistentShadowing name)
    [] -> pure ()
  case [ name
       | name <- names
       , Just binding <- [lookup name consistencyScope]
       , not (bindingHasUnrestrictedShadowing binding)
       ] of
    name : _ -> Left (InconsistentShadowing name)
    [] -> pure ()
  case [ name
       | name <- names
       , name `elem` map fst captured
          || length (filter (== name) names) > 1
       ] of
    name : _ -> Left (IdentifierStringOverlap name)
    [] -> pure ()
  input <- parameterDomain schema
  let (explicitSelf, selfIncludesDependencies) = case
        lookup "_this" captured >>= contextualBinding of
        Just (includesDependencies, _) -> (True, includesDependencies)
        _ -> (False, False)
  output <- evaluate specifiedOutput
  let prepare argument = do
        (prepared, imported) <- overloadArgumentSchemaCompleteWithGenerics
          (inferGenericArgument captured resolving writtenDomainExpression)
          schema argument
        _ <- validateDependentMapArgumentsExcept inferredGenericNames
          captured resolving writtenDomainExpression imported
        supplied <- if argumentSchemaHasInferredGenerics schema
          then argumentSchemaValidationArgument schema prepared
          else Right argument
        pure (PreparedFunctionArgument supplied prepared imported)
      invoke invocationReduction preparedCall = do
        let argument = functionPreparedArgument preparedCall
            imported = functionPreparedBindings preparedCall
        dependentScope <- validateDependentMapArgumentsExcept
          inferredGenericNames captured resolving writtenDomainExpression imported
        (_, protectedGenerics) <- prepareProtectedGenericDomain
          protection captured resolving generics writtenDomainExpression imported
        let genericNames =
              [ name
              | binder <- generics
              , let GenericIdentifier (IdentifierString name) _ =
                      genericBinderIdentifier binder
              ]
            ordinaryDependentScope =
              [ binding
              | binding@(name, _) <- dependentScope
              , name `notElem` genericNames
              ]
            codomainScope = ordinaryDependentScope <>
              [ scopeBinding name (EvaluatedBinding value)
              | binder <- generics
              , genericBinderPolarity binder == GenericProduct
              , let GenericIdentifier (IdentifierString name) _ =
                      genericBinderIdentifier binder
              , Just value <- [lookup name protectedGenerics]
              , not (valueIsScopeProtected value)
              ]
        let localScope =
              constantContextualBindings "it" argument
                <> [scopeBinding name
                    (if isPrivateIdentifier name
                      then PrivateParameterBinding value
                      else EvaluatedBinding value)
                  | (name,value) <- imported]
                <> captured
        bodyScope <- importScope localScope [] bindings
        value <- evalInScopeWithProtection
          protection invocationReduction bodyScope [] result
        let escaped = withoutCanonicalDependencies
              ( nub
                  ( scopePresentationDependencies bodyScope
                      <> scopePresentationDependencies captured)
              )
              value
        let (_, codomainProtection) =
              enterProtectionScope preparedCall protection
        dynamicOutput <- evalInScopeWithProtection
          codomainProtection invocationReduction
          (codomainScope <> captured) resolving writtenOutput
        contextuallySpecify escaped dynamicOutput
  let signatureText = renderSourceExpression signature
  let definition = MapSpecification (FunctionBody bindings result)
        signature
      self = case [bindingKey name expressionValue
                  | (name, binding) <- captured
                  , Just (_, _, expressionValue) <- [bindingDefinition binding]
                  , expressionValue == definition] of
        key : _ -> Just key
        [] -> Nothing
      closed = closeFunction
        (closureResolver captured)
        self
        explicitSelf
        selfIncludesDependencies
        definition
  pure (makeFunctionValue (EvaluatedFunction input output Nothing Nothing
    (Just (renderSourceExpression closed)) signatureText
    (Just prepare) (Just invoke) False))
  where
    evaluate = evalInScopeWithProtection protection reduction captured resolving

prepareProtectedGenericDomain
  :: EvaluationProtectionContext
  -> Scope
  -> [String]
  -> [GenericBinder Expression]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError
      (EvaluationProtectionContext, [(String, InterpretedValue)])
prepareProtectedGenericDomain
    parent captured resolving generics domain supplied =
  go domainProtection [] generics
  where
    (domainLabel, domainProtection) =
      enterProtectionScope supplied parent

    go context prepared [] = Right (context, reverse prepared)
    go context prepared (binder : remaining) = do
      let GenericIdentifier (IdentifierString name) _ =
            genericBinderIdentifier binder
          dependentScope =
            [ scopeBinding preparedName (EvaluatedBinding value)
            | (preparedName, value) <- prepared
            ]
      witness <- maybe (Left (UnknownIdentifier name)) Right
        (lookup name supplied)
      boundExpression <- maybe (Left (UnknownIdentifier name)) Right
        (dependentBound name (domainEntries domain))
      target <- evalInScopeWithProtection
        context UnrestrictedReduction
        (dependentScope <> captured) resolving boundExpression
      specified <- runProtectedOperation context [witness, target] $ \actuals ->
        case actuals of
          [actualWitness, actualTarget] ->
            specifyValues actualWitness actualTarget
          _ -> Right neverValue
      let protectedWitness =
            case genericBinderPolarity binder of
              GenericSum -> protectGenericExistential domainLabel witness
              GenericProduct ->
                protectWithPoliciesOf context [target, specified] witness
      go context ((name, protectedWitness) : prepared) remaining

    dependentBound _ [] = Nothing
    dependentBound target (entry : remaining) =
      case dependentBinding entry of
        Just dependent
          | dependentBindingName dependent == IdentifierString target ->
              Just (dependentBindingBound dependent)
        _ -> dependentBound target remaining

applyFunction
  :: ReductionContext
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
applyFunction reduction callable input =
  case selectFunctionCandidate preparations of
    Right (function, preparedCall) | Just invoke <- functionInvoke function -> do
      nextReduction <- consumeReduction reduction
      value <- invoke nextReduction preparedCall
      result <- if functionValidatesResult function
        then contextuallySpecify value (functionCodomain function)
        else pure value
      -- A syntax-backed call has its own surface form, and its result semantics
      -- already carries the canonical value produced by that form. Recasting
      -- it as ordinary juxtaposition would invent source such as
      -- @from ((2; 5))@ for a call written @from 2 to 5@.
      let callablePresentations = case functionSyntax function of
            Just _ -> []
            Nothing -> interpretedCanonicalPresentations callable
          inputPresentations = nub
            (interpretedCanonicalPresentations input
              <> [([], interpretedSemanticResult input)])
          applications =
            [ ( nub (functionDependencies <> inputDependencies)
              , CanonicalApplication functionPresentation inputPresentation)
            | (functionDependencies, functionPresentation) <- callablePresentations
            , (inputDependencies, inputPresentation) <- inputPresentations
            ]
      pure (if interpretedTypeIsTotal result
        then result
        else foldr present result applications)
    Right _ -> Left (FunctionEvaluationFailed
      ExternalAdapterRequiresAstCaptures)
    Left failure -> Left failure
  where
    preparations = [(function, prepare function)
      | function <- functionAlternatives callable]
    present (dependencies, CanonicalApplication function argument) =
      withCanonicalApplication dependencies function argument
    present _ = id
    prepare function =
      case attempt input of
        Right prepared -> Right prepared
        Left original -> case stripOuterIdentifierValue input of
          Right erased -> attempt erased
          Left _ -> Left original
      where
        attempt argument = case functionPrepare function of
          Just operation -> operation argument
          Nothing -> PreparedFunctionArgument argument argument []
            <$ validateFunctionInput argument (functionDomain function)

consumeReduction
  :: ReductionContext
  -> Either InterpretingError ReductionContext
consumeReduction UnrestrictedReduction = Right UnrestrictedReduction
consumeReduction (ShadowingConsistencyReduction name remaining)
  | remaining > 0 =
      Right (ShadowingConsistencyReduction name (remaining - 1))
  | otherwise = Left (InconsistentShadowing name)

contextuallySpecify
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
contextuallySpecify source target =
  contextuallySpecifyValues source target >>= contextualSpecificationValue

contextualSpecificationValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
contextualSpecificationValue value =
  case interpretedFederationSpecificationBranches value of
    Just branches -> do
      selected <- traverse contextualSpecificationValue branches
      case selected of
        first : rest -> do
          materialized <- foldM eitherValue first rest
          pure
            (case interpretedFederationSpecificationSourceValue value of
              Just source
                | interpretedSemanticResult source
                    == interpretedSemanticResult materialized -> source
              _ -> materialized)
        [] -> Right value
    Nothing -> maybe (Right value) contextualSpecificationValue
      (interpretedSpecificationSourceValue value)

externalValue
  :: Scope
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
externalValue scope descriptor = do
  resolved <- resolveExternal scope descriptor
  case resolved of
    ResolvedExternalValue value -> Right value
    ResolvedFunctionBody _ -> Left (FunctionEvaluationFailed
      ExternalAdapterRequiresAstCaptures)

data ResolvedExternal
  = ResolvedExternalValue InterpretedValue
  | ResolvedFunctionBody SyntaxFunctionBody

resolveExternal
  :: Scope
  -> InterpretedValue
  -> Either InterpretingError ResolvedExternal
resolveExternal scope descriptor =
  case interpretedSemanticResult descriptor of
    CanonicalAsciiString symbol -> resolve symbol
    canonical -> do
      fields <- fieldsOf canonical
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
        else resolve symbol
  where
    resolve "datra.import" =
      Right (ResolvedExternalValue (importExternal False "datra.import"))
    resolve "datra.importAll" =
      Right (ResolvedExternalValue
        (importExternal True "datra.importAll"))
    resolve symbol = case syntaxFunctionBodyForSymbol symbol of
      Just body -> Right (ResolvedFunctionBody body)
      Nothing -> ResolvedExternalValue <$> registeredExternal symbol
    importExternal allNames symbol =
      unlinkedExternalFunction
        (if allNames then 2 else 1)
        symbol
        (invokeImport allNames)
    invokeImport allNames argument = do
      pathValue <- if allNames
        then accessValues argument (naturalValue 1)
        else Right argument
      requested <- case interpretedSemanticResult pathValue of
        CanonicalAsciiString path -> Right path
        _ -> Left (ExternalEvaluationFailed
          (MissingNativeArgument "path"))
      (_, _, value) <- lookupModule scope requested >>= loadedModuleValue
      if allNames
        then () <$ importAllBindings value
        else requireTotalModuleValue value
      pure (makeAtlasMap 0 [])
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
  "datra.never" -> Right neverValue
  "datra.Ordinal" -> Right ordinalTypeValue
  "datra.Nat" -> naturalTypeValue
  "datra.Int" -> integerTypeValue
  "datra.Char" -> charTypeValue
  "datra.IdenStr" -> Right identifierValueTypeValue
  "datra.public" -> do
    let anyExpression = External (AsciiStringLiteral "datra.Any")
        signatureText = renderSourceExpression
          (FunctionType anyExpression anyExpression)
    pure (makeFunctionValue (EvaluatedFunction
      anyTypeValue anyTypeValue Nothing Nothing
      (Just ("!~" <> show symbol)) signatureText
      (Just (\argument -> Right
        (PreparedFunctionArgument argument argument [])))
      (Just (\_ preparedCall ->
        publicValue (functionPreparedArgument preparedCall))) False))
  "datra.AST" -> Right astTypeValue
  "datra.Expr" -> Right (syntaxCategoryTypeValue ExpressionAST)
  "datra.IdenExp" -> Right (syntaxCategoryTypeValue IdentifierExpressionAST)
  "datra.Block" -> Right (syntaxCategoryTypeValue BlockAST)
  "datra.Template" -> Right templateTypeValue
  "datra.SyntaxTemplate" -> Right syntaxTemplateTypeValue
  "datra.NatRange" -> Right naturalRangeTypeValue
  "datra.IntRange" -> Right integerRangeTypeValue
  "datra.NatValRange" -> Right naturalValuedRangeTypeValue
  "datra.IntValRange" -> Right integerValuedRangeTypeValue
  "datra.from" -> nativeRange ValuedIntegerRangeKind
  "datra.range" -> nativeRange IntegerRangeKind
  "datra.add" -> nativeFunction
    (ArgumentMap [optional "a" IntegerType, optional "b" IntegerType]) IntegerType $ \arguments -> do
      a <- lookupArgument "a" arguments
      b <- lookupArgument "b" arguments
      addValues a b
  "datra.abs" -> nativeFunction (optional "value" IntegerType) NaturalType $ \arguments -> do
    value <- lookupArgument "value" arguments
    integer <- requireFiniteInteger LeftOperand value
    pure (integerValue (abs integer))
  "datra.len" -> Right (unlinkedExternalFunction 1 symbol mapLengthValue)
  "datra.ordinal.sum" -> ordinalBinaryNative ordinalOperandType ordinalSumValues
  "datra.ordinal.prod" -> ordinalBinaryNative ordinalOperandType ordinalProductValues
  "datra.ordinal.minus" -> ordinalBinaryNative ordinalOperandType ordinalMinusValues
  "datra.ordinal.exp" -> nativeFunction
    (ArgumentMap
      [optional "x" ordinalOperandType, optional "power" NaturalType]) ordinalOperandType $ \arguments -> do
        ordinalValue <- lookupArgument "x" arguments
        power <- lookupArgument "power" arguments
        ordinalExponentValues ordinalValue power
  "datra.ordinal.lt" -> ordinalComparisonNative ordinalLTValues
  "datra.ordinal.lte" -> ordinalComparisonNative ordinalLTEValues
  "datra.ordinal.gt" -> ordinalComparisonNative ordinalGTValues
  "datra.ordinal.gte" -> ordinalComparisonNative ordinalGTEValues
  _ -> Left (ExternalEvaluationFailed (UnknownExternalSymbol symbol))
  where
    nativeRange kind = do
      let invoke argument = do
            startValue <- accessValues argument (naturalValue 0)
            endValue <- accessValues argument (naturalValue 1)
            integerLimitRangeValue kind startValue endValue
      pure (unlinkedExternalFunction 2 symbol invoke)
    optional name target =
      OptionalType (IdentifierOperation (IdentifierString name) target Nothing)
    lookupArgument name values = maybe
      (Left (ExternalEvaluationFailed (MissingNativeArgument name)))
      Right
      (lookup name values)
    ordinalOperandType = EitherType
      (External (AsciiStringLiteral "datra.Ordinal")) NaturalType
    ordinalBinaryDomain = ArgumentMap
      [ optional "x" ordinalOperandType
      , optional "y" ordinalOperandType
      ]
    ordinalBinaryNative output operation = nativeFunction
      ordinalBinaryDomain output $ \arguments -> do
          left <- lookupArgument "x" arguments
          right <- lookupArgument "y" arguments
          operation left right
    ordinalComparisonNative operation = ordinalBinaryNative BooleanType $ \left right ->
      booleanValue <$> operation left right
    nativeFunction domain codomain implementation = do
      let evaluate = evalInScope [] []
      schema <- compileParameters evaluate domain
      input <- parameterDomain schema
      output <- evaluate codomain
      let prepare argument = do
            (prepared, bindings) <- overloadArgumentSchemaComplete schema argument
            pure (PreparedFunctionArgument argument prepared bindings)
          invoke _ preparedCall = do
            result <- implementation (functionPreparedBindings preparedCall)
            _ <- specifyValues result output
            pure result
      let signatureText = renderSourceExpression
            (FunctionType domain codomain)
      pure (makeFunctionValue (EvaluatedFunction input output Nothing Nothing
        (Just ("!~" <> show symbol)) signatureText
        (Just prepare) (Just invoke) True))

unlinkedExternalFunction
  :: Int
  -> String
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
unlinkedExternalFunction arity symbol invoke =
  makeFunctionValue (EvaluatedFunction domain anyTypeValue Nothing Nothing
    (Just ("!~" <> show symbol)) signatureText Nothing
    (Just (\_ preparedCall -> invoke
      (functionSuppliedArgument preparedCall))) False)
  where
    domain
      | arity == 1 = anyTypeValue
      | otherwise = makeAtlasMap 2 (replicate arity anyTypeValue)
    anyExpression = External (AsciiStringLiteral "datra.Any")
    domainExpression
      | arity == 1 = anyExpression
      | otherwise = AtlasMap (replicate arity anyExpression)
    signatureText = renderSourceExpression
      (FunctionType domainExpression anyExpression)


importModule :: Scope -> (Bool, String) -> Either InterpretingError Scope
importModule scope (allNames, requested) = do
  source <- lookupModule scope requested
  importLoadedModule scope allNames source

importLoadedModule
  :: Scope
  -> Bool
  -> ModuleSource
  -> Either InterpretingError Scope
importLoadedModule scope allNames source = do
  (identity, namespace, value) <- loadedModuleValueWithBase [] source
  exportedValues <- if allNames
    then importAllBindings value
    else requireTotalModuleValue value >> pure []
  internal <- moduleScopeWithBase [] source
  let exported =
        [ ModuleExport name presentation
            (maybe evaluated (retainExportDefinition evaluated)
              (lookup name internal))
        | ModuleExport name presentation evaluated <- exportedValues
        ]
      dependency = case scopePresentationDependency scope of
        Just current -> current
        Nothing -> PresentationDependency ("import:" <> identity)
      namedExports =
        [ scopeBinding name
            (case presentation of
              ModularImportPresentation -> NamedBinding
                (modularPresentationDependency identity)
                (QualifiedBinding (namespace <> "." <> name) binding)
              TransparentImportPresentation -> QualifiedBinding
                (namespace <> "." <> name)
                (NamedBinding dependency binding))
        | ModuleExport name presentation binding <- exported
        ]
  (alreadyImported, namespaceScope) <- case lookup namespace scope of
    Nothing -> pure
      (False,
        (namespace, ImportedBinding dependency identity value internal) : scope)
    Just (ImportedBinding _ previous _ _) | previous == identity ->
      pure (True, scope)
    _ -> Left (IdentifierStringOverlap namespace)
  if allNames
    then foldM (insertExport alreadyImported) namespaceScope
      namedExports
    else pure namespaceScope
  where
    insertExport alreadyImported values entry@(name,_) = case lookup name values of
      Nothing -> Right (entry:values)
      Just _ | alreadyImported -> Right values
      _ -> Left (IdentifierStringOverlap name)

loadedModuleValue
  :: ModuleSource
  -> Either InterpretingError (FilePath, String, InterpretedValue)
loadedModuleValue = loadedModuleValueWithBase []

loadedModuleValueWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError (FilePath, String, InterpretedValue)
loadedModuleValueWithBase base
    moduleSource@(ModuleSource path expression dependencies) = do
  name <- moduleName moduleSource
  (_, annotation, given) <- case yieldedIdentifier expression of
    Just binding -> Right binding
    Nothing -> Left (ModuleEvaluationFailed
      ImportedModuleRequiresSimpleIdentifierType)
  scope <- importScope
    ( ("\0scope", LexicalScope (PresentationDependency ("module:" <> path)))
        : ("\0imports", ModuleCatalog ((path, moduleSource) : dependencies))
        : base
    )
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
  pure (map moduleExportName exported)

moduleSyntaxRules
  :: String
  -> ModuleSource
  -> Either InterpretingError [SyntaxRule]
moduleSyntaxRules requested source = do
  (_, _, value) <- loadedModuleValue source
  moduleSyntaxRulesFromValue requested value

moduleSyntaxRulesFromValue
  :: String
  -> InterpretedValue
  -> Either InterpretingError [SyntaxRule]
moduleSyntaxRulesFromValue requested moduleValue = do
  members <- case namedMembers moduleValue of
    Right named -> Right named
    Left (ModuleEvaluationFailed ImportedModuleRequiresNamedExports) -> Right []
    Left failure -> Left failure
  concat <$> traverse memberRules members
  where
    memberRules (name, memberValue) = concat <$>
      traverse (functionRules name) (functionAlternatives memberValue)
    functionRules name function = case functionSyntaxSource function of
      Nothing -> pure []
      Just (FunctionSyntax templates) -> do
        sourceTemplates <- traverse
          (traverseSyntaxTemplate parseScopedRuleExpression)
          templates
        signature <- parseRuleExpression (functionSignatureSource function)
        implementation <- maybe
          (pure (IdentifierReference (IdentifierString name)))
          parseRuleExpression
          (functionSource function)
        pure
          [ SyntaxRule
              name template signature False (Just requested) implementation
          | template <- sourceTemplates
          ]
    parseScopedRuleExpression sourceText = do
      expressionValue <- parseRuleExpression sourceText
      pure (case expressionValue of
        AsciiStringLiteral {} -> expressionValue
        _ -> InModule requested expressionValue)
    parseRuleExpression sourceText =
      case parseDatra ("(" <> sourceText <> "\n)") of
        Right expressionValue -> Right expressionValue
        Left _ -> Left NoCanonicalStringConversion

moduleName :: ModuleSource -> Either InterpretingError String
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
  -> Either InterpretingError [ModuleExport]
importAllBindings value
  | not (interpretedTypeIsTotal value) = invalid
  | not (all isSimpleIdentifier members) = invalid
  | otherwise =
      case namedBindings value of
        Right bindings -> Right bindings
        Left _ -> invalid
  where
    members = case interpretedSemanticResult value of
      CanonicalMap _ values -> values
      CanonicalConcatenation values -> values
      _ -> []
    isSimpleIdentifier CanonicalSimpleIdentifierType {} = True
    isSimpleIdentifier CanonicalAssignment {} = True
    isSimpleIdentifier _ = False
    invalid = Left (ModuleEvaluationFailed
      ImportAllRequiresTotalMapOfSimpleIdentifierTypes)

scopeMemberNames :: Scope -> [String]
scopeMemberNames scope = case lookup "_this" scope of
  Just binding | Just names <- scopeMembersBinding binding -> names
  _ -> []

publicValue :: InterpretedValue -> Either InterpretingError InterpretedValue
publicValue value = do
  members <- namedMembers value
  pure (makeAtlasMap 2 (map snd (public members)))

namedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
namedMembers value = case interpretedSemanticResult value of
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

namedBindings
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
namedBindings value = namedMembers value >>= traverse field
  where
    field (name, selected) = do
      payload <- accessValues selected (naturalValue 1)
      pure (ModuleExport
        name
        (if hasTrailingIdentifierMarker modularMarker selected
          then ModularImportPresentation
          else TransparentImportPresentation)
        (EvaluatedBinding payload))

modularMarker :: String
modularMarker = "Modular"

-- A modular name is owned by the exporting module, rather than by the lexical
-- scope that happened to import it. Keeping those dependencies distinct makes
-- the canonical spelling survive both explicit and implicit imports.
modularPresentationDependency :: FilePath -> PresentationDependency
modularPresentationDependency identity =
  PresentationDependency ("modular:" <> identity)

modularValue :: InterpretedValue -> Either InterpretingError InterpretedValue
modularValue value = do
  members <- either (const invalid) Right (namedMembers value)
  case
      [ name
      | (name, member) <- members
      , hasTrailingIdentifierMarker modularMarker member
      ] of
    name : _ -> Left (ModuleEvaluationFailed
      (ModularIdentifierAlreadyMarked name))
    [] -> pure (makeAtlasMap 2
      [ withTrailingIdentifierMarker modularMarker member
      | (_, member) <- members
      ])
  where
    invalid = Left (ModuleEvaluationFailed
      ModularRequiresTotalMapOfSimpleIdentifierTypes)

lookupModule :: Scope -> String -> Either InterpretingError ModuleSource
lookupModule scope path
  | value : _ <-
      [ source
      | (_, ModuleCatalog modules) <- scope
      , Just source <- [lookup path modules]
      ] = Right value
  | otherwise = Left (ModuleEvaluationFailed (ModuleNotLoaded path))

-- Imported values and their definition scopes form one module instance.
-- Re-evaluating a module to enter an 'InModule' expression would duplicate
-- that instance and can recursively bootstrap the same module again.
lookupModuleDefinitionScope
  :: Scope
  -> String
  -> Either InterpretingError Scope
lookupModuleDefinitionScope scope path =
  case
      [ imported
      | (_, ImportedBinding _ identity _ imported) <- scope
      , identity == path
      ] of
    imported : _ -> Right imported
    [] -> lookupModule scope path >>= moduleScope

moduleScope :: ModuleSource -> Either InterpretingError Scope
moduleScope = moduleScopeWithBase []

moduleScopeWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError Scope
moduleScopeWithBase base
    moduleSource@(ModuleSource path expression dependencies) = do
  _ <- declaredModuleName expression
  outer <- importScope
    (("\0imports", ModuleCatalog ((path, moduleSource) : dependencies)) : base)
    []
    (resourceBindings expression)
  case namedBeginBlock expression of
    Just (_, declarations, _) ->
      importScope outer [] declarations
    Nothing -> Right outer

resourceBindings :: Expression -> [Expression]
resourceBindings (Program bindings _) = bindings
resourceBindings _ = []

-- | Source provenance survives eager let evaluation. Ordinary definitions
-- already retain their lexical scope; both use the same reconstruction path.
bindingDefinition :: Binding -> Maybe (Scope, Maybe Expression, Expression)
bindingDefinition (ShadowingConsistentBinding binding) = bindingDefinition binding
bindingDefinition (NamedBinding _ binding) = bindingDefinition binding
bindingDefinition (QualifiedBinding _ binding) = bindingDefinition binding
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
    resolver = Resolver resolve moduleResolver scopeIndex contextualDepth
    scopeIndex expressionValue = do
      index <- either (const Nothing) Just (evalInScope scope [] expressionValue)
      either (const Nothing) id (selectedDeclarationName (scopeMemberNames scope) index)
    moduleResolver path = case
        [ imported
        | (_, ImportedBinding _ identity _ imported) <- scope
        , identity == path
        ] of
      imported : _ -> Just (closureResolver imported)
      [] -> case lookupModuleDefinitionScope scope path of
        Right imported -> Just (closureResolver imported)
        Left _ -> Nothing
    contextualDepth name depth = do
      let selected = FunctionApplication
            (IdentifierReference (IdentifierString name))
            (EllipsisNatural depth)
      value <- either (const Nothing) Just (evalInScope scope [] selected)
      expressionValue <- either (const Nothing) Just (valueExpression value)
      pure (Dependency
        (name <> ":" <> show depth <> ":" <> show expressionValue)
        (dropWhile (== '_') name <> "_" <> show depth)
        expressionValue
        emptyResolver)
    resolve [] = Nothing
    -- FunctionClosure tags the exact expansion of @~name@ so it remains
    -- distinguishable from an ordinary @_this.name@ access. Both select the
    -- named lexical binding here, but the tagged form must be resolved as one
    -- dependency rather than traversed into and projected a second time.
    resolve ["\0this", name] = resolve [name]
    resolve ["_this", name] = resolve [name]
    resolve (name : fields@(_ : _))
      | Just (ImportedBinding _ identity _ imported) <- lookup name scope
      , Just dependency <- resolveDependency (closureResolver imported) fields =
          Just dependency
            { dependencyKey = identity <> ":" <> dependencyKey dependency
            , dependencyName = originName name <> "." <> dependencyName dependency
            , dependencyExpression = normalizeExpression
                (dependencyExpression dependency)
            }
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
      | Just binding <- lookup name scope
      , Just origin <- qualifiedBindingOrigin binding = origin
      | otherwise = name
    qualifiedBindingOrigin (QualifiedBinding origin _) = Just origin
    qualifiedBindingOrigin (NamedBinding _ target) =
      qualifiedBindingOrigin target
    qualifiedBindingOrigin (ShadowingConsistentBinding target) =
      qualifiedBindingOrigin target
    qualifiedBindingOrigin _ = Nothing
emptyResolver :: Resolver
emptyResolver = Resolver
  (const Nothing)
  (const Nothing)
  (const Nothing)
  (\_ _ -> Nothing)

-- Render/parse remains the bridge from evaluated values to the shared AST.
-- Resolve library spellings from the library source, using the same lexical
-- dependency traversal as closures rather than a second primitive registry.
valueExpression :: InterpretedValue -> Either InterpretingError Expression
valueExpression = closedSourceExpression . renderCanonicalResult . interpretedSemanticResult

closedSourceExpression :: String -> Either InterpretingError Expression
closedSourceExpression text = do
  expressionValue <- parsedSourceExpression text
  definitions <- defaultDefinitionScope
  pure (inlineDependencies (closureResolver definitions) expressionValue)

parsedSourceExpression :: String -> Either InterpretingError Expression
parsedSourceExpression text = do
  expressionValue <- either (const (Left NoCanonicalStringConversion)) Right
    (parseDatra ("(" <> text <> "\n)"))
  pure (normalizeExpression expressionValue)

defaultDefinitionScope :: Either InterpretingError Scope
defaultDefinitionScope = defaultModuleSource >>= moduleScopeWithBase []
