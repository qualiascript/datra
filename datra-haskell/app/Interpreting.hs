{-# LANGUAGE PatternSynonyms #-}

-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( ModuleSource (..)
  , EvaluationMode (..)
  , moduleExportNames
  , moduleSyntaxRules
  , importInvocation
  , StandardLibraryVisibility (..)
  , ParsedDatraSource
  , parseDatraSourceSyntax
  , parsedSourceImportInvocations
  , rewriteParsedDatraSourceWithImports
  , parseDatraSourceLocatedWithImportsAndStandardLibrary
  , parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
  , interpretLocatedWithImports
  , interpretLocatedWithImportsInMode
  , interpretLocatedWithImportsInModeAndStandardLibrary
  , interpretLocatedWithImportsInModeAndStandardLibraryVisibility
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
import Data.Maybe (catMaybes)
import BlockScope
import FunctionClosure
import DatraHost
  ( datraHostIdentifier
  , datraHostValue
  , namedMembers
  )
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
  , GenericBinderId
  , GenericIdentifier (..)
  , GenericIntroduction (..)
  , GenericPolarity (..)
  , GenericReference (..)
  , IdentifierString (IdentifierString)
  , StringTemplatePart (..)
  , namedBeginBlock
  , normalizeExpression
  , optionalIdentifierExpression
  , isContextualAccessOf
  , expressionChildren
  , mapExpressionChildren
  )
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (FunctionSyntax)
  , SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , mapSyntaxHoleKind
  , traverseSyntaxTemplate
  )
import DatraTypes
import Parsing
  ( FunctionTypeIdentifier (..)
  , forwardGenericBoundReference
  , functionTypeIdentifiers
  , inferredFunction
  , prepareFunctionDomainExpression
  , prepareGenericExpression
  , parseDatra
  , parseDatraRawLocatedWithSourceName
  , resolveGenericFunctionTypes
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
  ( SyntaxRule (..)
  , SyntaxTemplateCompilationFailure (..)
  , compileSyntaxTemplatesFromExpression
  , declarationRules
  )
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application (ParseFailure (..))
import Numeric.Natural (Natural)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import System.FilePath (takeFileName)

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
    includeStandardLibrary =
  parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
    (if includeStandardLibrary
      then AllStandardLibrary
      else NoStandardLibrary)

data StandardLibraryVisibility
  = NoStandardLibrary
  | QualifiedStandardLibrary
  | AllStandardLibrary
  deriving (Eq, Show)

data ParsedDatraSource = ParsedDatraSource
  { parsedEnvelope :: ResourceEnvelope
  , parsedRawExpression :: Located Expression
  , parsedBaseScope :: Scope
  , parsedStandardRules :: [SyntaxRule]
  , parsedBaseModuleRules :: [(String, String, [SyntaxRule])]
  }

parseDatraSourceSyntax
  :: StandardLibraryVisibility
  -> FilePath
  -> String
  -> Either ParseFailure ParsedDatraSource
parseDatraSourceSyntax standardLibraryVisibility sourceName source = do
  (envelope, locatedRaw@(Located _ raw)) <-
    parseDatraRawLocatedWithSourceName sourceName source
  (base, standardRules, baseModuleRules) <-
    Bifunctor.first (ParseFailure . show)
      (standardLibraryParsingEnvironment standardLibraryVisibility raw)
  pure ParsedDatraSource
    { parsedEnvelope = envelope
    , parsedRawExpression = locatedRaw
    , parsedBaseScope = base
    , parsedStandardRules = standardRules
    , parsedBaseModuleRules = baseModuleRules
    }

parsedSourceImportInvocations
  :: ParsedDatraSource
  -> Either ParseFailure [[String]]
parsedSourceImportInvocations parsed =
  discoverImportInvocations base activeRules envelope raw
  where
    envelope = parsedEnvelope parsed
    Located _ raw = parsedRawExpression parsed
    base = parsedBaseScope parsed
    activeRules = parsedStandardRules parsed

parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> [(String, ModuleSource)]
  -> FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseDatraSourceLocatedWithImportsAndStandardLibraryVisibility
    standardLibraryVisibility modules sourceName source = do
  parsed <- parseDatraSourceSyntax
    standardLibraryVisibility sourceName source
  rewriteParsedDatraSourceWithImports modules parsed

rewriteParsedDatraSourceWithImports
  :: [(String, ModuleSource)]
  -> ParsedDatraSource
  -> Either ParseFailure (Located Expression)
rewriteParsedDatraSourceWithImports modules parsed = do
  let dependencyRules =
        [ (requested, namespace, rules)
        | (requested, source) <- modules
        , Right ruleSets <- [moduleSyntaxRuleSets requested source]
        , (namespace, rules) <- ruleSets
        ]
      availableModuleRules = baseModuleRules <> dependencyRules
      initialRules = standardRules
      classify = classifySyntaxHole base modules
      capture = captureSyntaxHole base modules
      scopedRules = importedSyntaxRules base modules availableModuleRules
      rewrite = case (envelope, raw) of
        (ExplicitMapEnvelope, expressionValue) ->
          rewriteExplicitSyntax
            classify capture scopedRules (evaluateSyntaxValue base modules)
            initialRules [] expressionValue
        (ImplicitBlockEnvelope, Begin entries _) ->
          rewriteImplicitSyntax
            classify capture scopedRules (evaluateSyntaxValue base modules)
            initialRules [] entries
        _ -> Left MissingImplicitBlockResult
  expressionValue <- Bifunctor.first rewriteParseFailure rewrite
  pure (Located sourceSpan (resolveGenericFunctionTypes expressionValue))
  where
    envelope = parsedEnvelope parsed
    Located sourceSpan raw = parsedRawExpression parsed
    base = parsedBaseScope parsed
    standardRules = parsedStandardRules parsed
    baseModuleRules = parsedBaseModuleRules parsed
    rewriteParseFailure = ParseFailure . show

importedSyntaxRules
  :: Scope
  -> [(String, ModuleSource)]
  -> [(String, String, [SyntaxRule])]
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
importedSyntaxRules base modules availableRules =
  scopeSyntaxRules
    (classifySyntaxHole base modules)
    [ (namespace, rules)
    | (_, namespace, rules) <- availableRules
    ]

discoverImportInvocations
  :: Scope
  -> [SyntaxRule]
  -> ResourceEnvelope
  -> Expression
  -> Either ParseFailure [[String]]
discoverImportInvocations base activeRules envelope raw = do
  baseModuleRules <- Bifunctor.first (ParseFailure . show) $ traverse
    (\(namespace, identity, value) -> do
      rules <- moduleSyntaxRulesFromValueIn identity namespace value
      pure (namespace, rules))
    [ (namespace, identity, value)
    | (namespace, ImportedBinding _ identity value _) <- scopeBindings base
    ]
  let scoped = scopeSyntaxRules classify baseModuleRules
  rewritten <- Bifunctor.first (ParseFailure . show) $ case (envelope, raw) of
    (ExplicitMapEnvelope, expressionValue) ->
      rewriteExplicitSyntax classify capture scoped
        (evaluateSyntaxValue base []) activeRules [] expressionValue
    (ImplicitBlockEnvelope, Begin entries _) ->
      rewriteImplicitSyntax classify capture scoped
        (evaluateSyntaxValue base []) activeRules [] entries
    _ -> Left MissingImplicitBlockResult
  pure (nub (importsInExpansion rewritten))
  where
    classify = classifySyntaxHole base []
    capture strict declarations previous kind value =
      captureSyntaxHole base [] strict declarations previous kind value
    importsInExpansion expressionValue =
      maybe [] pure (importInvocation expressionValue)
        <> concatMap importsInExpansion (expressionChildren expressionValue)

scopeSyntaxNamespaces :: Expression -> [String]
scopeSyntaxNamespaces source = case source of
  IdentifierReference (IdentifierString selected) -> [selected]
  ArgumentMap modules -> concatMap scopeSyntaxNamespaces modules
  _ -> []

scopeSyntaxRules
  :: ([Expression] -> SyntaxHoleKind Expression -> SyntaxHoleKind Expression)
  -> [(String, [SyntaxRule])]
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
scopeSyntaxRules classify availableRules declarations source =
  localSyntaxRules classify declarations source <>
  concat
    [ rules
    | selected <- scopeSyntaxNamespaces source
    , (namespace, rules) <- availableRules
    , namespace == selected
    ]

-- A lexical map can introduce syntax in exactly the same way as an imported
-- module.  Its rules are visible only on the right side of an access to that
-- map, and are specialized against the declarations visible both outside and
-- inside the map.
localSyntaxRules
  :: ([Expression] -> SyntaxHoleKind Expression -> SyntaxHoleKind Expression)
  -> [Expression]
  -> Expression
  -> [SyntaxRule]
localSyntaxRules classify declarations source =
  case localScopeDeclarations declarations source of
    [] -> []
    local -> snd (foldl introduce (enclosingDeclarations, []) local)
  where
    enclosingDeclarations = case localScopeName source of
      Nothing -> declarations
      Just name -> filter (notElem name . bindingNames) declarations
    introduce (visible, rules) declaration =
      (retainedDeclarations <> [declaration], retainedRules <> introduced)
      where
        names = bindingNames declaration
        retainedDeclarations = filter
          (null . filter (`elem` names) . bindingNames)
          visible
        retainedRules = filter ((`notElem` names) . syntaxName) rules
        introduced = map (specialize visible) (declarationRules declaration)
    specialize visible rule = rule
      { syntaxTemplate = specializeTemplate visible (syntaxTemplate rule) }
    specializeTemplate visible (SyntaxTemplate pieces) = SyntaxTemplate
      [ case piece of
          SyntaxHole kind -> SyntaxHole (classify visible kind)
          SyntaxLiteral {} -> piece
      | piece <- pieces
      ]

localScopeName :: Expression -> Maybe String
localScopeName source = case source of
  IdentifierReference (IdentifierString name) -> Just name
  SyntaxBoundary inner -> localScopeName inner
  _ -> Nothing

localScopeDeclarations :: [Expression] -> Expression -> [Expression]
localScopeDeclarations declarations source = case source of
  IdentifierReference (IdentifierString name) ->
    case
        [ declarationValue binding
        | declaration <- reverse declarations
        , Just binding <- [blockDeclaration declaration]
        , declarationName binding == name
        ] of
      value : _ -> mapScopeEntries value
      [] -> []
  SyntaxBoundary inner -> localScopeDeclarations declarations inner
  _ -> []

mapScopeEntries :: Expression -> [Expression]
mapScopeEntries value = case value of
  AtlasMap entries -> entries
  MapSequence entries -> entries
  MapConcatenation left right ->
    mapScopeEntries left <> mapScopeEntries right
  SyntaxBoundary inner -> mapScopeEntries inner
  _ -> []

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
    ExpressionSyntaxHole {} -> Just captured
    BlockSyntaxHole {} -> case captured of
      AtlasMap {} -> Just captured
      _ -> Nothing
    FunctionBodySyntaxHole {} -> case captured of
      FunctionBody {} -> Just captured
      _ -> Nothing
    IdentifierExpressionSyntaxHole {} -> identifierSyntaxCapture captured
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
    identifierSyntaxCapture value = case value of
      IdentifierReference {} -> Just value
      AsciiStringLiteral {} -> Just value
      StringTemplate {} -> Just value
      OptionalType inner -> OptionalType <$> identifierSyntaxCapture inner
      _ -> Nothing
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
        enclosing = extendScope [("\0imports", ModuleCatalog modules)] base
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
    enclosing = extendScope [("\0imports", ModuleCatalog modules)] base

evaluateSyntaxValue
  :: Scope
  -> [(String, ModuleSource)]
  -> [Expression]
  -> Expression
  -> Maybe InterpretedValue
evaluateSyntaxValue base modules declarations expressionValue = do
  let enclosing = extendScope [("\0imports", ModuleCatalog modules)] base
  (scope, _, _) <- either (const Nothing) Just
    (declareScope enclosing
      (map syntaxValidationDeclaration declarations))
  either (const Nothing) Just (evalInScope scope [] expressionValue)

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
  Let (Val (IdentifierOperation name _ (Just definition)))
    | Just implementation <- recursiveFunctionImplementation definition ->
        Let (Val
          (IdentifierOperation name implementation (Just implementation)))
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
    includeStandardLibrary =
  interpretLocatedWithImportsInModeAndStandardLibraryVisibility
    (if includeStandardLibrary then AllStandardLibrary else NoStandardLibrary)

interpretLocatedWithImportsInModeAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> EvaluationMode
  -> [(String, ModuleSource)]
  -> Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedWithImportsInModeAndStandardLibraryVisibility
    visibility mode modules (Located sourceSpan expression) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretWithImportsInModeAndStandardLibraryVisibility
      visibility mode modules expression)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason expressionValue = do
  validateFunctionBodyParts expressionValue
  scope <- defaultImportScope
  evalInScope scope [] expressionValue

-- | Evaluate a closed reconstruction without importing Std or any modules.
interpretClosedExpression :: Expression -> Either InterpretingError InterpretedValue
interpretClosedExpression expressionValue = do
  validateFunctionBodyParts expressionValue
  scope <- rootScopeWithDatra expressionValue []
  evalInScope scope [] expressionValue

interpretWithImports :: [(String, ModuleSource)] -> Expression -> Either InterpretingError InterpretedValue
interpretWithImports modules expression = do
  validateEvaluationSources modules expression
  scope <- defaultImportScope
  evalResourceInScopeWith UnrestrictedReduction
    (extendScope [("\0imports", ModuleCatalog modules)] scope)
    [] expression

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
    includeStandardLibrary =
  interpretWithImportsInModeAndStandardLibraryVisibility
    (if includeStandardLibrary then AllStandardLibrary else NoStandardLibrary)

interpretWithImportsInModeAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> EvaluationMode
  -> [(String, ModuleSource)]
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithImportsInModeAndStandardLibraryVisibility
    visibility mode modules expression = do
  validateEvaluationSources modules expression
  (base, _) <- standardLibraryEnvironment visibility expression
  evalResourceInScopeWith UnrestrictedReduction
    (extendScope
      [("\0imports", ModuleCatalog (modulesForMode mode modules))]
      base)
    []
    (expressionForMode mode expression)

-- Validate the written tree before evaluation-mode lowering can erase soft
-- assertions. A pre-yield part is meaningful precisely when it introduces a
-- declaration, requests eager evaluation with let, or performs an assertion;
-- every other value would be computed and discarded. The same rule applies
-- to explicit begin blocks because they use the same block-part syntax and
-- scope semantics as function bodies.
validateFunctionBodyParts :: Expression -> Either InterpretingError ()
validateFunctionBodyParts expressionValue = do
  case expressionValue of
    FunctionBody parts _ -> mapM_ validatePart parts
    Begin parts _ -> mapM_ validatePart parts
    _ -> Right ()
  mapM_ validateFunctionBodyParts (expressionChildren expressionValue)
  where
    validatePart part
      | Just _ <- blockDeclaration part = Right ()
    validatePart Let {} = Right ()
    validatePart Val {} = Right ()
    validatePart part
      | containsActiveAssertion part = Right ()
    validatePart _ = Left OperationHasNoEffect

    -- Declarative syntax can leave an assertion beneath an application or
    -- another strict operator. It still runs when that body part is evaluated.
    -- A nested function body is a closure boundary: its assertions do not run
    -- merely because the enclosing operation is evaluated.
    containsActiveAssertion value = case value of
      Assert {} -> True
      FunctionBody {} -> False
      _ -> any containsActiveAssertion (expressionChildren value)

validateEvaluationSources
  :: [(String, ModuleSource)]
  -> Expression
  -> Either InterpretingError ()
validateEvaluationSources modules expressionValue = do
  validateFunctionBodyParts expressionValue
  mapM_ (validateModuleSource . snd) modules
  where
    validateModuleSource (ModuleSource _ source dependencies) = do
      validateFunctionBodyParts source
      mapM_ (validateModuleSource . snd) dependencies


defaultImportScope :: Either InterpretingError Scope
defaultImportScope = fst <$> defaultModuleEnvironment

standardLibraryEnvironment
  :: StandardLibraryVisibility
  -> Expression
  -> Either InterpretingError (Scope, [SyntaxRule])
standardLibraryEnvironment visibility raw = do
  (scope, activeRules, _) <-
    standardLibraryParsingEnvironment visibility raw
  pure (scope, activeRules)

standardLibraryParsingEnvironment
  :: StandardLibraryVisibility
  -> Expression
  -> Either InterpretingError
      (Scope, [SyntaxRule], [(String, String, [SyntaxRule])])
standardLibraryParsingEnvironment visibility raw = case visibility of
  NoStandardLibrary -> do
    scope <- rootScopeWithDatra raw []
    Right (scope, [], [])
  QualifiedStandardLibrary -> qualifiedStandardModuleBundle
  AllStandardLibrary -> defaultModuleBundle

-- Parsing and evaluation consume two views of the same imported module.
-- Build them from one module instance so syntax discovery cannot recursively
-- instantiate Std independently of the scope used to evaluate those rules.
defaultModuleEnvironment
  :: Either InterpretingError (Scope, [SyntaxRule])
defaultModuleEnvironment = do
  (scope, activeRules, _) <- defaultModuleBundle
  pure (scope, activeRules)
{-# NOINLINE defaultModuleEnvironment #-}

defaultModuleBundle
  :: Either InterpretingError
      (Scope, [SyntaxRule], [(String, String, [SyntaxRule])])
defaultModuleBundle = standardModuleEnvironment True
{-# NOINLINE defaultModuleBundle #-}

qualifiedStandardModuleBundle
  :: Either InterpretingError
      (Scope, [SyntaxRule], [(String, String, [SyntaxRule])])
qualifiedStandardModuleBundle = standardModuleEnvironment False
{-# NOINLINE qualifiedStandardModuleBundle #-}

standardModuleEnvironment
  :: Bool
  -> Either InterpretingError
      (Scope, [SyntaxRule], [(String, String, [SyntaxRule])])
standardModuleEnvironment allNames = do
  source <- defaultModuleSource
  let base = rootScope source [("\0imports", ModuleCatalog
        [(standardLibraryFileName, source)])]
  scope <- importLoadedModule base allNames source
  let imported =
        [ (namespace, value)
        | (namespace, ImportedBinding _ identity value _) <- scopeBindings scope
        , identity == standardLibraryFileName
        ]
  ruleSets <- traverse
    (\(namespace, value) -> do
      rules <- moduleSyntaxRulesFromValueIn
        standardLibraryFileName namespace value
      pure (standardLibraryFileName, namespace, rules))
    imported
  if null imported
    then Left (ModuleEvaluationFailed
      (ModuleNotLoaded standardLibraryFileName))
    else pure
      ( scope
      , [rule | allNames, (_, _, rules) <- ruleSets, rule <- rules]
      , ruleSets
      )

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
  emptyScope <- rootScopeWithDatra raw []
  let
      capture = captureSyntaxHole emptyScope []
      classify = classifySyntaxHole emptyScope []
      scopedRules = scopeSyntaxRules classify []
      rewritten = case (envelope, raw) of
        (ExplicitMapEnvelope, expressionValue) ->
          rewriteExplicitSyntax
            classify capture scopedRules (evaluateSyntaxValue emptyScope [])
            [] [] expressionValue
        (ImplicitBlockEnvelope, Begin entries _) ->
          rewriteImplicitSyntax
            classify capture scopedRules (evaluateSyntaxValue emptyScope [])
            [] [] entries
        _ -> Left MissingImplicitBlockResult
  resolveGenericFunctionTypes <$> either
    (parseFailure . ParseFailure . show)
    Right
    rewritten
  where
    parseFailure = Left . ModuleEvaluationFailed
      . StandardLibraryParseFailure standardLibraryFileName
      . parseFailureMessage
{-# NOINLINE parsedDefaultModule #-}

defaultModuleSource :: Either InterpretingError ModuleSource
defaultModuleSource =
  ModuleSource standardLibraryFileName <$> parsedDefaultModule <*> pure []
{-# NOINLINE defaultModuleSource #-}

canonicalStringCodec :: CanonicalStringCodec
canonicalStringCodec =
  CanonicalStringCodec
    { renderCanonicalString =
        renderInterpretedValue . withoutCanonicalPresentation
    , decodeCanonicalString = canonicalStringCandidates
    }

evaluateFunctionSyntax
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError (FunctionSyntax InterpretedValue)
evaluateFunctionSyntax interpret templatesExpression = do
  templates <- validatedSyntaxTemplates templatesExpression
  FunctionSyntax <$> traverse evaluateTemplate templates
  where
    evaluateTemplate (SyntaxTemplate pieces) =
      SyntaxTemplate <$> traverse evaluatePiece pieces
    evaluatePiece (SyntaxLiteral literal) = pure (SyntaxLiteral literal)
    evaluatePiece (SyntaxHole kind) = do
      specialized <- specializeSourceSyntaxHole interpret kind
      SyntaxHole <$> traverseSyntaxHoleKind interpret specialized

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
      specialized <- specializeSourceSyntaxHole interpret kind
      pure (SyntaxHole
        (mapSyntaxHoleKind renderSourceExpression
          specialized))

specializeSourceSyntaxHole
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> SyntaxHoleKind Expression
  -> Either InterpretingError (SyntaxHoleKind Expression)
specializeSourceSyntaxHole interpret kind@(ValueSyntaxHole target) = do
  evaluated <- interpret target
  let specialized = specializeSyntaxHoleKind evaluated kind
  pure $ case specialized of
    ValueSyntaxHole {}
      | any syntaxCategoryExpression
          (concatMap expressionTree (expressionChildren target)) ->
          ExpressionSyntaxHole target
    _ -> specialized
  where
    expressionTree expressionValue =
      expressionValue
        : concatMap expressionTree (expressionChildren expressionValue)
    syntaxCategoryExpression expressionValue = case interpret expressionValue of
      Right value -> case specializeSyntaxHoleKind value
          (ValueSyntaxHole expressionValue) of
        ValueSyntaxHole {} -> False
        _ -> True
      Left _ -> False
specializeSourceSyntaxHole _ kind = pure kind

traverseSyntaxHoleKind
  :: Applicative f
  => (source -> f target)
  -> SyntaxHoleKind source
  -> f (SyntaxHoleKind target)
traverseSyntaxHoleKind transform kind = case kind of
  ExpressionSyntaxHole value -> ExpressionSyntaxHole <$> transform value
  BlockSyntaxHole value -> BlockSyntaxHole <$> transform value
  FunctionBodySyntaxHole value -> FunctionBodySyntaxHole <$> transform value
  IdentifierExpressionSyntaxHole value ->
    IdentifierExpressionSyntaxHole <$> transform value
  ValueSyntaxHole value -> ValueSyntaxHole <$> transform value

validatedSyntaxTemplates
  :: Expression
  -> Either InterpretingError [SyntaxTemplate Expression]
validatedSyntaxTemplates templatesExpression =
  case compileSyntaxTemplatesFromExpression templatesExpression of
    Left ExpectedSyntaxTemplateOperand ->
      Left InvalidSyntaxTemplateOperand
    Left (InadmissibleSyntaxTemplate template failure) ->
      Left (InvalidSyntaxTemplate template failure)
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

type ScopeBindings = [(String, Binding)]

data ScopeHandoff = ScopeHandoff
  { scopeHandoffReceiver :: ScopeActivation
  , scopeHandoffPolicyDecision
      :: ScopeProtectionPolicy -> ScopeHandoffDecision
  }

-- | The interpreter has one scope abstraction.  Its binding environment and
-- dynamic protection authority are activated and captured together; handoff
-- is the generic exit path for values which leave this activation.
data Scope = Scope
  { scopeBindings :: ScopeBindings
  , scopeActivation :: ScopeActivation
  , scopeHandoff :: Maybe ScopeHandoff
  }

data Binding
  = DeferredBinding Scope (Maybe Expression) Expression
  | EvaluatedBinding InterpretedValue
  | ContextualBinding String Bool
      (ReductionContext -> Either InterpretingError InterpretedValue)
  | ShadowingConsistentBinding Binding
  | NamedBinding PresentationDependency Binding
  | QualifiedBinding String Binding
  | RetainedBinding Scope (Maybe Expression) Expression InterpretedValue
  | ImportedBinding
      PresentationDependency FilePath InterpretedValue Scope
  | ModuleCatalog [(String, ModuleSource)]
  | ScopeMembers [ScopeMember]
  | CanonicalNames [(String, String)]
  | LexicalScope PresentationDependency

rootScope :: salt -> ScopeBindings -> Scope
rootScope salt bindings = Scope
  { scopeBindings = bindings
  , scopeActivation = initialScopeActivation salt
  , scopeHandoff = Nothing
  }

rootScopeWithDatra
  :: salt
  -> ScopeBindings
  -> Either InterpretingError Scope
rootScopeWithDatra salt bindings = do
  host <- datraHostValue
  pure (rootScope salt
    ( (datraHostIdentifier, EvaluatedBinding
        (withCanonicalReference [] datraHostIdentifier host))
    : bindings
    ))

scopeWithBindings :: ScopeBindings -> Scope -> Scope
scopeWithBindings bindings scope = scope { scopeBindings = bindings }

extendScope :: ScopeBindings -> Scope -> Scope
extendScope bindings scope =
  scopeWithBindings (bindings <> scopeBindings scope) scope

enterScope
  :: salt
  -> ScopeBindings
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope
enterScope salt bindings decide parent = Scope
  { scopeBindings = bindings <> scopeBindings parent
  , scopeActivation = enterScopeActivation salt (scopeActivation parent)
  , scopeHandoff = Just (ScopeHandoff (scopeActivation parent) decide)
  }

enterScopeWithReceiver
  :: salt
  -> ScopeBindings
  -> ScopeActivation
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope
enterScopeWithReceiver salt bindings receiver decide parent =
  (enterScope salt bindings decide parent)
    { scopeHandoff = Just (ScopeHandoff receiver decide) }

handoffScopeValue :: Scope -> InterpretedValue -> InterpretedValue
handoffScopeValue scope value =
  case scopeHandoff scope of
    Nothing -> value
    Just handoff -> handoffProtectedValue
      (scopeActivation scope)
      (scopeHandoffReceiver handoff)
      (scopeHandoffPolicyDecision handoff)
      value

lookupScope :: String -> Scope -> Maybe Binding
lookupScope name = lookup name . scopeBindings

scopeProtectedValues :: Scope -> [InterpretedValue]
scopeProtectedValues scope =
  [ value
  | (_, binding) <- scopeBindings scope
  , Just value <- [bindingValue binding]
  , valueIsScopeProtected value
  ]
  where
    bindingValue binding =
      case binding of
        EvaluatedBinding value -> Just value
        RetainedBinding _ _ _ value -> Just value
        ImportedBinding _ _ value _ -> Just value
        ShadowingConsistentBinding target -> bindingValue target
        NamedBinding _ target -> bindingValue target
        QualifiedBinding _ target -> bindingValue target
        _ -> Nothing

data ImportPresentation
  = TransparentImportPresentation
  | CanonicalValueImportPresentation

data ModuleExport = ModuleExport String ImportPresentation Binding

data LoadedModuleBinder = LoadedModuleBinder
  { loadedModuleBinderName :: String
  , loadedModuleBinderPresentation :: ImportPresentation
  , loadedModuleBinderValue :: InterpretedValue
  , loadedModuleBinderScope :: Scope
  }

data LoadedModuleResult = LoadedModuleResult
  { loadedModuleIdentity :: FilePath
  , loadedModuleFederation :: InterpretedValue
  , loadedModuleBinders :: [LoadedModuleBinder]
  }

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
  -> ScopeBindings
contextualBindings surface includesDependencies value =
  [scopeBinding ("_" <> surface)
    (ContextualBinding surface includesDependencies value)]

constantContextualBindings :: String -> InterpretedValue -> ScopeBindings
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
contextualLevels includesPrivate resolving surface scope =
  go (scopeBindings scope) (scopeBindings scope)
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
        ScopeMembers members ->
          Just (False, \reduction -> declarationMap members
            (resolveIdentifierAccess
              includesPrivate reduction
              (scopeWithBindings environment scope) resolving))
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
    Nothing
    signatureSource
    (Just (prepare schema))
    (Just invoke)
    False))
  where
    maximumDepth = fromIntegral (length levels - 1)
    domainExpression = ValuedNaturalRange 0 maximumDepth
    signatureSource = renderSourceExpression
      (FunctionType domainExpression
        (ScopeAccess
          (IdentifierReference (IdentifierString "'datra"))
          (IdentifierReference (IdentifierString "Any"))))
    innerMap = ContextualMap ("_inner_" <> surface) levels

    -- The surface spelling has no holes and therefore supplies the empty map.
    -- Contextual depth zero is the function's ordinary default; explicit
    -- @_this n@ and @_it n@ calls overload that default with @n@.
    prepare schema supplied = do
      (depth, bindings) <- overloadArgumentSchemaComplete schema supplied
      pure (PreparedFunctionArgument supplied depth bindings)

    invoke _ reduction prepared = do
      depth <- requireFiniteInteger LeftOperand
        (functionPreparedArgument prepared)
      value <- accessContextualMap reduction depth innerMap
      pure (EvaluatedFunctionInvocation value Nothing)

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

scopeMembersBinding :: Binding -> Maybe [ScopeMember]
scopeMembersBinding binding =
  case binding of
    ScopeMembers names -> Just names
    ShadowingConsistentBinding target -> scopeMembersBinding target
    NamedBinding _ target -> scopeMembersBinding target
    QualifiedBinding _ target -> scopeMembersBinding target
    _ -> Nothing

contextualThisAvailable :: Scope -> Bool
contextualThisAvailable scope = case lookupScope "_this" scope of
  Just binding -> case
      (contextualBinding binding, scopeMembersBinding binding) of
    (Nothing, Nothing) -> False
    _ -> True
  Nothing -> False

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
    binding <- lookupScope name scope
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
evalInScopeWith reduction scope resolving =
  interpretNormalizedExpressionWith reduction scope resolving
    . normalizeExpression

-- A source resource is an implicit block even though it shares the 'Begin'
-- AST node with explicit nested blocks. The resource boundary supplies the
-- evaluation context: its declarations are scoped, but no fresh @this@ is
-- installed. Nested 'Begin' nodes continue through ordinary expression
-- evaluation and therefore do install @this@.
evalResourceInScopeWith
  :: ReductionContext
  -> Scope
  -> [String]
  -> Interpreter
evalResourceInScopeWith reduction scope resolving expressionValue =
  case normalizeExpression expressionValue of
    Begin bindings result ->
      evaluateBlockInScope False Nothing reduction scope resolving
        bindings result
    normalized ->
      interpretNormalizedExpressionWith reduction scope resolving normalized

evalInContinuationScopeWith
  :: salt
  -> ReductionContext
  -> ScopeBindings
  -> Scope
  -> [String]
  -> Interpreter
evalInContinuationScopeWith salt reduction bindings parent resolving expressionValue = do
  let child = enterScope salt bindings genericContinuationHandoff parent
  value <- evalInScopeWith reduction child resolving expressionValue
  pure (handoffScopeValue child value)

evalResourceInContinuationScopeWith
  :: salt
  -> ReductionContext
  -> ScopeBindings
  -> Scope
  -> [String]
  -> Interpreter
evalResourceInContinuationScopeWith
    salt reduction bindings parent resolving expressionValue = do
  let child = enterScope salt bindings genericContinuationHandoff parent
  value <- evalResourceInScopeWith reduction child resolving expressionValue
  pure (handoffScopeValue child value)

evaluateBlockInScope
  :: Bool
  -> Maybe String
  -> ReductionContext
  -> Scope
  -> [String]
  -> [Expression]
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateBlockInScope introducesThis source reduction scope resolving
    bindings result = do
  let origins = canonicalDependencyNames bindings result
      reconstructionScope = if null origins then scope
        else extendScope [("\0canonical", CanonicalNames origins)] scope
  imported <- (if introducesThis
      then importScope
      else importScopeWithoutContextualThis)
    reconstructionScope resolving bindings
  value <- evalInScopeWith reduction imported resolving result
  let handed = handoffScopeValue imported value
  pure (withEvaluationSource source
    (withoutCanonicalDependencies
      (maybe [] pure (scopePresentationDependency imported)) handed))

interpretNormalizedExpressionWith
  :: ReductionContext
  -> Scope
  -> [String]
  -> Interpreter
interpretNormalizedExpressionWith reduction scope resolving expressionValue =
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
      checkedBinary boundedRangeValue lower upper
    SuperEllipsisRangePlus lower ->
      checkedUnary openPlusRangeValue lower
    SuperEllipsisRangeMinus upper ->
      checkedUnary openMinusRangeValue upper
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
    MaybeThen optional branch -> do
      optionalResult <- interpret optional >>= unconsList
      runProtectedOperation protection [optionalResult] $ \actuals ->
        case actuals of
          [actualOptional] ->
            case interpretedSemanticResult actualOptional of
              CanonicalAssignment "Just" _ _ -> do
                result <- evalInContinuationScopeWith branch reduction
                  (constantContextualBindings "it" actualOptional)
                  scope resolving branch
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
      checkedBinary addValues left right
    Subtraction left right ->
      checkedBinary subtractValues left right
    Plus operand -> checkedUnary plusValue operand
    Minus operand -> checkedUnary minusValue operand
    Multiplication left right ->
      checkedBinary multiplyValues left right
    Exponentiation base exponentValue ->
      checkedBinary exponentiateValues base exponentValue
    Subfederation source target ->
      checkedBinary subfederationValues source target
    Equality left right ->
      checkedBinary equalValues left right
    Inequality left right ->
      checkedBinary
        (\actualLeft actualRight ->
          equalValues actualLeft actualRight >>= booleanNotValue)
        left right
    LessThan left right ->
      binaryComparison (== LT) left right
    LessThanOrEqual left right ->
      binaryComparison (/= GT) left right
    GreaterThan left right ->
      binaryComparison (== GT) left right
    GreaterThanOrEqual left right ->
      binaryComparison (/= LT) left right
    BooleanAnd left right ->
      checkedBinary booleanAndValues left right
    BooleanOr left right ->
      checkedBinary booleanOrValues left right
    BooleanNot operand -> checkedUnary booleanNotValue operand
    Coalization operand -> unary (Right . coalizeValue) operand
    Val _ -> Left ValOutsideBegin
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
        recursive activeReduction = evalInContinuationScopeWith
          operand activeReduction
          (contextualBindings "this"
            (case operand of Begin {} -> True; _ -> False)
            recursive)
          scope resolving operand
    GenericIntroductionExpression introduction ->
      Left (GenericIntroductionOutsideFunctionType
        (case genericIntroductionPolarity introduction of
          GenericProduct -> "&"
          GenericSum -> "^"))
    GenericReferenceExpression {} ->
      Left (FunctionEvaluationFailed ExpectedFunctionType)
    InModule path body -> do
      imported <- lookupModuleDefinitionScope scope path
      evalInContinuationScopeWith body reduction
        (scopeBindings imported) scope resolving body
    Import paths body -> evaluateImport
      reduction scope resolving expressionValue paths body
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
    FunctionTypeExpression [] domain codomain ->
      evaluateFunctionType [] expressionValue domain codomain
    FunctionTypeExpression generics domain codomain -> do
      validateGenericFunctionType interpret generics domain codomain
      let preparedDomain = prepareFunctionDomainExpression generics domain
          preparedCodomain = prepareGenericExpression generics codomain
      evaluateFunctionType generics expressionValue
        preparedDomain preparedCodomain
    FunctionBody bindings result -> do
      implementation <- createFunctionWithEvaluatedTypes
        (Just (anyTypeValue, anyTypeValue))
        reduction scope resolving expressionValue
        (AtlasMap []) (AtlasMap []) bindings result []
      case interpretedFunction implementation of
        Just function -> pure (makeFunctionBodyValue
          (EvaluatedRuntimeFunctionBody
            (renderSourceExpression expressionValue)
            function))
        Nothing -> Left (FunctionEvaluationFailed ExpectedFunctionType)
    FunctionApplication
        (SyntaxType templates signature)
        body@FunctionBody {} -> do
      syntax <- evaluateFunctionSyntax interpret templates
      sourceSyntax <- sourceFunctionSyntax interpret templates
      value <- interpret (FunctionApplication signature body)
      case interpretedFunction value of
        Just function -> pure (makeFunctionValue function
          { functionSyntax = Just syntax
          , functionSyntaxSource = Just sourceSyntax
          })
        Nothing -> Left (FunctionEvaluationFailed
          AstPatternRequiresFunctionImplementation)
    FunctionApplication
        signature@(FunctionTypeExpression [] domain codomain)
        (FunctionBody bindings result) ->
      createFunction reduction scope resolving signature
        domain codomain bindings result
    FunctionApplication
        signature@(FunctionTypeExpression generics domain codomain)
        (FunctionBody bindings result) -> do
      validateGenericFunctionType interpret generics domain codomain
      let preparedDomain = prepareFunctionDomainExpression generics domain
          preparedCodomain = prepareGenericExpression generics codomain
      createFunctionWithGenerics reduction scope resolving
        signature preparedDomain preparedCodomain bindings result
        generics
    FunctionApplication function argument -> do
      let applyEvaluated callable supplied =
            runProtectedOperationWithContract
              protection
              genericOperationResultDecision
              contextuallySpecify
              [callable, supplied] $ \actuals ->
              case actuals of
                [actualCallable, actualSupplied]
                  | Just signature <- interpretedFunction actualCallable
                  , Nothing <- functionSource signature
                  , Just body <- interpretedFunctionBody actualSupplied ->
                      (, Nothing) <$> attachFunctionBody actualCallable body
                  | Nothing <- interpretedFunction actualCallable
                  , not (interpretedTypeIsTotal actualCallable)
                  , Just _ <- interpretedFunctionBody actualSupplied ->
                      (, Nothing) <$> interpret
                        (resolveGenericFunctionTypes
                          (inferredFunction argument function))
                  | otherwise -> do
                      input <- functionArgumentValue actualSupplied
                      applyFunction
                        (scopeActivation scope) reduction actualCallable input
                _ -> Right (neverValue, Nothing)
      case interpret function of
        Left failure@(GenericIntroductionOutsideFunctionType _) -> do
          supplied <- interpret argument
          case interpretedFunctionBody supplied of
            Just _ -> interpret (resolveGenericFunctionTypes
              (inferredFunction argument function))
            Nothing -> Left failure
        Left failure -> Left failure
        Right callable -> do
          supplied <- interpret argument
          applyEvaluated callable supplied
    Begin bindings result ->
      evaluateBlockInScope True
        (Just (renderSourceExpression expressionValue))
        reduction scope resolving bindings result
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
    MapConcatenation left right
      | AtlasMap [] <- right ->
          case left of
            -- The postfix comma in @A, B,@ delegates its diagnostic decision
            -- to the enclosed binary concatenation.
            MapConcatenation _ _ -> binary concatenateValues left right
            _ -> checkedConcatenation
              RedundantConcatenation
              (\actualLeft _ -> actualLeft)
              left
              right
      | otherwise -> checkedConcatenation
          RedundantConcatenation
          (\actualLeft actualRight ->
            buildAtlasMapFromValues
              makeAtlasMap
              [left, right]
              [actualLeft, actualRight])
          left
          right
    Overload defaults supplied ->
      binary overloadValues defaults supplied
    SafeOverload defaults supplied ->
      binary safeOverloadValues defaults supplied
    -- Project one declared binding without forcing the whole scope map. This
    -- also permits projections next to recursive function declarations.
    ScopeAccess
        thisValue
        (IdentifierReference (IdentifierString name))
      | isContextualAccessOf (IdentifierString "_this") thisValue
      , contextualThisAvailable scope
          -> resolveIdentifierWith reduction scope resolving name
    ScopeAccess operand body
      | Just moduleOperands <- withModuleScopeOperands operand -> do
          let distinctOperands = nub moduleOperands
          sources <- traverse interpret distinctOperands
          runProtectedOperation protection sources $ \actuals -> do
            publicDomains <- traverse publicDomainValue actuals
            _ <- importDomainValue publicDomains
            members <- concat <$> traverse scopeNamedMembers actuals
            let combined = makeAtlasMapPreservingSingleton 2
                  (map snd (public members))
            enterOpenedScope expressionValue combined
              (zip distinctOperands actuals) body
    ScopeAccess operand body -> do
      source <- interpret operand
      runProtectedOperation protection [source] $ \actuals ->
        case actuals of
          [actual] -> case body of
            IdentifierReference (IdentifierString name)
              | isPrivateIdentifier name -> Left (UnknownIdentifier name)
              | otherwise -> do
                  selected <- namedAccessValue actual name
                  validateOpenedBinding actual (name, selected)
                  payload <- accessValues selected (naturalValue 1)
                  let imported = case operand of
                        IdentifierReference (IdentifierString namespace) ->
                          case lookupScope namespace scope of
                            Just (ImportedBinding _ identity _ internal) ->
                              Just (identity, internal)
                            _ -> Nothing
                        _ -> Nothing
                      exportedPayload = case imported of
                        Just (_, internal) -> withoutCanonicalDependencies
                          [ dependency
                          | (_, LexicalScope dependency) <- scopeBindings internal
                          ]
                          payload
                        Nothing -> payload
                  if hasTrailingIdentifierMarker canonicalValueMarker selected
                    then do
                      let dependencies = case imported of
                            Just (identity, _) ->
                              [canonicalValuePresentationDependency identity]
                            Nothing -> maybe [] fst
                              (interpretedCanonicalPresentation actual)
                      pure (withCanonicalNamedAccess
                        dependencies
                        (interpretedCanonicalResult actual)
                        name
                        exportedPayload)
                    else case imported of
                      Just _ -> transparentEitherAlias exportedPayload
                      Nothing -> pure exportedPayload
            _ -> enterOpenedScope expressionValue actual
              [(operand, actual)] body
          _ -> Right neverValue
    MapAccess
        thisValue
        insertionOperand
      | isContextualAccessOf (IdentifierString "_this") thisValue
      , contextualThisAvailable scope -> do
          insertion <- interpret insertionOperand
          case lookupScope "_this" scope >>= contextualBinding of
            Just (_, value) -> do
              contextual <- value reduction
              runProtectedOperation
                protection [contextual, insertion] $ \actuals ->
                  case actuals of
                    [actualContextual, actualInsertion] ->
                      accessValues actualContextual actualInsertion
                    _ -> Right neverValue
            _ -> projectDeclaration
              (scopeDeclarationMembers scope)
              (resolveIdentifierWith reduction scope resolving)
              insertion
    MapAccess mapOperand insertionOperand ->
      case lazyRecursivePrefix scope mapOperand of
        Just (captured, prefix) -> do
          insertion <- interpret insertionOperand
          accessRepeatedPrefix captured resolving prefix insertion
        Nothing -> binary accessValues mapOperand insertionOperand
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
      let identifierExpression = StringTemplate parts
          familyKey = renderSourceExpression identifierExpression
          nameFamily supplied =
            interpretStringTemplateWith protection
              (evalInContinuationScopeWith identifierExpression reduction
                (constantContextualBindings "it" supplied)
                scope resolving)
              parts
      identifier <- nameFamily typeAnnotation
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
    protection = scopeActivation scope
    interpret = evalInScopeWith reduction scope resolving
    transparentEitherAlias value =
      case stripOuterIdentifierType value of
        Right underlying
          | interpretedValueKind underlying == EitherValueKind -> Right underlying
        _ -> Right value
    interpretIdentifierOperation
        identifierString typeAnnotationExpression
        (Just givenValueExpression)
      | typeAnnotationExpression == givenValueExpression = do
          givenValue <- interpret givenValueExpression
          if interpretedValueHasTotalMap givenValue
            then assignIdentifierValues identifierString givenValue givenValue
            else pure
              (inferredIdentifierAssignmentValue identifierString givenValue)
    interpretIdentifierOperation
        identifierString typeAnnotationExpression maybeGivenValueExpression = do
      typeAnnotation <- interpret typeAnnotationExpression
      case maybeGivenValueExpression of
        Nothing ->
          runProtectedOperation protection [typeAnnotation] $ \actuals ->
            case actuals of
              [actualAnnotation] -> do
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
                  case assignIdentifierValues
                      identifierString actualAnnotation actualGiven of
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
    checkedConcatenation rejection comparison left right = do
      leftValue <- interpret left
      rightValue <- interpret right
      runProtectedOperation protection [leftValue, rightValue] $ \actuals ->
        case actuals of
          [actualLeft, actualRight] -> do
            (result, equivalenceView) <-
              concatenateValuesWithEquivalenceView actualLeft actualRight
            equivalent <-
              equalValues
                equivalenceView
                (comparison actualLeft actualRight)
                >>= booleanCondition
            if equivalent then Left rejection else Right result
          _ -> Right neverValue
    checkedUnary operation operand = do
      value <- interpret operand
      runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [value] $ \actuals ->
          case actuals of
            [actual] -> checkedResult (operation actual)
            _ -> Right (neverValue, Nothing)
    checkedBinary operation left right = do
      leftValue <- interpret left
      rightValue <- interpret right
      runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [leftValue, rightValue] $ \actuals ->
          case actuals of
            [actualLeft, actualRight] ->
              checkedResult (operation actualLeft actualRight)
            _ -> Right (neverValue, Nothing)
    checkedResult operation = do
      result <- operation
      pure (result, Just result)
    validateOpenedBinding _ (name, selected) =
      case lookupScope name scope of
        Just existing | not (bindingHasUnrestrictedShadowing existing) -> do
          let bounded = ShadowingConsistencyReduction
                name shadowingConsistencyFuel
          original <- resolveIdentifierWith bounded scope resolving name
          replacement <- accessValues selected (naturalValue 1)
          if interpretedSemanticResult original
              == interpretedSemanticResult replacement
            then Right ()
            else Left (InconsistentShadowing name)
        _ -> Right ()
    enterOpenedScope salt actual contributions selectedBody = do
      validateShortScopeMember actual selectedBody
      members <- scopeNamedMembers actual
      let opened = public members
      bindings <- concat <$>
        traverse (openedScopeContributionBindings scope) contributions
      validateShortScopeAccess actual opened selectedBody
      mapM_ (validateOpenedBinding actual) opened
      evalResourceInContinuationScopeWith salt reduction
        bindings scope resolving selectedBody
    validateShortScopeAccess actual opened selectedBody =
      case selectedBody of
        IdentifierReference (IdentifierString name)
          | name `elem` map fst opened -> Right ()
          | otherwise -> case namedAccessValue actual name of
              Left failure -> Left failure
              Right _ -> Left (UnknownIdentifier name)
        _ -> Right ()
    validateShortScopeMember actual selectedBody =
      case selectedBody of
        IdentifierReference (IdentifierString name) ->
          () <$ namedAccessValue actual name
        _ -> Right ()
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
      runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [leftValue, rightValue] $ \actuals ->
          case actuals of
            [actualLeft, actualRight] -> checkedResult $ do
              ordering <- compareIntegerLimitValues actualLeft actualRight
              pure (booleanValue (predicate ordering))
            _ -> Right (neverValue, Nothing)
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
      runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [constructor, value] $ \actuals ->
          case actuals of
            [actualConstructor, actualValue] -> do
              input <- functionArgumentValue actualValue
              applyFunction
                (scopeActivation scope) reduction actualConstructor input
            _ -> Right (neverValue, Nothing)
    interpretContainer ordinary _ _ = ordinary
    evaluateFunctionType generics written preparedDomain preparedCodomain = do
      let (staticDomain, substitutions) =
            staticGenericDomain generics preparedDomain
          staticCodomain = substituteDependent substitutions preparedCodomain
      schema <- compileParametersWithGenerics generics interpret
        preparedDomain staticDomain
      input <- parameterDomain schema
      output <- interpret staticCodomain
      let signatureText = renderSourceExpression written
          prepare argument = do
            (prepared, bindings) <- overloadArgumentSchemaComplete schema argument
            pure (PreparedFunctionArgument argument prepared bindings)
      runProtectedOperation protection [input, output] $ \actuals ->
        case actuals of
          [actualInput, actualOutput] -> pure (makeFunctionValue
            (EvaluatedFunction actualInput actualOutput Nothing Nothing Nothing Nothing
              signatureText (Just prepare) Nothing True))
          _ -> Right neverValue

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
    Nothing -> case lookupScope name scope of
      Just binding -> resolve binding
      Nothing -> Left (UnknownIdentifier name)
  where
    canonicalAlias = unique exactAliases `orElse` unique qualifiedAliases
    aliases = concat
      [names | (_, CanonicalNames names) <- scopeBindings scope]
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
      let activeCaptured = captured
            { scopeActivation = scopeActivation scope
            , scopeHandoff = Nothing
            }
      in withCanonicalReference
        (scopePresentationDependencies captured) name <$>
        evaluateBindingDefinitionWith reduction
          activeCaptured resolving name annotation expressionValue

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
        Just implementation -> do
          seed <- evalInScopeWith reduction captured resolving implementation
          pure (case interpretedFunctionBody seed of
            Just (EvaluatedRuntimeFunctionBody _ function) ->
              makeFunctionValue function
            _ -> seed)
        Nothing -> Left (CyclicIdentifierReference
          (reverse
            (name : map resolutionName
              (takeWhile (/= resolutionKey) resolving))
            <> [name]))
  | otherwise = do
      case annotation of
        Nothing -> pure ()
        Just typeExpression ->
          () <$ evalInScopeWith reduction captured
            (resolutionKey : resolving) typeExpression
      resolveInferredEitherAlias annotation
        <$> evaluateDefinition
  where
    resolutionKey = bindingKey name expressionValue
    resolutionName = takeWhile (/= ':')
    evaluateDefinition =
      case expressionValue of
        contextual
          | isContextualAccessOf (IdentifierString "_this") contextual
          , Just _ <- lookupScope "_this" captured >>= scopeMembersBinding ->
              declarationMap
                (visibleScopeMembers "_this" captured)
                (resolveIdentifierWith reduction captured
                  (resolutionKey : resolving))
        IdentifierReference (IdentifierString reference)
          | Just _ <- lookupScope reference captured >>= scopeMembersBinding ->
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
visibleScopeMembers :: String -> Scope -> [ScopeMember]
visibleScopeMembers reference scope =
  case break isReferencedScope (scopeBindings scope) of
    (visible, (_, binding) : _)
      | Just members <- scopeMembersBinding binding ->
      let visibleNames = map fst visible
      in [member | member <- members
           , scopeMemberName member `elem` visibleNames]
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
    SyntaxType _ (FunctionApplication _ implementation) ->
      Just implementation
    FunctionApplication (SyntaxType {}) implementation ->
      Just implementation
    FunctionApplication (FunctionTypeExpression {}) implementation
      | not (sourceFunctionBody implementation) ->
      Just implementation
    MapSpecification implementation SyntaxType {} -> Just implementation
    MapSpecification implementation FunctionTypeExpression {}
      | not (sourceFunctionBody implementation) ->
      Just implementation
    Begin _ result -> recursiveFunctionImplementation result
    Let value -> recursiveFunctionImplementation value
    Val value -> recursiveFunctionImplementation value
    EitherType left right ->
      case recursiveFunctionImplementation left of
        Just implementation -> Just implementation
        Nothing -> recursiveFunctionImplementation right
    OptionalType operand -> recursiveFunctionImplementation operand
    _ -> Nothing
  where
    sourceFunctionBody FunctionBody {} = True
    sourceFunctionBody _ = False

-- A block imports declarations from left to right. Ordinary definitions capture
-- only earlier ordinary definitions, while every let definition is predeclared
-- throughout the block. Lets are forced before yield and their results replace
-- the deferred definitions. Names are checked before evaluating any binding.
importScope :: Scope -> [String] -> [Expression] -> Either InterpretingError Scope
importScope = importScopeUsing scopeBuilder

importScopeWithoutContextualThis
  :: Scope -> [String] -> [Expression] -> Either InterpretingError Scope
importScopeWithoutContextualThis =
  importScopeUsing scopeBuilderWithoutContextualThis

importScopeWithin
  :: Scope -> [String] -> [Expression] -> Either InterpretingError Scope
importScopeWithin = importScopeUsing scopeBuilderWithin

importScopeUsing
  :: (Scope -> [Expression] -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      ))
  -> Scope
  -> [String]
  -> [Expression]
  -> Either InterpretingError Scope
importScopeUsing build enclosing resolving entries = do
  (rebuild, eagerNames, eagerEntries, validateConsistency) <-
    build enclosing entries
  let deferred = rebuild []
      forced =
        [ name
        | name <- eagerNames
        , maybe True (not . productiveRecursiveBinding name)
            (lookupScope name deferred)
        ]
      (seeded, ordinary) = partition
        (maybe False bindingHasRecursiveFunctionSeed . (`lookupScope` deferred))
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
  case
      [ dependency
      | (_, LexicalScope dependency) <- scopeBindings scope
      ] of
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
scopeBuilder = scopeBuilderWithContextualThis True

scopeBuilderWithoutContextualThis
  :: Scope
  -> [Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      )
scopeBuilderWithoutContextualThis = scopeBuilderWithContextualThis False

scopeBuilderWithContextualThis
  :: Bool
  -> Scope
  -> [Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      )
scopeBuilderWithContextualThis introducesThis enclosing entries = do
  let dependency = childPresentationDependency enclosing entries
      scopedEnclosing = enterScope entries
        [("\0scope", LexicalScope dependency)]
        genericContinuationHandoff
        enclosing
  scopeBuilderActivated introducesThis scopedEnclosing entries

scopeBuilderWithin
  :: Scope
  -> [Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      )
scopeBuilderWithin enclosing entries =
  let dependency = childPresentationDependency enclosing entries
      scopedEnclosing = extendScope
        [("\0scope", LexicalScope dependency)] enclosing
  in scopeBuilderActivated True scopedEnclosing entries

scopeBuilderActivated
  :: Bool
  -> Scope
  -> [Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [String]
      , [Expression]
      , [String] -> Scope -> Either InterpretingError ()
      )
scopeBuilderActivated introducesThis scopedEnclosing entries = do
  let (definitions, eagerEntries) = foldMap (bindingImports False) entries
      members = map declarationScopeMember definitions
      eagerNames =
        [ declarationName declaration
        | declaration <- definitions
        , declarationIsLet declaration
        ]
      blockBase
        | not introducesThis = scopedEnclosing
        | otherwise =
            case lookupScope "_this" scopedEnclosing >>= contextualBinding of
              Just _ -> scopedEnclosing
              Nothing -> extendScope
                [scopeBinding "_this" (ScopeMembers members)] scopedEnclosing
  (blockOuter, scopeEntries) <- scopeEntriesFrom blockBase entries
  let
      rebuild retained = scopeWithBindings
        (buildScopedBindings (makeBinding retained)
          (scopeBindings blockBase) scopeEntries)
        blockOuter
      consistencyNames =
        [ name
        | declaration <- definitions
        , let name = declarationName declaration
        , Just binding <- [lookupScope name blockOuter]
        , not (bindingHasUnrestrictedShadowing binding)
        ]
      validateConsistency resolving imported =
        mapM_ (validateConsistencyName resolving imported) consistencyNames
      validateConsistencyName resolving imported name =
        case lookupScope name blockOuter of
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
      makeBinding retained capturedBindings declaration =
        let name = declarationName declaration
            annotation = declarationAnnotation declaration
            expressionValue = declarationValue declaration
            captured = scopeWithBindings capturedBindings blockOuter
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
    , eagerNames
    , eagerEntries
    , validateConsistency
    )
  where
    checkName blockOuter declared declaration
      | declarationIsLet declaration
      , Just binding <- lookupScope name blockOuter
      , not (bindingHasUnrestrictedShadowing binding) =
          Left (LetBindingCannotShadowConsistentIdentifier name)
      | name `elem` declared = Left (IdentifierStringOverlap name)
      | otherwise = Right (name : declared)
      where name = declarationName declaration

data ScopeEntry
  = ScopeDeclaration Declaration

scopeEntriesFrom
  :: Scope
  -> [Expression]
  -> Either InterpretingError (Scope, [ScopeEntry])
scopeEntriesFrom initial = go []
  where
    go reversed [] = Right (initial, reverse reversed)
    go reversed (entry : remaining) = case blockDeclaration entry of
      Just declaration ->
        go (ScopeDeclaration declaration : reversed) remaining
      Nothing -> go reversed remaining

buildScopedBindings
  :: (ScopeBindings -> Declaration -> (String, Binding))
  -> ScopeBindings
  -> [ScopeEntry]
  -> ScopeBindings
buildScopedBindings makeBinding enclosing entries = foldl add initial entries
  where
    initial = recursiveLets <> enclosing
    recursiveLets =
      [ makeBinding (scopeBefore position) declaration
      | (position, ScopeDeclaration declaration) <- zip [0 :: Int ..] entries
      , declarationIsLet declaration
      ]
    scopeBefore position = foldl add initial (take position entries)
    add bindings (ScopeDeclaration declaration)
      | declarationIsLet declaration = bindings
      | otherwise = makeBinding bindings declaration : bindings

importInvocation :: Expression -> Maybe [String]
importInvocation expressionValue =
  case expressionValue of
    Import paths _ -> Just paths
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
      Val _ -> ([], [expressionValue])
      Assert {} -> ([], [expressionValue])
      _ -> ([], [expressionValue | strict])

interpretStringTemplateWith
  :: ScopeActivation
  -> Interpreter
  -> [StringTemplatePart Expression]
  -> Either InterpretingError InterpretedValue
interpretStringTemplateWith protection interpret parts = do
  values <- traverse interpretPart parts
  case values of
    [] -> asciiStringValue ""
    firstValue : remaining -> do
      result <- foldM concatenateTemplateValues firstValue remaining
      runProtectedOperation protection [result] $ \actuals ->
        case actuals of
          [actual] -> Right (templateValue actual)
          _ -> Right neverValue
  where
    interpretPart (StringTemplateLiteral value) = asciiStringValue value
    interpretPart (StringTemplateInterpolation expressionValue) = do
      value <- interpret expressionValue
      runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [value] $ \actuals ->
          case actuals of
            [actual] -> checkedString
              (toStringValue canonicalStringCodec actual)
            _ -> Right (neverValue, Nothing)

    concatenateTemplateValues left right =
      case runProtectedOperationWithContract
          protection
          genericOperationResultDecision
          contextuallySpecify
          [left, right] $ \actuals ->
          case actuals of
            [actualLeft, actualRight] -> checkedString
              (concatenateValues actualLeft actualRight)
            _ -> Right (neverValue, Nothing) of
        Right value -> Right value
        Left _ -> Left AmbiguousStringTemplate

    checkedString operation = do
      result <- operation
      pure (result, Just result)

interpretSpecificationWith
  :: ScopeActivation
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
            specifyValues actualSource actualTarget
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

-- Generic bounds form one ordered telescope. Static function signatures use
-- each binder's upper bound, while invocation repeats the checks with the
-- actual witnesses.
staticGenericDomain
  :: [GenericBinder Expression]
  -> Expression
  -> (Expression, [(String, Expression)])
staticGenericDomain generics expressionValue =
  (substituteDependent substitutions expressionValue, substitutions)
  where
    substitutions = go [] generics
    go prepared [] = reverse prepared
    go prepared (binder : remaining) =
      let GenericIdentifier (IdentifierString name) _ =
            genericBinderIdentifier binder
          bound = prepareGenericExpression generics
            (genericBinderBound binder)
          staticBound = substituteDependent prepared bound
      in go ((name, staticBound) : prepared) remaining

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

-- | Validate the generic telescope from left to right, then validate ordinary
-- named parameters in the resulting scope. Polarity affects protection, not
-- telescope name resolution.
validateGenericArgumentsExcept
  :: [String]
  -> Scope
  -> [String]
  -> [GenericBinder Expression]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError ScopeBindings
validateGenericArgumentsExcept
    trusted captured resolving generics domain supplied =
  validateGenerics [] generics
  where
    genericNames =
      [ name
      | binder <- generics
      , let GenericIdentifier (IdentifierString name) _ =
              genericBinderIdentifier binder
      ]
    validateGenerics genericScope [] =
      validateEntries genericScope (domainEntries domain)
    validateGenerics genericScope (binder : remaining) = do
      let GenericIdentifier (IdentifierString name) _ =
            genericBinderIdentifier binder
          bound = prepareGenericExpression generics
            (genericBinderBound binder)
      witness <- maybe (Left (UnknownIdentifier name)) Right
        (lookup name supplied)
      target <- evalInScope
        (extendScope genericScope captured) resolving bound
      _ <- if name `elem` trusted
        then Right witness
        else specifyValues witness target
      validateGenerics
        (scopeBinding name (EvaluatedBinding witness) : genericScope)
        remaining
    validateEntries genericScope [] = Right genericScope
    validateEntries genericScope (entry : remaining) = do
      case entry of
        IdentifierOperation (IdentifierString name) annotation _
          | name `notElem` genericNames ->
              validateNamed genericScope name annotation
        optional
          | Just
              (IdentifierOperation (IdentifierString name) annotation _, _)
              <- optionalIdentifierExpression optional
          , name `notElem` genericNames ->
              validateNamed genericScope name annotation
        _ -> Right ()
      validateEntries genericScope remaining
    validateNamed genericScope name annotation =
      case lookup name supplied of
        Nothing -> Right ()
        Just value -> do
          target <- evalInScope
            (extendScope genericScope captured) resolving annotation
          () <$ specifyValues value target

inferGenericArgument
  :: Scope
  -> [String]
  -> [GenericBinder Expression]
  -> GenericArgumentBinder
  -> InterpretedValue
  -> [InterpretedValue]
  -> [(GenericArgumentBinder, InterpretedValue)]
  -> Either InterpretingError InterpretedValue
inferGenericArgument captured resolving generics binder _ evidence prior = do
  boundExpression <- maybe
    (Left (UnknownIdentifier name))
    (Right . prepareGenericExpression generics . genericBinderBound)
    (findBinder (genericArgumentBinderId binder) generics)
  let currentBindings =
        [ scopeBinding (genericArgumentName priorBinder)
            (EvaluatedBinding value)
        | (priorBinder, value) <- prior
        ]
  bound <- evalInScope
    (extendScope currentBindings captured) resolving boundExpression
  admissible <- keepSuccessful (`specifyValues` bound) evidence
  case admissible of
    [] -> Left (OverloadError OverloadNoMatch)
    first : remaining -> foldM combineInferenceEvidence first remaining
  where
    name = genericArgumentName binder

    findBinder _ [] = Nothing
    findBinder binderId (candidate : remaining)
      | genericBinderId candidate == binderId = Just candidate
      | otherwise = findBinder binderId remaining

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


createFunction :: ReductionContext -> Scope -> [String]
  -> Expression -> Expression -> Expression
  -> [Expression] -> Expression -> Either InterpretingError InterpretedValue
createFunction reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result =
  createFunctionWithGenerics reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result []

createFunctionWithGenerics
  :: ReductionContext
  -> Scope
  -> [String]
  -> Expression
  -> Expression
  -> Expression
  -> [Expression]
  -> Expression
  -> [GenericBinder Expression]
  -> Either InterpretingError InterpretedValue
createFunctionWithGenerics reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result
    generics = createFunctionWithEvaluatedTypes Nothing
      reduction captured resolving signature writtenDomainExpression
      writtenOutput bindings result generics

createFunctionWithEvaluatedTypes
  :: Maybe (InterpretedValue, InterpretedValue)
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
createFunctionWithEvaluatedTypes evaluatedTypes reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result
    generics = do
  let (domainExpression, substitutions) =
        staticGenericDomain generics writtenDomainExpression
      specifiedOutput = substituteDependent substitutions writtenOutput
      preparedBindings = map (prepareGenericExpression generics) bindings
      preparedResult = prepareGenericExpression generics result
  schema <- case evaluatedTypes of
    Just (input, _) -> pure (argumentSchemaFromValue input)
    Nothing -> compileParametersWithGenerics generics evaluate
      writtenDomainExpression domainExpression
  let inferredGenericNames = argumentSchemaInferredGenericNames schema
  let parameters = parameterBindings schema
      names = map fst parameters
      consistencyScope = extendScope
        (constantContextualBindings "it" anyTypeValue) captured
      bodyDeclarations =
        [ declaration
        | entry <- preparedBindings
        , Just declaration <- [blockDeclaration entry]
        ]
  -- Reject an unprovable recursive-scope shadow before invocation. Finite
  -- bindings still use the ordinary fixed-point comparison once parameter
  -- values are available.
  case [ name
       | declaration <- bodyDeclarations
       , let name = declarationName declaration
       , Just binding <- [lookupScope name captured]
       , not (bindingHasUnrestrictedShadowing binding)
       , bindingHasNoFiniteShadowingNormalForm binding
       ] of
    name : _ -> Left (InconsistentShadowing name)
    [] -> pure ()
  case [ name
       | name <- names
       , Just binding <- [lookupScope name consistencyScope]
       , not (bindingHasUnrestrictedShadowing binding)
       ] of
    name : _ -> Left (InconsistentShadowing name)
    [] -> pure ()
  case [ name
       | name <- names
       , name `elem` map fst (scopeBindings captured)
          || length (filter (== name) names) > 1
       ] of
    name : _ -> Left (IdentifierStringOverlap name)
    [] -> pure ()
  input <- parameterDomain schema
  let (explicitSelf, selfIncludesDependencies) = case
        lookupScope "_this" captured >>= contextualBinding of
        Just (includesDependencies, _) -> (True, includesDependencies)
        _ -> (False, False)
  output <- case evaluatedTypes of
    Just (_, preparedOutput) -> pure preparedOutput
    Nothing -> evaluate specifiedOutput
  let prepareWith trusted argument = do
        (prepared, imported) <-
          overloadArgumentSchemaCompleteWithTrustedGenerics
          (inferGenericArgument captured resolving generics)
          trusted schema argument
        let trustedNames =
              [ name
              | binder <- generics
              , Just _ <- [lookup (genericBinderId binder) trusted]
              , let GenericIdentifier (IdentifierString name) _ =
                      genericBinderIdentifier binder
              ]
        _ <- validateGenericArgumentsExcept
          (trustedNames <> inferredGenericNames)
          captured resolving generics writtenDomainExpression imported
        supplied <- if argumentSchemaHasInferredGenerics schema
          then argumentSchemaValidationArgument schema prepared
          else Right argument
        pure (PreparedFunctionArgument supplied prepared imported)
      prepare = prepareWith []
      evaluatePreparedBodyWith bodyResult
          callerActivation invocationReduction preparedCall = do
        let argument = functionPreparedArgument preparedCall
            imported = functionPreparedBindings preparedCall
            callCaptured = captured
              { scopeActivation = callerActivation
              , scopeHandoff = Nothing
              }
            bodySeed = enterScopeWithReceiver
              preparedCall [] callerActivation
              genericFunctionReturnHandoff callCaptured
        let genericNames =
              [ name
              | binder <- generics
              , let GenericIdentifier (IdentifierString name) _ =
                      genericBinderIdentifier binder
              ]
        dependentScope <- validateGenericArgumentsExcept
          genericNames callCaptured resolving generics
          writtenDomainExpression imported
        protectedDomain <- prepareProtectedDomain
          bodySeed callCaptured resolving generics
          writtenDomainExpression imported
        let ordinaryDependentScope =
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
              , Just value <- [lookup name protectedDomain]
              , not (valueIsScopeProtected value)
              ]
            bodyImported =
              [ (name, maybe value id (lookup name protectedDomain))
              | (name, value) <- imported
              ]
            bodyArgument = protectWithPoliciesOf
              (scopeActivation bodySeed)
              (map snd bodyImported)
              argument
            localBindings =
              constantContextualBindings "it" bodyArgument
                <> [ scopeBinding name (EvaluatedBinding value)
                   | (name, value) <- bodyImported
                   ]
                <> scopeBindings callCaptured
            bodyBase = scopeWithBindings localBindings bodySeed
        bodyScope <- importScopeWithin bodyBase [] preparedBindings
        value <- evalInScopeWith invocationReduction bodyScope [] bodyResult
        let escaped = withoutCanonicalDependencies
              ( nub
                  ( scopePresentationDependencies bodyScope
                      <> scopePresentationDependencies captured)
              )
              value
            codomainEvaluationScope = enterScope preparedCall
              codomainScope genericContinuationHandoff callCaptured
        pure (bodyScope, escaped, codomainEvaluationScope)
      evaluatePreparedBody = evaluatePreparedBodyWith preparedResult
      invoke callerActivation invocationReduction preparedCall = do
        (bodyScope, escaped, codomainEvaluationScope) <-
          evaluatePreparedBody callerActivation invocationReduction preparedCall
        let handed = handoffScopeValue bodyScope escaped
        dynamicOutput <- case evaluatedTypes of
          Just (_, preparedOutput) -> pure preparedOutput
          Nothing -> evalInScopeWith invocationReduction
            codomainEvaluationScope resolving writtenOutput
        let handedOutput = handoffScopeValue
              codomainEvaluationScope dynamicOutput
        specified <- contextuallySpecify handed handedOutput
        pure (EvaluatedFunctionInvocation specified (Just handedOutput))
  let definition = case evaluatedTypes of
        Just _ -> FunctionBody bindings result
        Nothing -> FunctionApplication signature
          (FunctionBody bindings result)
      signatureText = renderSourceExpression definition
      self = case [bindingKey name expressionValue
                  | (name, binding) <- scopeBindings captured
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
  let functionValue = makeFunctionValue
        (EvaluatedFunction input output Nothing Nothing
          (Just (renderSourceExpression closed)) Nothing signatureText
          (Just prepare) (Just invoke) False)
      validateExistentialPackage source = do
        rows <- argumentRows source
        tryPackageRows source Nothing rows
      tryPackageRows _ Nothing [] = Left (OverloadError OverloadNoMatch)
      tryPackageRows _ (Just failure) [] = Left failure
      tryPackageRows source previousFailure (row : remainingRows) =
        case splitExistentialRow generics row of
          Nothing -> tryPackageRows source previousFailure remainingRows
          Just (prefix, fibreSource) ->
            case validatePackageRow source prefix fibreSource of
              Right selected -> Right selected
              Left failure ->
                tryPackageRows source (Just failure) remainingRows
      validatePackageRow source prefix fibreMembers = do
        preparedCall <- prepare (makeAtlasMap 2 prefix)
        (bodyScope, protectedFibre, _) <- evaluatePreparedBody
          (scopeActivation captured) reduction preparedCall
        fibre <- case authorizeProtectedValue
            (scopeActivation bodyScope) protectedFibre of
          Right actual -> Right actual
          Left _ -> Left (OverloadError OverloadNoMatch)
        let fibreSource = makeAtlasMap 2 fibreMembers
        _ <- specifyValues fibreSource fibre
        pure source
      existentialView
        | any ((== GenericSum) . genericBinderPolarity) generics =
            Just (makeDependentSumValue
              signatureText
              input
              validateExistentialPackage)
        | otherwise = Nothing
      existentialFunction = maybe functionValue
        (`withDependentSumView` functionValue) existentialView
  reservationTarget <- case genericFamilyEnvelope generics preparedResult of
    Nothing -> Right Nothing
    Just envelopeResult ->
      case genericUpperBoundWitnesses captured resolving reduction generics of
        Left _ -> Right Nothing
        Right trusted ->
          case prepareWith trusted (makeAtlasMap 0 []) of
            Left _ -> Right Nothing
            Right preparedCall ->
              case evaluatePreparedBodyWith envelopeResult
                  (scopeActivation captured) reduction preparedCall of
                Left _ -> Right Nothing
                Right (bodyScope, value, _) ->
                  case authorizeProtectedValue
                      (scopeActivation bodyScope) value of
                    Left _ -> Right Nothing
                    Right actual -> Right (Just actual)
  let reservedFunction = maybe existentialFunction
        (`withDependentSumReservationTarget` existentialFunction)
        reservationTarget
  mapView <- genericFunctionMapView
    captured resolving reduction generics prepareWith invoke
  let projectedFunction = maybe reservedFunction
        (`withMapView` reservedFunction) mapView
      protectedFunction = protectWithPoliciesOf
        (scopeActivation captured)
        (scopeProtectedValues captured)
        projectedFunction
  pure (protectWithPoliciesOf
    (scopeActivation captured)
    (scopeProtectedValues captured)
    protectedFunction)
  where
    evaluate = evalInScopeWith reduction captured resolving

-- | Split a dependent-sum package without letting an optional generic slot
-- consume the entire package as one positional value. Explicitly named
-- witnesses win; optional names may otherwise consume the next unnamed
-- member. The unconsumed members form the dependent fibre.
splitExistentialRow
  :: [GenericBinder Expression]
  -> [InterpretedValue]
  -> Maybe ([InterpretedValue], [InterpretedValue])
splitExistentialRow binders = select [] binders
  where
    select selected [] remaining = Just (reverse selected, remaining)
    select selected (binder : later) remaining = do
      let GenericIdentifier (IdentifierString name) optional =
            genericBinderIdentifier binder
      (witness, rest) <-
        removeFirst ((== Just name) . fst . suppliedArgumentValue) remaining
          <|> if optional
            then removeFirst
              ((== Nothing) . fst . suppliedArgumentValue)
              remaining
            else Nothing
      select (witness : selected) later rest

    removeFirst _ [] = Nothing
    removeFirst predicate (value : remaining)
      | predicate value = Just (value, remaining)
      | otherwise = do
          (selected, rest) <- removeFirst predicate remaining
          pure (selected, value : rest)

-- | A leading ordinal-indexed generic gives a function an ordinary lazy Atlas
-- view. Atomic valued ranges and products of them share this interface. Each
-- selected witness fixes one telescope entry; another enumerable entry makes
-- the next curried map. Naming optionality and privacy affect calls, not
-- whether this map view exists.
genericFunctionMapView
  :: Scope
  -> [String]
  -> ReductionContext
  -> [GenericBinder Expression]
  -> ( [(GenericBinderId, InterpretedValue)]
       -> InterpretedValue
       -> Either InterpretingError PreparedFunctionArgument)
  -> ( ScopeActivation
       -> ReductionContext
       -> PreparedFunctionArgument
       -> Either InterpretingError EvaluatedFunctionInvocation)
  -> Either InterpretingError (Maybe InterpretedValue)
genericFunctionMapView
    captured resolving reduction generics prepare invoke =
  case generics of
    [] -> Right Nothing
    _ -> build [] generics
  where
    build selected [] = do
      prepared <- prepare (reverse selected) (makeAtlasMap 0 [])
      invocation <- invoke
        (scopeActivation captured) reduction prepared
      pure (Just (functionInvocationValue invocation))
    build selected (binder : remaining) = do
      let boundExpression = prepareGenericExpression generics
            (genericBinderBound binder)
          selectedScope =
            [ scopeBinding name (EvaluatedBinding witness)
            | selectedBinder <- generics
            , let identity = genericBinderId selectedBinder
            , Just witness <- [lookup identity selected]
            , let GenericIdentifier (IdentifierString name) _ =
                    genericBinderIdentifier selectedBinder
            ]
      bound <- evalInScopeWith reduction
        (extendScope selectedScope captured) resolving boundExpression
      case ordinalIndexedValueFamily bound of
        Nothing -> pure Nothing
        Just family -> pure (Just (makeLazyMapValue
          (ordinalIndexedFamilyOrderType family)
          (\position -> do
            witness <- ordinalIndexedFamilyValueAt family position
            either (const Nothing) id
              (build
                ((genericBinderId binder, witness) : selected)
                remaining))))

-- | Evaluate each upper bound in telescope order so a generic family can
-- build structural metadata without inventing a concrete witness.  These
-- values are trusted only for the metadata evaluation; ordinary calls still
-- validate concrete witnesses through the regular argument path.
genericUpperBoundWitnesses
  :: Scope
  -> [String]
  -> ReductionContext
  -> [GenericBinder Expression]
  -> Either InterpretingError [(GenericBinderId, InterpretedValue)]
genericUpperBoundWitnesses captured resolving reduction generics =
  go [] generics
  where
    go selected [] = Right
      [(identity, value) | (identity, _, value) <- reverse selected]
    go selected (binder : remaining) = do
      let boundExpression = prepareGenericExpression generics
            (genericBinderBound binder)
          selectedScope =
            [ scopeBinding selectedName (EvaluatedBinding value)
            | (_, selectedName, value) <- selected
            ]
          GenericIdentifier (IdentifierString name) _ =
            genericBinderIdentifier binder
      bound <- evalInScopeWith reduction
        (extendScope selectedScope captured) resolving boundExpression
      go ((genericBinderId binder, name, bound) : selected) remaining

-- | Replace a prefix ending at a generic-sum witness with its open-prefix
-- envelope.  The resulting value contains every identifier name admitted by
-- the family, which lets argument matching reserve such names before choosing
-- one concrete page.
genericFamilyEnvelope
  :: [GenericBinder Expression]
  -> Expression
  -> Maybe Expression
genericFamilyEnvelope generics expressionValue =
  let transformed = go expressionValue
  in if null sumBinders then Nothing else Just transformed
  where
    sumBinders =
      [ genericBinderId binder
      | binder <- generics
      , genericBinderPolarity binder == GenericSum
      ]
    sumNames =
      [ name
      | binder <- generics
      , genericBinderPolarity binder == GenericSum
      , let GenericIdentifier (IdentifierString name) _ =
              genericBinderIdentifier binder
      ]
    go current =
      case current of
        SuperEllipsisRange lower (GenericReferenceExpression reference)
          | genericReferenceBinderId reference `elem` sumBinders ->
              SuperEllipsisRangePlus (go lower)
        SuperEllipsisRange lower
            (IdentifierReference (IdentifierString name))
          | name `elem` sumNames -> SuperEllipsisRangePlus (go lower)
        _ -> mapExpressionChildren go current

prepareProtectedDomain
  :: Scope
  -> Scope
  -> [String]
  -> [GenericBinder Expression]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError [(String, InterpretedValue)]
prepareProtectedDomain
    bodyScope parent resolving generics domain supplied = do
  preparedGenerics <- go [] generics
  prepared <- protectEntries preparedGenerics (domainEntries domain)
  pure
    [ (name, handoffScopeValue domainScope value)
    | (name, value) <- prepared
    ]
  where
    domainScope = enterScopeWithReceiver supplied []
      (scopeActivation bodyScope)
      genericDomainToBodyHandoff
      parent
    domainActivation = scopeActivation domainScope
    domainLabel = currentScopeLabel domainActivation

    go prepared [] = Right (reverse prepared)
    go prepared (binder : remaining) = do
      let GenericIdentifier (IdentifierString name) _ =
            genericBinderIdentifier binder
          boundExpression = prepareGenericExpression generics
            (genericBinderBound binder)
          dependentScope =
            [ scopeBinding preparedName (EvaluatedBinding value)
            | (preparedName, value) <- prepared
            ]
      witness <- maybe (Left (UnknownIdentifier name)) Right
        (lookup name supplied)
      target <- evalInScope
        (extendScope dependentScope domainScope) resolving boundExpression
      let protectedWitness =
            case genericBinderPolarity binder of
              GenericSum ->
                protectGenericExistential domainLabel witness
              GenericProduct -> protectWithPoliciesOf
                domainActivation [target] witness
      go ((name, protectedWitness) : prepared) remaining

    -- An ordinary parameter inherits every protection policy carried by its
    -- evaluated annotation.  For example, after protecting the existential
    -- witness in @^T@, both @marker : T@ and @value : T@ must enter the body
    -- protected as well.  Merely validating them against T is insufficient:
    -- it would install their raw values and allow the existential to escape.
    protectEntries prepared [] = Right prepared
    protectEntries prepared (entry : remaining) = do
      extended <- case namedDomainEntry entry of
        Just (name, annotation)
          | name `notElem` genericNames
          , Just value <- lookup name supplied -> do
              target <- evalInScope
                (extendScope (preparedBindings prepared) domainScope)
                resolving
                annotation
              let protected = protectWithPoliciesOf
                    domainActivation [target] value
              pure ((name, protected) : prepared)
        _ -> Right prepared
      protectEntries extended remaining

    namedDomainEntry entry =
      case entry of
        IdentifierOperation (IdentifierString name) annotation _ ->
          Just (name, annotation)
        optional
          | Just
              (IdentifierOperation (IdentifierString name) annotation _, _)
              <- optionalIdentifierExpression optional ->
                Just (name, annotation)
        _ -> Nothing

    preparedBindings prepared =
      [ scopeBinding name (EvaluatedBinding value)
      | (name, value) <- prepared
      ]

    genericNames =
      [ name
      | binder <- generics
      , let GenericIdentifier (IdentifierString name) _ =
              genericBinderIdentifier binder
      ]

applyFunction
  :: ScopeActivation
  -> ReductionContext
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError
      (InterpretedValue, Maybe InterpretedValue)
applyFunction activation reduction callable input =
  case selectFunctionCandidate preparations of
    Right (function, preparedCall)
      | Just invoke <- attachedFunctionInvocation function -> do
        nextReduction <- consumeReduction reduction
        invocation <- invoke activation nextReduction preparedCall
        let value = functionInvocationValue invocation
        (result, contract) <- if attachedFunctionValidatesResult function
          then do
            checked <- contextuallySpecify value (functionCodomain function)
            pure (checked, Just (functionCodomain function))
          else pure (value, functionInvocationContract invocation)
        -- A syntax-backed call already carries its surface representation.
        -- Ordinary application composes the callable and argument presentation
        -- trees directly, leaving each operand responsible for its own lexical
        -- fallback.
        pure
          ( case functionSyntax function of
              Just _ -> result
              Nothing
                | interpretedTypeIsTotal result -> result
                | otherwise -> withCanonicalApplication callable input result
          , contract
          )
    Right _ -> Left (FunctionEvaluationFailed
      HostSyntaxHookRequiresAstCaptures)
    Left failure -> Left failure
  where
    preparations = [(function, prepare function)
      | function <- functionAlternatives callable]
    prepare function =
      case attempt input of
        Right prepared -> Right prepared
        Left failure@(OverloadError OverloadNamedPrivateSlot) -> Left failure
        Left original -> case stripOuterIdentifierValue input of
          Right erased -> attempt erased
          Left _ -> Left original
      where
        attempt argument = case functionPrepare function of
          Just operation -> operation argument
          Nothing -> PreparedFunctionArgument argument argument []
            <$ validateFunctionInput argument (functionDomain function)

attachFunctionBody
  :: InterpretedValue
  -> EvaluatedFunctionBody
  -> Either InterpretingError InterpretedValue
attachFunctionBody signatureValue body =
  case interpretedFunction signatureValue of
    Just signature -> Right (makeFunctionValue (attach signature))
    Nothing -> Left (FunctionEvaluationFailed ExpectedFunctionType)
  where
    attach signature = case body of
      EvaluatedSyntaxFunctionBody {} -> signature
        { functionSource = Just (attachedSource signature)
        , functionBody = Just body
        }
      EvaluatedRuntimeFunctionBody _ implementation -> signature
        { functionSource = Just (attachedSource signature)
        , functionBody = Just body
        , functionPrepare = Just (\argument ->
            case functionPrepare signature of
              Just prepare -> case prepare argument of
                Right preparedSignature -> Right preparedSignature
                Left _ -> prepareBody argument
              Nothing -> prepareBody argument)
        }
        where
          prepareBody argument = do
            prepared <- case functionPrepare implementation of
              Just prepare -> prepare argument
              Nothing -> pure
                (PreparedFunctionArgument argument argument [])
            prepared <$ validateFunctionInput
              (functionSuppliedArgument prepared)
              (functionDomain signature)
    attachedSource signature =
      functionSignatureSource signature <> " " <> functionBodySource body

attachedFunctionInvocation
  :: EvaluatedFunction
  -> Maybe
      (ScopeActivation
        -> ReductionContext
        -> PreparedFunctionArgument
        -> Either InterpretingError EvaluatedFunctionInvocation)
attachedFunctionInvocation function =
  case functionInvoke function of
    Just invoke -> Just invoke
    Nothing -> case functionBody function of
      Just (EvaluatedRuntimeFunctionBody _ implementation) ->
        functionInvoke implementation
      _ -> Nothing

attachedFunctionValidatesResult :: EvaluatedFunction -> Bool
attachedFunctionValidatesResult function =
  case functionBody function of
    Just (EvaluatedRuntimeFunctionBody _ implementation) ->
      functionValidatesResult implementation
    _ -> functionValidatesResult function

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

withModuleScopeOperands :: Expression -> Maybe [Expression]
withModuleScopeOperands expressionValue = case expressionValue of
  ArgumentMap modules
    | not (null modules)
    , all (null . bindingNames) modules -> Just modules
  _ -> Nothing

evaluateImport
  :: ReductionContext
  -> Scope
  -> [String]
  -> Expression
  -> [String]
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateImport reduction captured resolving sourceExpression paths body =
  case body of
    FunctionBody declarations result -> do
      modules <- traverse load (nub paths)
      let loaded =
            [ (loadedModuleIdentity loadedModule, binder)
            | loadedModule <- modules
            , binder <- loadedModuleBinders loadedModule
            ]
          names = map (loadedModuleBinderName . snd) loaded
      case
          [ name
          | name <- names
          , name `elem` map fst (scopeBindings captured)
          ] of
        name : _ -> Left (IdentifierStringOverlap name)
        [] -> pure ()
      domain <- importDomainValue (map loadedModuleFederation modules)
      let schema = argumentSchemaFromValue domain
      input <- parameterDomain schema
      let prepare argument = do
            (prepared, bindings) <-
              overloadArgumentSchemaComplete schema argument
            pure (PreparedFunctionArgument argument prepared bindings)
          invoke callerActivation invocationReduction preparedCall = do
            let argument = functionPreparedArgument preparedCall
                supplied = functionPreparedBindings preparedCall
                callCaptured = captured
                  { scopeActivation = callerActivation
                  , scopeHandoff = Nothing
                  }
                bodySeed = enterScopeWithReceiver
                  preparedCall [] callerActivation
                  genericFunctionReturnHandoff callCaptured
                bodyArgument = protectWithPoliciesOf
                  (scopeActivation bodySeed) (map snd supplied) argument
                bodyDependency = childPresentationDependency
                  bodySeed declarations
            importedBindings <- traverse
              (importArgumentBinding bodyDependency supplied) loaded
            let localBindings =
                  constantContextualBindings "it" bodyArgument
                    <> importedBindings
                    <> scopeBindings callCaptured
                bodyBase = scopeWithBindings localBindings bodySeed
            bodyScope <- importScopeWithin bodyBase [] declarations
            value <- evalInScopeWith
              invocationReduction bodyScope resolving result
            let escaped = withoutCanonicalDependencies
                  ( nub
                      ( scopePresentationDependencies bodyScope
                          <> scopePresentationDependencies captured)
                  )
                  value
                handed = handoffScopeValue bodyScope escaped
            pure (EvaluatedFunctionInvocation handed Nothing)
          callable = makeFunctionValue (EvaluatedFunction
            input anyTypeValue Nothing Nothing Nothing Nothing
            (renderSourceExpression sourceExpression)
            (Just prepare) (Just invoke) False)
      (applied, _) <- applyFunction
        (scopeActivation captured) reduction callable domain
      pure (withoutCanonicalPresentation applied)
    _ -> Left (FunctionEvaluationFailed ExpectedFunctionType)
  where
    load requested = do
      moduleSource <- lookupModule captured requested
      let isolatedBase = scopeWithBindings [] captured
      loadedModuleResultWithBase isolatedBase moduleSource

importDomainValue
  :: [InterpretedValue]
  -> Either InterpretingError InterpretedValue
importDomainValue values =
  case values of
    [] -> Right (makeAtlasMap 0 [])
    first : remaining -> foldM concatenateValues first remaining

importArgumentBinding
  :: PresentationDependency
  -> [(String, InterpretedValue)]
  -> (FilePath, LoadedModuleBinder)
  -> Either InterpretingError (String, Binding)
importArgumentBinding dependency supplied (identity, binder) = do
  let name = loadedModuleBinderName binder
  value <- maybe (Left (UnknownIdentifier name)) Right (lookup name supplied)
  pure (scopeBinding name (ImportedBinding
    dependency identity value (loadedModuleBinderScope binder)))


importLoadedModule
  :: Scope
  -> Bool
  -> ModuleSource
  -> Either InterpretingError Scope
importLoadedModule scope openMembers source = do
  let isolatedBase = scopeWithBindings [] scope
  (identity, binders) <- loadedModuleBindersWithBase isolatedBase source
  let dependency = case scopePresentationDependency scope of
        Just current -> current
        Nothing -> PresentationDependency ("import:" <> identity)
      alreadyImported = all (sameImportedBinding identity scope) binders
  qualified <- foldM (insertBinder dependency identity) scope binders
  if openMembers
    then foldM (openBinderMembers alreadyImported identity) qualified binders
    else pure qualified
  where
    sameImportedBinding identity values binder =
      case lookupScope (loadedModuleBinderName binder) values of
        Just (ImportedBinding _ previous _ _) -> previous == identity
        _ -> False
    insertBinder dependency identity values binder =
      let name = loadedModuleBinderName binder
          entry = scopeBinding name (ImportedBinding
            dependency identity
            (loadedModuleBinderValue binder)
            (loadedModuleBinderScope binder))
      in case lookupScope name values of
        Nothing -> Right (extendScope [entry] values)
        Just (ImportedBinding _ previous _ _) | previous == identity ->
          Right values
        _ -> Left (IdentifierStringOverlap name)
    openBinderMembers alreadyImported identity values binder = do
      exported <- moduleExportsFromValue (loadedModuleBinderValue binder)
      entries <- moduleExportBindings
        values
        (loadedModuleBinderName binder)
        identity
        (loadedModuleBinderScope binder)
        exported
      foldM (insertExport alreadyImported) values entries
    insertExport alreadyImported values entry@(name, _) =
      case lookupScope name values of
        Nothing -> Right (extendScope [entry] values)
        Just _ | alreadyImported -> Right values
        _ -> Left (IdentifierStringOverlap name)

-- Both evaluated scope access and resource preparation install opened
-- members through this boundary. Imported binders retain their definition
-- scopes and presentation metadata; ordinary local values use evaluated
-- public members.
openedScopeContributionBindings
  :: Scope
  -> (Expression, InterpretedValue)
  -> Either InterpretingError ScopeBindings
openedScopeContributionBindings scope (operand, actual) =
  case operand of
    IdentifierReference (IdentifierString namespace)
      | Just (ImportedBinding _ identity _ internal) <-
          lookupScope namespace scope -> do
          exported <- moduleExportsFromValue actual
          moduleExportBindings
            scope namespace identity internal exported
    _ -> do
      members <- scopeNamedMembers actual
      traverse openedBinding (public members)
  where
    openedBinding (name, selected) = do
      payload <- accessValues selected (naturalValue 1)
      pure (scopeBinding name (EvaluatedBinding payload))

moduleExportBindings
  :: Scope
  -> String
  -> FilePath
  -> Scope
  -> [ModuleExport]
  -> Either InterpretingError ScopeBindings
moduleExportBindings scope namespace identity internal exportedValues =
  pure
    [ scopeBinding name
        (case presentation of
          CanonicalValueImportPresentation -> NamedBinding
            (canonicalValuePresentationDependency identity)
            (QualifiedBinding (namespace <> "." <> name) binding)
          TransparentImportPresentation -> QualifiedBinding
            (namespace <> "." <> name)
            (NamedBinding dependency binding))
    | ModuleExport name presentation evaluated <- exportedValues
    , let binding = maybe evaluated (retainExportDefinition evaluated)
            (lookupScope name internal)
    ]
  where
    dependency = case scopePresentationDependency scope of
      Just current -> current
      Nothing -> PresentationDependency ("import:" <> identity)

loadedModuleBindersWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError (FilePath, [LoadedModuleBinder])
loadedModuleBindersWithBase base moduleSource = do
  loaded <- loadedModuleResultWithBase base moduleSource
  pure (loadedModuleIdentity loaded, loadedModuleBinders loaded)

loadedModuleResultWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError LoadedModuleResult
loadedModuleResultWithBase base
    moduleSource@(ModuleSource path expression _) = do
  prepared <- moduleBaseScope base moduleSource
  (resourceBase, resource) <- prepareModuleResource prepared expression
  (resourceBindings, resultExpression) <- resourceBlock resource
  outer <- importScopeWithoutContextualThis resourceBase [] resourceBindings
  result <- evalInScope outer [] resultExpression
  exported <- case importNamedBindings result of
    Right bindings@(_ : _) -> Right bindings
    _ | interpretedValueKind result == DependentIdentifierTypeValueKind ->
      Right []
    Right [] -> Left (ModuleEvaluationFailed
      ImportedModuleRequiresIdentifierBinderFederation)
    Left _ -> Left (ModuleEvaluationFailed
      ImportedModuleRequiresIdentifierBinderFederation)
  binders <- traverse (loadedBinder outer resultExpression) exported
  pure LoadedModuleResult
    { loadedModuleIdentity = path
    , loadedModuleFederation = handoffScopeValue outer result
    , loadedModuleBinders = binders
    }
  where
    loadedBinder outer resultExpression
        (ModuleExport name presentation binding) = do
      value <- case binding of
        EvaluatedBinding evaluated -> Right evaluated
        _ -> Left (ModuleEvaluationFailed
          ImportedModuleRequiresIdentifierBinderFederation)
      internal <- moduleBinderScope outer resultExpression name
      pure LoadedModuleBinder
        { loadedModuleBinderName = name
        , loadedModuleBinderPresentation = presentation
        , loadedModuleBinderValue = handoffScopeValue outer value
        , loadedModuleBinderScope = internal
        }

moduleBinderScope
  :: Scope
  -> Expression
  -> String
  -> Either InterpretingError Scope
moduleBinderScope outer resultExpression name =
  case namedBinderValueExpression name resultExpression of
    Just (Begin declarations _) -> importScope outer [] declarations
    _ -> Right outer

namedBinderValueExpression :: String -> Expression -> Maybe Expression
namedBinderValueExpression selected expressionValue = case expressionValue of
  IdentifierOperation (IdentifierString name) annotation given
    | name == selected -> Just (case given of
        Nothing -> annotation
        Just value
          | value == annotation -> value
          | otherwise -> MapSpecification value annotation)
  AtlasMap members -> firstJust members
  ArgumentMap members -> firstJust members
  MapSequence members -> firstJust members
  MapConcatenation left right ->
    namedBinderValueExpression selected left
      <|> namedBinderValueExpression selected right
  SyntaxBoundary inner -> namedBinderValueExpression selected inner
  _ -> Nothing
  where
    firstJust = foldr
      ((<|>) . namedBinderValueExpression selected)
      Nothing

moduleBaseScope
  :: Scope
  -> ModuleSource
  -> Either InterpretingError Scope
moduleBaseScope base
    moduleSource@(ModuleSource path _ dependencies) = do
  let seeded = extendScope
        [ ("\0scope", LexicalScope (PresentationDependency ("module:" <> path)))
        , ("\0imports", ModuleCatalog ((path, moduleSource) : dependencies))
        ]
        base
      standardDependency =
        [ source
        | (_, source@(ModuleSource identity _ _)) <- dependencies
        , takeFileName identity == standardLibraryFileName
        ]
  case (takeFileName path == standardLibraryFileName, standardDependency) of
    (False, standard : _) -> importLoadedModule seeded False standard
    (True, _) -> do
      host <- datraHostValue
      Right (extendScope
        [ (datraHostIdentifier, EvaluatedBinding
            (withCanonicalReference [] datraHostIdentifier host))
        ] seeded)
    _ -> Right seeded

-- Resource-level scope access and import wrap the declarations which produce
-- a module value. Prepare those lexical scopes once so value evaluation and
-- retained export definitions close over precisely the same bindings.
prepareModuleResource
  :: Scope
  -> Expression
  -> Either InterpretingError (Scope, Expression)
prepareModuleResource base expressionValue = case expressionValue of
  ScopeAccess source body -> do
    value <- case source of
      IdentifierReference (IdentifierString namespace)
        | Just (ImportedBinding _ _ value _) <-
            lookupScope namespace base -> Right value
      _ -> evalInScope base [] source
    bindings <- openedScopeContributionBindings base (source, value)
    prepareModuleResource (extendScope bindings base) body
  Import paths (FunctionBody bindings result) -> do
    imported <- foldM importQualified base (nub paths)
    prepareModuleResource imported (Begin bindings result)
  Import _ _ -> Left (FunctionEvaluationFailed ExpectedFunctionType)
  _ -> Right (base, expressionValue)
  where
    importQualified imported requested = do
      source <- lookupModule imported requested
      importLoadedModule imported False source

moduleExportNames :: ModuleSource -> Either InterpretingError [String]
moduleExportNames source = do
  base <- rootScopeWithDatra source []
  (_, binders) <- loadedModuleBindersWithBase base source
  concat <$> traverse binderExports binders
  where
    binderExports binder = do
      exported <- moduleExportsFromValue (loadedModuleBinderValue binder)
      pure (map moduleExportName exported)

moduleSyntaxRules
  :: String
  -> ModuleSource
  -> Either InterpretingError [SyntaxRule]
moduleSyntaxRules requested source = do
  ruleSets <- moduleSyntaxRuleSets requested source
  pure (concatMap snd ruleSets)

moduleSyntaxRuleSets
  :: String
  -> ModuleSource
  -> Either InterpretingError [(String, [SyntaxRule])]
moduleSyntaxRuleSets requested source = do
  base <- rootScopeWithDatra source []
  (_, binders) <- loadedModuleBindersWithBase base source
  traverse rulesForBinder binders
  where
    rulesForBinder binder = do
      rules <- moduleSyntaxRulesFromValueIn
        requested
        (loadedModuleBinderName binder)
        (loadedModuleBinderValue binder)
      pure (loadedModuleBinderName binder, rules)

moduleSyntaxRulesFromValueIn
  :: String
  -> String
  -> InterpretedValue
  -> Either InterpretingError [SyntaxRule]
moduleSyntaxRulesFromValueIn requested scopeName moduleValue = do
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
        unscopedImplementation <- maybe
          (pure (IdentifierReference (IdentifierString name)))
          parseRuleExpression
          ( functionBodySource <$> functionBody function
              <|> functionSource function
          )
        let implementation = InModule scopeName unscopedImplementation
        pure
          [ SyntaxRule
              name template signature False (Just scopeName) implementation
          | template <- sourceTemplates
          ]
    parseScopedRuleExpression sourceText = do
      expressionValue <- parseRuleExpression sourceText
      pure (case expressionValue of
        AsciiStringLiteral {} -> expressionValue
        ScopeAccess {} -> expressionValue
        _ -> InModule requested expressionValue)
    parseRuleExpression sourceText =
      case parseDatra ("(" <> sourceText <> "\n)") of
        Right expressionValue -> Right expressionValue
        Left _ -> Left NoCanonicalStringConversion

moduleExportsFromValue
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
moduleExportsFromValue value =
  case namedBindings value of
    Right bindings -> Right bindings
    Left _ -> invalid
  where
    invalid = Left (ModuleEvaluationFailed
      ModuleScopeRequiresTotalMapOfSimpleIdentifierTypes)

scopeDeclarationMembers :: Scope -> [ScopeMember]
scopeDeclarationMembers scope = case lookupScope "_this" scope of
  Just binding | Just members <- scopeMembersBinding binding -> members
  _ -> []

publicDomainValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
publicDomainValue value = do
  members <- namedMembers value
  importDomainValue
    [ simpleIdentifierTypeValue name anyTypeValue
    | (name, _) <- public members
    ]

scopeNamedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
scopeNamedMembers = namedMembers

namedBindings
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
namedBindings value = namedMembers value >>= traverse namedBinding

-- An imported file may yield a federation that mixes ordinary named binders
-- with dependent identifier binders.  The dependent fibers remain in the
-- complete federation used as the synthesized function domain; this view is
-- only for installing the ordinary names as qualified lexical bindings.
importNamedBindings
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
importNamedBindings value =
  case scopeNamedMembers value of
    Right members -> traverse namedBinding members
    Left _ -> mixedBindings
  where
    mixedBindings = do
      members <- case argumentMapMembers value of
        Just arguments -> Right arguments
        Nothing -> do
          count <- maybe invalid Right
            (naturalAtOrdinal
              (interpretedMapFinalOrderType (interpretedMap value)))
          traverse memberAt
            (if count == 0 then [] else [0 .. count - 1])
      catMaybes <$> traverse export members
    invalid = Left (ModuleEvaluationFailed
      ImportedModuleRequiresIdentifierBinderFederation)
    memberAt index = maybe invalid Right
      (interpretedMapValueAt (interpretedMap value) (finiteOrdinal index))
    export member = case simpleIdentifierName member of
      Just name -> Just <$> namedBinding (name, member)
      Nothing
        | interpretedValueKind member == DependentIdentifierTypeValueKind ->
            Right Nothing
        | otherwise -> invalid

namedBinding
  :: (String, InterpretedValue)
  -> Either InterpretingError ModuleExport
namedBinding (name, selected) = do
  payload <- accessValues selected (naturalValue 1)
  pure (ModuleExport
    name
    (if hasTrailingIdentifierMarker canonicalValueMarker selected
      then CanonicalValueImportPresentation
      else TransparentImportPresentation)
    (EvaluatedBinding payload))

-- A canonical value name is owned by the exporting module, rather than by the lexical
-- scope that happened to import it. Keeping those dependencies distinct makes
-- the canonical spelling survive both explicit and implicit imports.
canonicalValuePresentationDependency :: FilePath -> PresentationDependency
canonicalValuePresentationDependency identity =
  PresentationDependency ("canonical-value:" <> identity)

lookupModule :: Scope -> String -> Either InterpretingError ModuleSource
lookupModule scope path
  | value : _ <-
      [ source
      | (_, ModuleCatalog modules) <- scopeBindings scope
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
  case lookupScope path scope of
    Just (ImportedBinding _ _ _ imported) -> Right imported
    _ -> case
      [ imported
      | (_, ImportedBinding _ identity _ imported) <- scopeBindings scope
      , identity == path
      ] of
      imported : _ -> Right imported
      [] -> lookupModule scope path >>= moduleScope

moduleScope :: ModuleSource -> Either InterpretingError Scope
moduleScope source = do
  base <- rootScopeWithDatra source []
  moduleScopeWithBase base source

moduleScopeWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError Scope
moduleScopeWithBase base
    moduleSource@(ModuleSource _ expression _) = do
  prepared <- moduleBaseScope base moduleSource
  (resourceBase, resource) <- prepareModuleResource prepared expression
  (resourceBindings, _) <- resourceBlock resource
  outer <- importScopeWithoutContextualThis resourceBase [] resourceBindings
  case namedBeginBlock resource of
    Just (_, declarations, _) ->
      importScope outer [] declarations
    Nothing -> Right outer

resourceBlock
  :: Expression
  -> Either InterpretingError ([Expression], Expression)
resourceBlock (Begin bindings result) = Right (bindings, result)
resourceBlock _ = Left (ModuleEvaluationFailed ImportedModuleRequiresBlock)

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
      either (const Nothing) id
        (selectedDeclarationName (scopeDeclarationMembers scope) index)
    moduleResolver path = case
        [ imported
        | (_, ImportedBinding _ identity _ imported) <- scopeBindings scope
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
      | Just (ImportedBinding _ identity _ imported) <- lookupScope name scope
      , Just dependency <- resolveDependency (closureResolver imported) fields =
          Just dependency
            { dependencyKey = identity <> ":" <> dependencyKey dependency
            , dependencyName = originName name <> "." <> dependencyName dependency
            , dependencyExpression = normalizeExpression
                (dependencyExpression dependency)
            }
    resolve (name : fields) = do
      binding <- lookupScope name scope
      case (fields, bindingDefinition binding) of
        ([], Just (lexical, _, expressionValue)) ->
          Just (Dependency (bindingKey name expressionValue)
            (originName name) expressionValue (closureResolver lexical))
        _ -> do
          value <- either (const Nothing) Just
            (resolveIdentifier scope [] name)
          selected <- either (const Nothing) Just
            (foldM namedAccessValue value fields)
          if hasTrailingIdentifierMarker canonicalValueMarker selected
            then Nothing
            else do
              expressionValue <- either (const Nothing) Just
                (valueExpression selected)
              pure (Dependency
                (intercalate "." (name : fields) <> ":" <> show expressionValue)
                (intercalate "." (originName name : fields))
                expressionValue emptyResolver)
    originName name
      | Just original <- lookup name
          (concat
            [names | (_, CanonicalNames names) <- scopeBindings scope]) = original
      | Just binding <- lookupScope name scope
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
defaultDefinitionScope = defaultModuleSource >>= \source -> do
  base <- rootScopeWithDatra source []
  moduleScopeWithBase base source
