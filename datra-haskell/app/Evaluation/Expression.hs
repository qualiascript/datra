{-# LANGUAGE PatternSynonyms #-}

-- | Recursive interpretation of the parsed Datra AST.
--
-- This module owns the mutually recursive expression-evaluation knot. Checked
-- semantic operations and their strongly typed failures remain in 'DatraTypes';
-- structural scope and closure operations live in sibling Evaluation modules.
module Evaluation.Expression
  ( prepareModuleSource
  , installPreparedModules
  , standardLibraryModuleSource
  , moduleExportNames
  , interpretLocatedWithModulesAndStandardLibraryVisibility
  , interpretWithModules
  , interpretWithModulesAndStandardLibraryVisibility
  , InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
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
  -- Stateless evaluation capabilities used while source rewriting derives
  -- syntax visibility directly from Scope.
  , standardLibraryEnvironment
  , syntaxExpressionType
  , parsedDefaultModule
  ) where

import Data.Bifunctor qualified as Bifunctor
import Data.Char (isSpace)
import Data.List (nub, nubBy, partition)
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import DatraLanguage.DependentDeclaration
import DatraTypes.Closure
import DatraTypes.Contextual
import DatraTypes.Declaration
import DatraTypes.Evaluation
import DatraTypes.LookupCapture
import DatraTypes.Module
import DatraTypes.Module.Source
import DatraTypes.Resolution
import DatraTypes.Scope
import Evaluation.Closure
import Evaluation.Identifier
import Evaluation.Scope
import DatraHost
  ( datraHostIdentifier
  , datraHostValue
  )
import DatraLanguage.Identifier
  ( isIdentifierValue
  )
import DatraTypes.Lookup
  ( lookupKeyFieldName
  , lookupValueFieldName
  )
import LibraryFiles
  ( standardLibraryFileName
  , requiredBundledLibrarySource
  )
import Control.Applicative ((<|>))
import Control.Monad (foldM)
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.AST
  ( Expression (..)
  , pattern FunctionType
  , GenericBinder (..)
  , GenericBinderId
  , GenericArgument (..)
  , GenericPolarity (..)
  , IdentifierExpression (..)
  , SimpleIdentifierString (..)
  , StringTemplateInterpolation (..)
  , attachedFunctionImplementation
  , dependentArgumentExpression
  , identifierExpressionExpression
  , literalIdentifierExpression
  , literalIdentifierName
  , optionalIdentifierExpression
  , mapExpressionChildren
  , mapDependentDeclaration
  , normalizeExpression
  )
import DatraLanguage.ContextualDeclaration
import StringExpression
  ( FunctionSyntax (FunctionSyntax)
  , StringExpression (..)
  )
import DatraTypes
import DatraTypes.FunctionType
  ( FunctionTypeIdentifier (..)
  , forwardGenericBoundReference
  , functionTypeIdentifiers
  , prepareFunctionDomainExpression
  , prepareGenericExpression
  , resolveGenericFunctionTypes
  )
import Parsing
  ( parseSourceExpression
  , parseDatraRawLocatedWithSourceName
  )
import SyntaxRewriting
  ( rewriteResourceSyntaxLocated
  , rewriteStandaloneSyntax
  )
import Rendering (renderCanonicalResult, renderInterpretedValue)
import Evaluation.Scope.GenericProtection
import Evaluation.Scope.Protection
import StringInterpolation
  ( identifierExpressionBranches
  , identifierExpressionMatchingBranches
  )
import DatraLanguage.Application (applicationFrom)
import StringInterpolation.Exact (matchExactSegments)
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located, locatedValue)
  , atSourceSpan
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( ParseFailure (..) )
import DatraLanguage.Diagnostics.Localization
  ( Locale (English)
  , renderDatraError
  )
import Numeric.Natural (Natural)
import DatraOrdinal
  ( finiteOrdinal
  , finiteOrdinalPositions
  , naturalAtOrdinal
  , naturalsBelow
  , omega
  )
import FoliageMap (foliageMap, foliageMapPositionAt)
import System.FilePath (takeFileName)

shadowingConsistencyFuel :: Int
shadowingConsistencyFuel = 64

interpretLocatedExpression
  :: Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedExpression (Located sourceSpan expressionValue) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretExpressionReason expressionValue)

interpretLocatedWithModulesAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> PreparedModules
  -> Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedWithModulesAndStandardLibraryVisibility
    visibility modules (Located sourceSpan expression) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretWithModulesAndStandardLibraryVisibility
      visibility modules expression)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason expressionValue = do
  scope <- defaultModuleScope
  evalInScope scope [] expressionValue

-- | Evaluate a closed reconstruction without installing Std or any modules.
interpretClosedExpression :: Expression -> Either InterpretingError InterpretedValue
interpretClosedExpression expressionValue =
  evalInScope (rootScope expressionValue) [] expressionValue

interpretWithModules
  :: PreparedModules
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithModules modules expression = do
  scope <- defaultModuleScope
  installed <- installPreparedModules modules scope
  evalResourceInScopeWith UnrestrictedReduction
    installed
    [] expression

interpretWithModulesAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> PreparedModules
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretWithModulesAndStandardLibraryVisibility
    visibility modules expression = do
  base <- standardLibraryEnvironment visibility expression
  installed <- installPreparedModules modules base
  evalResourceInScopeWith UnrestrictedReduction
    installed
    []
    expression

installPreparedModules
  :: PreparedModules
  -> Scope
  -> Either InterpretingError Scope
installPreparedModules (PreparedModules modules) base =
  foldM install base modules
  where
    install scope prepared = installPreparedModule scope False prepared

prepareModuleSource
  :: PreparedModules
  -> ModuleSource
  -> Either InterpretingError PreparedModules
prepareModuleSource prepared@(PreparedModules modules) source = do
  base <- installPreparedModules prepared (rootScope source)
  loaded <- prepareModuleWithBase base source
  pure (PreparedModules (modules <> [loaded]))

defaultModuleScope :: Either InterpretingError Scope
defaultModuleScope = standardModuleScope True

standardLibraryEnvironment
  :: StandardLibraryVisibility
  -> Expression
  -> Either InterpretingError Scope
standardLibraryEnvironment visibility raw = case visibility of
  NoStandardLibrary -> Right (rootScope raw)
  QualifiedStandardLibrary -> standardModuleScope False
  AllStandardLibrary -> standardModuleScope True

standardModuleScope
  :: Bool
  -> Either InterpretingError Scope
standardModuleScope allNames = do
  source <- standardLibraryModuleSource
  base <- installDatraHost (rootScope source)
  prepared <- prepareModuleWithBase base source
  installPreparedModule base allNames prepared

installDatraHost :: Scope -> Either InterpretingError Scope
installDatraHost base = do
  host <- datraHostValue
  let declaration = (evaluatedRuntimeDeclaration datraHostIdentifier
        (withCanonicalReference [] datraHostIdentifier host))
        { runtimeDeclarationIsDefinition = True }
  pure (extendRuntimeDeclarations [declaration] base)

syntaxExpressionType :: Scope -> Expression -> Maybe InterpretedValue
syntaxExpressionType scope expressionValue = either (const Nothing) Just
  (evalInScope scope [] typeExpression)
  where
    typeExpression = case expressionValue of
      Equality {} -> BooleanType
      Inequality {} -> BooleanType
      LessThan {} -> BooleanType
      LessThanOrEqual {} -> BooleanType
      GreaterThan {} -> BooleanType
      GreaterThanOrEqual {} -> BooleanType
      _ -> expressionValue

parsedDefaultModule :: Either InterpretingError Expression
parsedDefaultModule = do
  locatedRaw@(Located _ raw) <- either parseFailure Right
    (parseDatraRawLocatedWithSourceName standardLibraryFileName
      (requiredBundledLibrarySource standardLibraryFileName))
  base <- installDatraHost (rootScope raw)
  let rewritten = rewriteResourceSyntaxLocated
        syntaxExpressionType base locatedRaw
  rewrittenValue <- locatedValue <$> either
    (parseFailure . SyntaxRewriteParseFailure)
    Right
    rewritten
  pure (resolveGenericFunctionTypes rewrittenValue)
  where
    parseFailure failure = Left (ModuleEvaluationFailed
      (StandardLibraryParseFailure standardLibraryFileName
        (renderDatraError English (withoutSourceSpan failure))))
{-# NOINLINE parsedDefaultModule #-}

standardLibraryModuleSource :: Either InterpretingError ModuleSource
standardLibraryModuleSource =
  ModuleSource standardLibraryFileName <$> parsedDefaultModule
{-# NOINLINE standardLibraryModuleSource #-}

canonicalStringCodec :: CanonicalStringCodec
canonicalStringCodec =
  CanonicalStringCodec
    { renderCanonicalString =
        renderInterpretedValue . withoutCanonicalPresentation
    , decodeCanonicalString = decodeCanonicalExpression
    }

-- Canonical text is Datra source, not a parallel scalar encoding. Parsing it
-- through the ordinary source grammar makes forms such as @-123@ use the
-- prefix operator and lets dependent declarations assign meanings to
-- otherwise ordinary identifiers such as @123@.
decodeCanonicalExpression :: String -> [InterpretedValue]
decodeCanonicalExpression characters =
  case do
      scope <- defaultModuleScope
      expressionValue <- obsoleteClosedSourceExpressionIn scope characters
      evalInScope scope [] expressionValue
    of
      Right value -> [value]
      Left _ -> []

scopeNameIsDefinition :: Scope -> String -> Bool
scopeNameIsDefinition scope name =
  any protectedDeclaration
      [ scoped
      | layer <- scopeDependentDeclarationLayers scope
      , scoped <- dependentDeclarationCandidates name layer
      ]
  where
    protectedDeclaration scoped =
      scopedDependentDeclarationIsDefinition scoped
        && either (const False) id
          (dependentDeclarationContainsName
            UnrestrictedReduction [] scoped name)

contextualRuntimeValue
  :: ContextualRole
  -> Scope
  -> Maybe
      ( Bool
      , Maybe [ScopedDependentDeclaration]
      , ResolutionStack
          -> ReductionContext
          -> Either InterpretingError InterpretedValue
      )
contextualRuntimeValue role scope = do
  runtime <- runtimeDeclarationByName (contextualPrivateName role) scope
  case runtimeDeclarationValue runtime of
    ContextualRuntimeValue _ includesDependencies declarations value ->
      Just (includesDependencies, declarations, value)
    EvaluatedRuntimeValue _ -> Nothing

contextualValue
  :: ContextualRole
  -> Scope
  -> Maybe
      ( Bool
      , ResolutionStack
          -> ReductionContext
          -> Either InterpretingError InterpretedValue
      )
contextualValue role scope =
  case contextualRuntimeValue role scope of
    Just (includesDependencies, _, value) ->
      Just (includesDependencies, value)
    Nothing -> Nothing

contextualDeclarations
  :: ContextualRole
  -> Bool
  -> (ReductionContext -> Either InterpretingError InterpretedValue)
  -> [RuntimeSingletonPayload]
contextualDeclarations role includesDependencies value =
  [contextualRuntimeDeclaration role includesDependencies Nothing
    (const value)]

constantContextualDeclarations
  :: ContextualRole
  -> InterpretedValue
  -> [RuntimeSingletonPayload]
constantContextualDeclarations role value =
  [constantContextualRuntimeDeclaration role value]

-- | A contextual function's private, coalized map. Its name is @_inner_this@
-- or @_inner_it@, but it lives only in the native function closure and never
-- enters a Datra lexical scope.
-- | Collect same-kind contextual declarations from current to outermost. The
-- environment retained for a declaration-scope level begins at the previous
-- same-kind boundary, so declarations belonging to that outer scope remain
-- visible. Scopes which introduce no declaration of this kind add no hole.
contextualLevels
  :: ResolutionStack
  -> ContextualRole
  -> Scope
  -> [ContextualLevel]
contextualLevels resolving role scope =
  [ (includesDependencies, value resolving)
  | layer <- scopeDependentDeclarationLayers scope
  , scoped <- dependentDeclarationCandidates key layer
  , Just runtime <- [scopedDependentDeclarationRuntime scoped]
  , runtimeDeclarationName runtime == key
  , ContextualRuntimeValue selected includesDependencies _ value <-
      [runtimeDeclarationValue runtime]
  , selected == role
  ]
  where
    key = contextualPrivateName role

-- | A contextual function has the exact valued-natural domain of its
-- available same-kind lexical levels. @_this n@ and @_it n@ lower inside the
-- native closure to @_inner_this @ n@ and @_inner_it @ n@ respectively.
contextualFunction
  :: ContextualRole
  -> [ContextualLevel]
  -> Either InterpretingError InterpretedValue
contextualFunction role levels@(_ : _) = do
  domain <- valuedNaturalRangeValue 0 maximumDepth
  let schema = argumentSlotSchema Nothing False domain (Just (naturalValue 0))
  pure (makeFunctionValue (EvaluatedFunction
    domain
    anyTypeValue
    (Just valueSyntax)
    Nothing
    Nothing
    signatureSource
    (Just (prepare schema))
    (Just invoke)
    False
    Nothing))
  where
    maximumDepth = fromIntegral (length levels - 1)
    domainExpression = ValuedNaturalRange 0 maximumDepth
    signatureSource = FunctionSource
      (FunctionType domainExpression AnyType)
    innerMap = ContextualMap role levels

    -- The surface spelling has no holes and therefore supplies the empty map.
    -- Contextual depth zero is the function's ordinary default; explicit
    -- @_this n@ and @_it n@ calls overload that default with @n@.
    prepare schema supplied = do
      (depth, bindings) <- overloadArgumentSchemaComplete schema supplied
      pure (PreparedFunctionArgument supplied depth bindings)

    invoke _ reduction prepared = do
      depth <- requireFiniteInteger
        (functionPreparedArgument prepared)
      value <- accessContextualMap reduction depth innerMap
      pure (EvaluatedFunctionInvocation value Nothing)

    valueSyntax :: FunctionSyntax InterpretedValue
    valueSyntax = FunctionSyntax
      [[StringTemplateInterpolation
        (LiteralString (contextualSurfaceName role))]]
contextualFunction role [] = Left
  (UnknownIdentifier (contextualPrivateName role))

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

scopeContextualDeclarationMembers
  :: ContextualRole
  -> Scope
  -> Maybe [ScopedDependentDeclaration]
scopeContextualDeclarationMembers role scope =
  case contextualRuntimeValue role scope of
    Just (_, declarations, _) -> declarations
    Nothing -> Nothing

declarationContextualDeclaration
  :: ContextualRole
  -> [ScopedDependentDeclaration]
  -> RuntimeSingletonPayload
declarationContextualDeclaration role declarations =
  contextualRuntimeDeclaration role False (Just declarations)
    (\resolving reduction ->
      scopeEntriesValue reduction resolving declarations)

scopeEntriesValue
  :: ReductionContext
  -> ResolutionStack
  -> [ScopedDependentDeclaration]
  -> Either InterpretingError InterpretedValue
scopeEntriesValue reduction resolving entries =
  do
    named <- scopeEntriesNamedView reduction resolving entries
    case named of
      Nothing -> Right (makeAtlasMap 0 [])
      Just view -> do
        collection <- coalizeNamedMapView view
        case coalizeNamedOrdinalMapView view of
          Right ordinal -> Right (withCoalizedMapView ordinal collection)
          Left LookupCaptureHasNoGenericMapView {} -> Right collection
          Left failure -> Left failure

scopeEntriesNamedView
  :: ReductionContext
  -> ResolutionStack
  -> [ScopedDependentDeclaration]
  -> Either InterpretingError (Maybe NamedMapView)
scopeEntriesNamedView reduction resolving entries = do
  combined <- foldM appendEntry Nothing entries
  pure (indexedView <$> combined)
  where
    appendEntry accumulated entry = do
      next <- entryView entry
      pure (Just (maybe next (`appendNamedMapViews` next) accumulated))
    entryView = dependentDeclarationNamedView reduction resolving
    layer = dependentDeclarationLayer entries
    indexedView combined = NamedMapView projection
      { namedProjectionMemberByName = memberByName
      , namedProjectionContainsName = containsName
      }
      where
        projection = namedMapProjection combined
    memberByName name = do
      members <- catMaybes <$> traverse
        (\declaration -> dependentDeclarationMemberByName
          reduction resolving declaration name)
        (dependentDeclarationCandidates name layer)
      case members of
        [] -> Right Nothing
        [member] -> Right (Just member)
        _ -> Left (NamedAccessFailed (NamedFieldAmbiguous name))
    containsName name = anyMRight
      (\declaration -> dependentDeclarationContainsName
        reduction resolving declaration name)
      (dependentDeclarationCandidates name layer)

contextualThisAvailable :: Scope -> Bool
contextualThisAvailable scope = case contextualValue ContextualThis scope of
  Just _ -> True
  Nothing -> False

-- A finite access into a productive recursive map only needs finitely many
-- unfoldings. Both comma concatenation and semicolon sequencing delegate back
-- to their ordinary evaluators after the recursive tail has been removed.
lazyRecursivePrefix :: Scope -> Expression -> Maybe (Scope, RecursivePrefix)
lazyRecursivePrefix scope expression = case expression of
  Fun value -> (scope,) <$> recursivePrefixFor
    (isContextualDeclarationReference ContextualThis scope) value
  IdentifierReference (SimpleIdentifierString name) -> do
    (captured, _, definition) <- declarationDefinitionByName scope name
    let isSelf value = value == IdentifierReference (SimpleIdentifierString name)
    prefix <- case definition of
      Fun value -> recursivePrefixFor
        (isContextualAccessOf ContextualThis) value
      value -> recursivePrefixFor isSelf value
    pure (captured, prefix)
  _ -> Nothing

-- Contextual surface names are ordinary singleton declarations. Productive
-- recursion follows their implementations through the declaration environment
-- instead of recognizing a privileged source spelling.
isContextualDeclarationReference
  :: ContextualRole
  -> Scope
  -> Expression
  -> Bool
isContextualDeclarationReference role scope = go []
  where
    go visited expressionValue
      | isContextualAccessOf role expressionValue = True
      | IdentifierReference (SimpleIdentifierString name) <- expressionValue
      , name `notElem` visited
      , Just (_, _, implementation) <- declarationDefinitionByName scope name =
          go (name : visited) implementation
      | otherwise = False

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
  -> ResolutionStack
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
  positions <- traverse selected (naturalsBelow count)
  pure (if null positions then 0 else maximum positions)
  where
    selected position = do
      value <- interpretedMapValueAt (interpretedMap insertion) (finiteOrdinal position)
      (_, ordinal) <- interpretedExplicitOrdinal value
      naturalAtOrdinal ordinal

evalInScope :: Scope -> ResolutionStack -> Interpreter
evalInScope = evalInScopeWith UnrestrictedReduction

scopedLiteralMemberName :: Expression -> Maybe SimpleIdentifierString
scopedLiteralMemberName expressionValue = case expressionValue of
  IdentifierReference name -> Just name
  SyntaxBoundary inner -> scopedLiteralMemberName inner
  _ -> Nothing

-- OBSOLETE normalization seam: evaluation must consume the AST selected by
-- parsing and syntax rewriting without reshaping it here.
evalInScopeWith :: ReductionContext -> Scope -> ResolutionStack -> Interpreter
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
  -> ResolutionStack
  -> Interpreter
evalResourceInScopeWith reduction scope resolving expressionValue =
  case normalizeExpression expressionValue of
    Begin bindings result ->
      evaluateBlockInScope False Nothing reduction scope resolving
        bindings result
    normalized ->
      interpretNormalizedExpressionWith reduction scope resolving normalized

evalInContextualContinuationScopeWith
  :: salt
  -> ReductionContext
  -> [RuntimeSingletonPayload]
  -> Scope
  -> ResolutionStack
  -> Interpreter
evalInContextualContinuationScopeWith
    salt reduction bindings parent resolving expressionValue = do
  let child = extendContextualRuntimeDeclarations bindings
        (enterScope salt genericContinuationHandoff parent)
  value <- evalInScopeWith reduction child resolving expressionValue
  pure (handoffScopeValue child value)

evaluateBlockInScope
  :: Bool
  -> Maybe String
  -> ReductionContext
  -> Scope
  -> ResolutionStack
  -> [DependentDeclaration Expression]
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateBlockInScope introducesThis source reduction scope resolving
    bindings result = do
  innerScope <- (if introducesThis
      then evaluateDeclarationScope
      else evaluateDeclarationScopeWithoutContextualThis)
    scope resolving bindings
  value <- evalInScopeWith reduction innerScope resolving result
  let handed = handoffScopeValue innerScope value
  pure (withEvaluationSource source
    (withoutCanonicalOwners
      (scopePresentationOwners innerScope) handed))

-- PARTIALLY OBSOLETE: this is the central recursive constructor dispatcher,
-- which remains necessary. Its embedded identifier/string interpretation,
-- standard-library spelling checks, scope-opening machinery, and checked
-- operation helpers are mixed responsibilities and should move to focused
-- Evaluation modules that receive 'interpret' explicitly.
interpretNormalizedExpressionWith
  :: ReductionContext
  -> Scope
  -> ResolutionStack
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
    IdentifierExpression body -> interpretIdentifierExpression interpret body
    AtlasMap expressions -> interpretContainer
      (interpretProtectedAtlasMap makeAtlasMap expressions)
      (AtlasMap expressions)
      expressions
    ArgumentativeMap expressions -> interpretContainer
      (interpretProtectedValues expressions makeArgumentativeMapPreservingSingleton)
      (ArgumentativeMap expressions)
      expressions
    MapSequence expressions -> interpretContainer
      (interpretProtectedAtlasMap makeAtlasMap expressions)
      (MapSequence expressions)
      expressions
    SyntaxBoundary inner -> interpret inner
    UnresolvedApplication expressions ->
      interpret (applicationFrom expressions)
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
    AnyType -> Right anyTypeValue
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
    EitherType left right -> binary eitherValue left right
    OptionalType operand ->
      case optionalIdentifierExpression expressionValue of
        Just (present, missing) -> binary eitherValue present missing
        Nothing -> interpret
          (FunctionApplication
            (IdentifierReference (SimpleIdentifierString "Maybe"))
            operand)
    MaybeThen optional branch -> do
      optionalResult <- interpret optional >>= unconsList
      runProtectedOperation protection [optionalResult] $ \actuals ->
        case actuals of
          [actualOptional] ->
            case interpretedSemanticResult actualOptional of
              CanonicalAssignment "Just" _ _ -> do
                result <- evalInContextualContinuationScopeWith branch reduction
                  (constantContextualDeclarations ContextualIt actualOptional)
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
    Equality left right -> checkedBinary equalValues left right
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
    Coalization operand -> unary (Right . coalizeValue) operand
    Fun operand ->
      case recursiveCollection scope operand of
        Just collection -> do
          let element = recursiveCollectionElement collection
          elementType <- interpret element
          runProtectedOperation protection [elementType] $ \actuals ->
            case actuals of
              [actualElement] -> pure $ case collection of
                RecursiveList _ -> listTypeValue
                  (renderSourceExpression expressionValue) actualElement
                RecursiveStream _ -> streamTypeValue
                  (renderSourceExpression expressionValue) actualElement
              _ -> Right neverValue
        Nothing -> recursive reduction
      where
        recursive activeReduction = evalInContextualContinuationScopeWith
          operand activeReduction
          (contextualDeclarations ContextualThis
            (case operand of Begin {} -> True; _ -> False)
            recursive)
          scope resolving operand
    GenericIntroductionExpression introduction ->
      Left (GenericIntroductionOutsideFunctionType
        (case genericArgumentPolarity introduction of
          GenericProduct ->
            AST.operatorPreferredSymbol AST.GenericProductOperator
          GenericSum ->
            AST.operatorPreferredSymbol AST.ExponentiationOperator))
    -- Module identity is presentation metadata, not a scope lookup key.
    -- Retained declarations already carry their lexical scope, so this old
    -- canonical wrapper is semantically transparent.
    InModule _ body -> interpret body
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
            (FunctionSource expressionValue)
            function))
        Nothing -> Left (FunctionEvaluationFailed ExpectedFunctionType)
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
                [actualCallable, actualSupplied] -> do
                  input <- functionArgumentValue actualSupplied
                  applyFunction
                    (scopeActivation scope) reduction actualCallable input
                _ -> Right (neverValue, Nothing)
      case interpret function of
        Left failure -> Left failure
        Right callable -> do
          supplied <- interpret argument
          applyEvaluated callable supplied
    Begin bindings result ->
      evaluateBlockInScope True
        (Just (renderSourceExpression expressionValue))
        reduction scope resolving bindings result
    DeclarationExpression _ -> Left OperationHasNoEffect
    LineBreak -> Left (UnknownIdentifier "\\n")
    UnresolvedSyntaxLiteral literal ->
      Left (UnknownIdentifier (dropWhile isSpace literal))
    IdentifierReference (SimpleIdentifierString name) ->
      resolveIdentifierAccess reduction scope resolving name
    Lookup operand -> do
      query <- interpret operand
      evaluateLookup reduction scope resolving query
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
    ScopedExpression thisValue body
      | Just (SimpleIdentifierString name) <- scopedLiteralMemberName body
      , isContextualAccessOf ContextualThis thisValue
      , contextualThisAvailable scope
          -> resolveIdentifierAccess reduction scope resolving name
    -- @with@ retains every namespace as a separate strict import layer.
    -- Overlap is harmless until a concrete use is accepted by more than one
    -- strict layer.
    WithScopes operands body -> do
      let distinctOperands = nub operands
      sources <- traverse interpret distinctOperands
      runProtectedOperation protection sources $ \actuals -> do
        enterStrictOpenedScopes expressionValue
          (zip distinctOperands actuals) body
    ScopedExpression operand body
      | Just (SimpleIdentifierString name) <- scopedLiteralMemberName body -> do
      source <- interpret operand
      runProtectedOperation protection [source] $ \actuals ->
        case actuals of
          [actual] -> do
            selected <- namedAccessValue actual name
            validateOpenedBinding actual (name, selected)
            payload <- accessValues selected (naturalValue 1)
            if hasTrailingIdentifierMarker canonicalValueMarker selected
              then do
                let dependencies = maybe [] fst
                      (interpretedCanonicalPresentation actual)
                pure (withCanonicalNamedAccess
                  dependencies
                  (interpretedCanonicalResult actual)
                  name
                  payload)
              else pure payload
          _ -> Right neverValue
    ScopedExpression operand body -> do
      source <- interpret operand
      runProtectedOperation protection [source] $ \actuals ->
        case actuals of
          [actual] -> enterOpenedScope expressionValue actual
            [(operand, actual)] body
          _ -> Right neverValue
    MapAccess
        thisValue
        insertionOperand
      | isContextualAccessOf ContextualThis thisValue
      , contextualThisAvailable scope -> do
          insertion <- interpret insertionOperand
          case contextualValue ContextualThis scope of
            Just (_, value) -> do
              contextual <- value resolving reduction
              runProtectedOperation
                protection [contextual, insertion] $ \actuals ->
                  case actuals of
                    [actualContextual, actualInsertion] ->
                      accessValues actualContextual actualInsertion
                    _ -> Right neverValue
            Nothing -> Left
              (UnknownIdentifier (contextualPrivateName ContextualThis))
    MapAccess mapOperand insertionOperand ->
      case lazyRecursivePrefix scope mapOperand of
        Just (captured, prefix) -> do
          insertion <- interpret insertionOperand
          accessRepeatedPrefix captured resolving prefix insertion
        Nothing -> binary accessValues mapOperand insertionOperand
    optionalName
      | Just (present, missing) <-
          optionalIdentifierExpression optionalName ->
            binary eitherValue present missing
    MapSpecification sourceOperand (DependentArgument name Nothing) -> do
      source <- interpret sourceOperand
      runProtectedOperation protection [source] $ \actuals ->
        case actuals of
          [actualSource] -> do
            target <- interpretDependentArgumentName name actualSource
            specifyValues actualSource target
          _ -> Right neverValue
    MapSpecification sourceOperand targetOperand ->
      interpretSpecificationWith protection interpret sourceOperand targetOperand
    DependentArgument _ Nothing -> Left OperationHasNoEffect
    DependentArgument nameExpression (Just typeAnnotationExpression) -> do
      typeAnnotation <- interpret typeAnnotationExpression
      interpretDependentArgumentName nameExpression typeAnnotation

  where
    protection = scopeActivation scope
    interpret = evalInScopeWith reduction scope resolving
    interpretDependentArgumentName nameExpression typeAnnotation =
      case literalIdentifierName nameExpression of
        Just (SimpleIdentifierString identifierString) ->
            interpretSimpleDependentArgument protection
              identifierString typeAnnotation
        Nothing -> case nameExpression of
          IdentifierExpressionBody body ->
            interpretDependentArgumentNameFamily body
      where
        interpretDependentArgumentNameFamily body = do
          let familyKey = renderSourceExpression
                (identifierExpressionExpression nameExpression)
              nameFamily supplied =
                evalInContextualContinuationScopeWith body reduction
                  (constantContextualDeclarations ContextualIt supplied)
                  scope resolving body
          identifier <- nameFamily typeAnnotation
          requireDependentNameSubfederation True interpret identifier
          case asciiStringFromInterpretedMap (interpretedMap identifier) of
            Just identifierString
              | interpretedValueHasTotalMap identifier
              , isIdentifierValue identifierString ->
              interpretSimpleDependentArgument protection
                identifierString typeAnnotation
            _ ->
              Right (dependentArgumentTemplateTypeValue
                familyKey identifier nameFamily typeAnnotation)
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
      if scopeNameIsDefinition scope name
        then do
          let bounded = ShadowingConsistencyReduction
                name shadowingConsistencyFuel
          original <- resolveIdentifierAccess bounded scope resolving name
          replacement <- accessValues selected (naturalValue 1)
          if interpretedSemanticResult original
              == interpretedSemanticResult replacement
            then Right ()
            else Left (InconsistentShadowing name)
        else Right ()
    enterOpenedScope salt actual contributions selectedBody = do
      prepared <- traverse
        (prepareOpenedScopeContribution scope) contributions
      opened <- moduleNamedMembers actual
      mapM_ (validateOpenedBinding actual) opened
      let activated = enterScope salt genericContinuationHandoff scope
          child = foldl
            (flip (installOpenedScopeContribution PreferentialImport))
            activated
            prepared
      value <- evalResourceInScopeWith reduction child resolving selectedBody
      pure (handoffScopeValue child value)
    enterStrictOpenedScopes salt contributions selectedBody = do
      prepared <- traverse
        (prepareOpenedScopeContribution scope) contributions
      let activated = enterScope salt genericContinuationHandoff scope
          child = foldl
            (flip (installOpenedScopeContribution StrictImport))
            activated
            prepared
      value <- evalResourceInScopeWith reduction child resolving selectedBody
      pure (handoffScopeValue child value)
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
      let orderType = interpretedMapFinalOrderType (interpretedMap value)
      if orderType == finiteOrdinal 0
        then standardNothingValue
        else do
          headValue <- accessValues value (naturalValue 0)
          tailRange <- naturalRangeUpwardsValue 1
          tailValue <- accessValues value tailRange
          let pair = makeAtlasMap 2
                (map (coalizeMapMemberAt 2) [headValue, tailValue])
          standardOptionalValue pair >>= contextuallySpecify pair
    standardNothingValue =
      interpret (IdentifierReference (SimpleIdentifierString "nothing"))
    isStandardNothing value = do
      target <- standardNothingValue
      subfederationValues value target >>= booleanCondition
    standardOptionalValue value = do
      constructor <- interpret (IdentifierReference (SimpleIdentifierString "Maybe"))
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
      let signatureSource = FunctionSource written
          prepare argument = do
            (prepared, bindings) <- overloadArgumentSchemaComplete schema argument
            pure (PreparedFunctionArgument argument prepared bindings)
      runProtectedOperation protection [input, output] $ \actuals ->
        case actuals of
          [actualInput, actualOutput] -> pure (makeFunctionValue
            (EvaluatedFunction actualInput actualOutput Nothing Nothing Nothing
              signatureSource (Just prepare) Nothing True Nothing))
          _ -> Right neverValue



genericBinderParts
  :: GenericBinder Expression
  -> (String, Bool, Expression)
genericBinderParts binder =
  ( simpleIdentifierStringText (genericArgumentName argument)
  , genericArgumentOptional argument
  , genericArgumentBound argument
  )
  where
    argument = genericBinderArgument binder

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
        (name, _, _) = genericBinderParts binder

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
    Just (SimpleIdentifierString owner, SimpleIdentifierString referenced) ->
      Left (ForwardGenericBoundReference owner referenced)
    Nothing -> pure ()
  let introduced =
        functionTypeIdentifiers domain <> functionTypeIdentifiers codomain
  mapM_ (validateBinder introduced) generics
  where
    validateBinder introduced binder =
      mapM_ (validateIdentifier name) introduced
      where
        (name, _, _) = genericBinderParts binder
    validateIdentifier genericName introduced =
      case introduced of
        SimpleFunctionTypeIdentifier (SimpleIdentifierString name)
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
      let (name, _, writtenBound) = genericBinderParts binder
          bound = prepareGenericExpression generics writtenBound
          staticBound = substituteDependent prepared bound
      in go ((name, staticBound) : prepared) remaining

substituteDependent :: [(String, Expression)] -> Expression -> Expression
substituteDependent substitutions expressionValue =
  case expressionValue of
    IdentifierReference (SimpleIdentifierString name) ->
      maybe expressionValue id (lookup name substitutions)
    _ -> mapExpressionChildren
      (substituteDependent substitutions)
      expressionValue

domainEntries :: Expression -> [Expression]
domainEntries expressionValue =
  case expressionValue of
    ArgumentativeMap entries -> entries
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
  -> ResolutionStack
  -> [GenericBinder Expression]
  -> Expression
  -> [(String, InterpretedValue)]
  -> Either InterpretingError [RuntimeSingletonPayload]
validateGenericArgumentsExcept
    trusted captured resolving generics domain supplied =
  validateGenerics [] generics
  where
    genericNames =
      [ name | binder <- generics
      , let (name, _, _) = genericBinderParts binder ]
    validateGenerics genericScope [] =
      validateEntries genericScope (domainEntries domain)
    validateGenerics genericScope (binder : remaining) = do
      let (name, _, writtenBound) = genericBinderParts binder
          bound = prepareGenericExpression generics writtenBound
      witness <- maybe (Left (UnknownIdentifier name)) Right
        (lookup name supplied)
      target <- evalInScope
        (extendRuntimeDeclarations genericScope captured) resolving bound
      _ <- if name `elem` trusted
        then Right witness
        else specifyValues witness target
      validateGenerics
        (evaluatedRuntimeDeclaration name witness : genericScope)
        remaining
    validateEntries genericScope [] = Right genericScope
    validateEntries genericScope (entry : remaining) = do
      case entry of
        parameter
          | Just (name, annotation) <- namedDependentArgument parameter
          , name `notElem` genericNames ->
              validateNamed genericScope name annotation
        optional
          | Just (parameter, _) <- optionalIdentifierExpression optional
          , Just (name, annotation) <- namedDependentArgument parameter
          , name `notElem` genericNames ->
              validateNamed genericScope name annotation
        _ -> Right ()
      validateEntries genericScope remaining
    namedDependentArgument value = do
      (nameExpression, annotation, _) <- dependentArgumentExpression value
      effective <- annotation <|> givenValue value
      SimpleIdentifierString name <- literalIdentifierName nameExpression
      pure (name, effective)
      where
        givenValue selected = do
          (_, _, given) <- dependentArgumentExpression selected
          given
    validateNamed genericScope name annotation =
      case lookup name supplied of
        Nothing -> Right ()
        Just value -> do
          target <- evalInScope
            (extendRuntimeDeclarations genericScope captured) resolving annotation
          () <$ specifyValues value target

inferGenericArgument
  :: Scope
  -> ResolutionStack
  -> [GenericBinder Expression]
  -> GenericArgumentBinder
  -> InterpretedValue
  -> [InterpretedValue]
  -> [(GenericArgumentBinder, InterpretedValue)]
  -> Either InterpretingError InterpretedValue
inferGenericArgument captured resolving generics binder _ evidence prior = do
  boundExpression <- maybe
    (Left (UnknownIdentifier name))
    (Right . prepareGenericExpression generics)
    (findBinder (genericArgumentBinderId binder) generics >>= genericBound)
  let currentBindings =
        [ evaluatedRuntimeDeclaration
            (genericArgumentBinderName priorBinder) value
        | (priorBinder, value) <- prior
        ]
  bound <- evalInScope
    (extendRuntimeDeclarations currentBindings captured) resolving boundExpression
  admissible <- keepSuccessful (`specifyValues` bound) evidence
  case admissible of
    [] -> Left (OverloadError OverloadNoMatch)
    first : remaining -> foldM combineInferenceEvidence first remaining
  where
    name = genericArgumentBinderName binder
    genericBound selected =
      let (_, _, bound) = genericBinderParts selected
      in Just bound

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


createFunction :: ReductionContext -> Scope -> ResolutionStack
  -> Expression -> Expression -> Expression
  -> [DependentDeclaration Expression] -> Expression
  -> Either InterpretingError InterpretedValue
createFunction reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result =
  createFunctionWithGenerics reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result []

createFunctionWithGenerics
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> Expression
  -> Expression
  -> Expression
  -> [DependentDeclaration Expression]
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
  -> ResolutionStack
  -> Expression
  -> Expression
  -> Expression
  -> [DependentDeclaration Expression]
  -> Expression
  -> [GenericBinder Expression]
  -> Either InterpretingError InterpretedValue
createFunctionWithEvaluatedTypes evaluatedTypes reduction captured resolving
    signature writtenDomainExpression writtenOutput bindings result
    generics = do
  let (domainExpression, substitutions) =
        staticGenericDomain generics writtenDomainExpression
      specifiedOutput = substituteDependent substitutions writtenOutput
      preparedBindings = map
        (mapDependentDeclaration (prepareGenericExpression generics)) bindings
      preparedResult = prepareGenericExpression generics result
  schema <- case evaluatedTypes of
    Just (input, _) -> pure (argumentSchemaFromValue input)
    Nothing -> compileParametersWithGenerics generics evaluate
      writtenDomainExpression domainExpression
  let inferredGenericNames = argumentSchemaInferredGenericNames schema
  let parameters = parameterBindings schema
      names = map fst parameters
      consistencyScope = extendContextualRuntimeDeclarations
        (constantContextualDeclarations ContextualIt anyTypeValue) captured
  case filter (scopeNameIsDefinition consistencyScope) names of
    name : _ -> Left (InconsistentShadowing name)
    [] -> pure ()
  existingNames <- filterMRight
    (scopeNameExists UnrestrictedReduction captured resolving)
    names
  case [ name
       | name <- names
       , name `elem` existingNames
          || length (filter (== name) names) > 1
       ] of
    name : _ -> Left (OverlappingBindings name)
    [] -> pure ()
  input <- parameterDomain schema
  let (explicitSelf, selfIncludesDependencies) = case
        contextualValue ContextualThis captured of
        Just (includesDependencies, _) -> (True, includesDependencies)
        _ -> (False, False)
  output <- case evaluatedTypes of
    Just (_, preparedOutput) -> pure preparedOutput
    Nothing -> evaluate specifiedOutput
  let prepareWith trusted argument = do
        (prepared, selectedBindings) <-
          overloadArgumentSchemaCompleteWithTrustedGenerics
          (inferGenericArgument captured resolving generics)
          trusted schema argument
        let trustedNames =
              [ name
              | binder <- generics
              , Just _ <- [lookup (genericBinderId binder) trusted]
              , let (name, _, _) = genericBinderParts binder
              ]
        _ <- validateGenericArgumentsExcept
          (trustedNames <> inferredGenericNames)
          captured resolving generics writtenDomainExpression selectedBindings
        supplied <- if argumentSchemaHasInferredGenerics schema
          then argumentSchemaValidationArgument schema prepared
          else Right argument
        pure (PreparedFunctionArgument supplied prepared selectedBindings)
      prepare = prepareWith []
      evaluatePreparedBodyWith bodyResult
          callerActivation invocationReduction preparedCall = do
        let argument = functionPreparedArgument preparedCall
            selectedBindings = functionPreparedBindings preparedCall
            callCaptured = captured
              { scopeActivation = callerActivation
              , scopeHandoff = Nothing
              }
            bodySeed = enterScopeWithReceiver
              preparedCall callerActivation
              genericFunctionReturnHandoff callCaptured
        let genericNames =
              [ name | binder <- generics
              , let (name, _, _) = genericBinderParts binder ]
        dependentScope <- validateGenericArgumentsExcept
          genericNames callCaptured resolving generics
          writtenDomainExpression selectedBindings
        protectedDomain <- prepareProtectedDomain
          bodySeed callCaptured resolving generics
          writtenDomainExpression selectedBindings
        let ordinaryDependentScope =
              [ declaration
              | declaration <- dependentScope
              , runtimeDeclarationName declaration `notElem` genericNames
              ]
            codomainScope = ordinaryDependentScope <>
              [ evaluatedRuntimeDeclaration name value
              | binder <- generics
              , genericArgumentPolarity (genericBinderArgument binder)
                  == GenericProduct
              , let (name, _, _) = genericBinderParts binder
              , Just value <- [lookup name protectedDomain]
              , not (valueIsScopeProtected value)
              ]
            bodyImported =
              [ (name, maybe value id (lookup name protectedDomain))
              | (name, value) <- selectedBindings
              ]
            bodyArgument = protectWithPoliciesOf
              (scopeActivation bodySeed)
              (map snd bodyImported)
              argument
            localDeclarations =
              constantContextualDeclarations ContextualIt bodyArgument
                <> [ evaluatedRuntimeDeclaration name value
                   | (name, value) <- bodyImported
                   ]
            bodyBase =
              extendContextualRuntimeDeclarations localDeclarations bodySeed
        bodyScope <- evaluateDeclarationScopeWithin bodyBase [] preparedBindings
        value <- evalInScopeWith invocationReduction bodyScope [] bodyResult
        let escaped = withoutCanonicalOwners
              ( nub
                  ( scopePresentationOwners bodyScope
                      <> scopePresentationOwners captured)
              )
              value
            codomainEvaluationScope = enterRuntimeScope preparedCall
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
      signatureSource = FunctionSource definition
      signatureText = renderSourceExpression definition
      self = case [BindingDependency name expressionValue
                  | layer <- scopeDependentDeclarationLayers captured
                  , scoped <- dependentDeclarationLayerMembers layer
                  , Just name <- [dependentDeclarationSingletonName scoped]
                  , Just (_, _, expressionValue) <-
                      [scopedDeclarationDefinition scoped]
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
        (EvaluatedFunction input output Nothing
          (Just (FunctionSource closed)) Nothing signatureSource
          (Just prepare) (Just invoke) False Nothing)
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
        | any
            ((== GenericSum)
              . genericArgumentPolarity
              . genericBinderArgument)
            generics =
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
  coalizedMapView <- genericFunctionCoalizedMapView
    captured resolving reduction generics prepareWith invoke
  let projectedFunction = maybe reservedFunction
        (`withCoalizedMapView` reservedFunction) coalizedMapView
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
      let (name, optionalName, _) = genericBinderParts binder
      (witness, rest) <-
        removeFirst ((== Just name) . fst . suppliedArgumentValue) remaining
          <|> if optionalName
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
genericFunctionCoalizedMapView
  :: Scope
  -> ResolutionStack
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
genericFunctionCoalizedMapView
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
      let (_, _, writtenBound) = genericBinderParts binder
          boundExpression = prepareGenericExpression generics writtenBound
          selectedScope =
            [ evaluatedRuntimeDeclaration name witness
            | selectedBinder <- generics
            , let identity = genericBinderId selectedBinder
            , Just witness <- [lookup identity selected]
            , let (name, _, _) = genericBinderParts selectedBinder
            ]
      bound <- evalInScopeWith reduction
        (extendRuntimeDeclarations selectedScope captured) resolving boundExpression
      case namedMapViewForValue bound of
        Just sourceView -> do
          let mappedView =
                mapNamedView selected binder remaining bound sourceView
          projected <- case coalizeNamedOrdinalMapView mappedView of
            Right ordinalView -> Right ordinalView
            Left LookupCaptureHasNoGenericMapView {} ->
              coalizeNamedMapView mappedView
            Left failure -> Left failure
          pure (Just projected)
        Nothing -> case ordinalIndexedValueFamily bound of
          Nothing -> pure Nothing
          Just family -> pure (Just (makeLazyMapValue
            (ordinalIndexedFamilyOrderType family)
            (\position -> do
              witness <- ordinalIndexedFamilyValueAt family position
              either (const Nothing) id
                (build
                  ((genericBinderId binder, witness) : selected)
                  remaining))))

    mapNamedView selected binder remaining bound sourceView =
      NamedMapView (NamedMapProjection
        (mapOrdinalProjection
          <$> namedProjectionCollection sourceProjection)
        (mapOrdinalProjection
          <$> namedProjectionOrdinal sourceProjection)
        (mapMemberByName selected binder remaining bound sourceView)
        (fmap (maybe False (const True))
          . mapMemberByName selected binder remaining bound sourceView)
        (\() -> mapMaybeMembers selected binder remaining bound
          =<< namedProjectionDeclaredMembers sourceProjection ()))
      where
        sourceProjection = namedMapProjection sourceView
        mapOrdinalProjection sourceOrdinal = NamedMapOrdinalProjection
          (namedOrdinalProjectionOrderType sourceOrdinal)
          (\position -> do
            sourceMember <-
              namedOrdinalProjectionMemberAt sourceOrdinal position
            case sourceMember of
              Nothing -> Right Nothing
              Just member -> mapNamedMember
                selected binder remaining bound member)

    mapMemberByName selected binder remaining bound sourceView name = do
      sourceMember <- namedMapMemberByName sourceView name
      case sourceMember of
        Nothing -> Right Nothing
        Just member -> mapNamedMember
          selected binder remaining bound member

    mapMaybeMembers selected binder remaining bound members =
      catMaybes <$> traverse
        (mapNamedMember selected binder remaining bound)
        members

    mapNamedMember selected binder remaining bound member = do
      witness <- case dependentSumElementType bound of
        Just elementType -> specifyDependentSumElement
          (namedMemberValue member) elementType
        Nothing -> Right (namedMemberValue member)
      mapped <- build
          ( (genericBinderId binder, witness)
          : selected
          )
          remaining
      let name = namedMemberName member
      pure (mapped >>= mappedMember name)

    -- The source member's name indexes the mapped family; it is not also the
    -- witness's structural field namespace. Preserve that outer index here
    -- instead of overwriting @_key@ and @_value@ on a specified declaration
    -- entry. An empty body contributes no member to the induced map.
    mappedMember name mapped
      | interpretedMapFinalOrderType (interpretedMap mapped)
          == finiteOrdinal 0 = Nothing
      | otherwise = Just (NamedMember name mapped)

-- | Evaluate each upper bound in telescope order so a generic family can
-- build structural metadata without inventing a concrete witness.  These
-- values are trusted only for the metadata evaluation; ordinary calls still
-- validate concrete witnesses through the regular argument path.
genericUpperBoundWitnesses
  :: Scope
  -> ResolutionStack
  -> ReductionContext
  -> [GenericBinder Expression]
  -> Either InterpretingError [(GenericBinderId, InterpretedValue)]
genericUpperBoundWitnesses captured resolving reduction generics =
  go [] generics
  where
    go selected [] = Right
      [(identity, value) | (identity, _, value) <- reverse selected]
    go selected (binder : remaining) = do
      let (name, _, writtenBound) = genericBinderParts binder
          boundExpression = prepareGenericExpression generics writtenBound
          selectedScope =
            [ evaluatedRuntimeDeclaration selectedName value
            | (_, selectedName, value) <- selected
            ]
      bound <- evalInScopeWith reduction
        (extendRuntimeDeclarations selectedScope captured) resolving boundExpression
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
  in if null sumNames then Nothing else Just transformed
  where
    sumNames =
      [ name
      | binder <- generics
      , genericArgumentPolarity (genericBinderArgument binder) == GenericSum
      , let (name, _, _) = genericBinderParts binder
      ]
    go current =
      case current of
        SuperEllipsisRange lower
            (IdentifierReference (SimpleIdentifierString name))
          | name `elem` sumNames -> SuperEllipsisRangePlus (go lower)
        _ -> mapExpressionChildren go current

prepareProtectedDomain
  :: Scope
  -> Scope
  -> ResolutionStack
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
    domainScope = enterScopeWithReceiver supplied
      (scopeActivation bodyScope)
      genericDomainToBodyHandoff
      parent
    domainActivation = scopeActivation domainScope
    domainLabel = currentScopeLabel domainActivation

    go prepared [] = Right (reverse prepared)
    go prepared (binder : remaining) = do
      let (name, _, writtenBound) = genericBinderParts binder
          boundExpression = prepareGenericExpression generics writtenBound
          dependentScope =
            [ evaluatedRuntimeDeclaration preparedName value
            | (preparedName, value) <- prepared
            ]
      witness <- maybe (Left (UnknownIdentifier name)) Right
        (lookup name supplied)
      target <- evalInScope
        (extendRuntimeDeclarations dependentScope domainScope) resolving boundExpression
      let protectedWitness =
            case genericArgumentPolarity (genericBinderArgument binder) of
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
                (extendRuntimeDeclarations
                  (preparedDeclarations prepared) domainScope)
                resolving
                annotation
              let protected = protectWithPoliciesOf
                    domainActivation [target] value
              pure ((name, protected) : prepared)
        _ -> Right prepared
      protectEntries extended remaining

    namedDomainEntry entry =
      case entry of
        parameter
          | Just named <- namedDependentArgument parameter -> Just named
        optional
          | Just (parameter, _) <- optionalIdentifierExpression optional
          , Just named <- namedDependentArgument parameter -> Just named
        _ -> Nothing

    namedDependentArgument value = do
      (nameExpression, annotation, _) <- dependentArgumentExpression value
      effective <- annotation <|> givenValue value
      SimpleIdentifierString name <- literalIdentifierName nameExpression
      pure (name, effective)
      where
        givenValue selected = do
          (_, _, given) <- dependentArgumentExpression selected
          given

    preparedDeclarations prepared =
      [ evaluatedRuntimeDeclaration name value
      | (name, value) <- prepared
      ]

    genericNames =
      [ name
      | binder <- generics
      , let (name, _, _) = genericBinderParts binder
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

installModuleSource
  :: Scope
  -> Bool
  -> ModuleSource
  -> Either InterpretingError Scope
installModuleSource scope openMembers source = do
  prepared <- prepareModuleWithBase scope source
  installPreparedModule scope openMembers prepared

installPreparedModule
  :: Scope
  -> Bool
  -> PreparedModule
  -> Either InterpretingError Scope
installPreparedModule scope openMembers prepared =
  Right (if openMembers then openNamespaces else qualified)
  where
    namespaceLayer = preparedModuleNamespaces prepared
    qualified = scope
      { scopeDependentDeclarationLayers = namespaceLayer
          : scopeDependentDeclarationLayers scope }
    openNamespaces = foldl openNamespace qualified
      (dependentDeclarationLayerMembers namespaceLayer)
    openNamespace current scoped = case scopedDependentDeclarationRuntime scoped
        >>= runtimeDeclarationPublicScope of
      Nothing -> current
      Just public -> case
          [ layer
          | layer <- scopeDependentDeclarationLayers public
          , dependentDeclarationLayerOrigin layer == SourceDeclarationLayer
          ] of
        layer : _ -> current
          { scopeDependentDeclarationLayers =
              withDeclarationLayerImportPolicy PreferentialImport layer
                : scopeDependentDeclarationLayers current }
        [] -> current

-- An opened namespace either contributes the exact declaration layer retained
-- by its selected value or, for an ordinary runtime map, its native named-map
-- projection.  In particular, this boundary never inspects whether the source
-- expression is a simple identifier: aliases and dependent declaration
-- applications follow the same provenance lookup.
data OpenedScopeContribution
  = OpenedDeclarationLayer DependentDeclarationLayer
  | OpenedRuntimeScope
      [RuntimeSingletonPayload]
      (Maybe NamedMapView)

prepareOpenedScopeContribution
  :: Scope
  -> (Expression, InterpretedValue)
  -> Either InterpretingError OpenedScopeContribution
prepareOpenedScopeContribution scope (_, actual) =
  case runtimePublicScopeForValue actual scope >>= publicDeclarationLayer of
    Just layer -> Right (OpenedDeclarationLayer layer)
    Nothing -> case namedMapViewForValue actual of
      Just projection -> Right (OpenedRuntimeScope [] (Just projection))
      Nothing -> do
        members <- namedMembers actual
        declarations <- traverse openedDeclaration members
        Right (OpenedRuntimeScope declarations Nothing)
  where
    openedDeclaration (name, selected) = do
      payload <- moduleMemberPayload selected
      pure ((evaluatedRuntimeDeclaration name payload)
        { runtimeDeclarationIsDefinition =
            hasTrailingIdentifierMarker definitionMarker selected
        })

publicDeclarationLayer :: Scope -> Maybe DependentDeclarationLayer
publicDeclarationLayer public = case
    [ layer
    | layer <- scopeDependentDeclarationLayers public
    , dependentDeclarationLayerOrigin layer == SourceDeclarationLayer
    ] of
  layer : _ -> Just layer
  [] -> Nothing

installOpenedScopeContribution
  :: DeclarationLayerImportPolicy
  -> OpenedScopeContribution
  -> Scope
  -> Scope
installOpenedScopeContribution policy contribution = case contribution of
  OpenedDeclarationLayer layer -> extendImportedDeclarationLayer policy layer
  OpenedRuntimeScope declarations projection ->
    extendImportedRuntimeScope policy declarations projection

prepareModuleWithBase
  :: Scope
  -> ModuleSource
  -> Either InterpretingError PreparedModule
prepareModuleWithBase base
    moduleSource@(ModuleSource path expression) = do
  prepared <- moduleBaseScope base moduleSource
  (resourceBase, resource) <- prepareModuleResource prepared expression
  (resourceDeclarations, resultExpression) <- resourceBlock resource
  outer <- evaluateDeclarationScopeWithoutContextualThis
    resourceBase [] resourceDeclarations
  result <- evalInScope outer [] resultExpression
  exported <- case moduleExportMembers result of
    Right members@(_ : _) -> Right members
    _ | interpretedValueKind result == DependentArgumentTypeValueKind ->
      Right []
    Right [] -> Left (ModuleEvaluationFailed
      ModuleRequiresIdentifierBinderFederation)
    Left _ -> Left (ModuleEvaluationFailed
      ModuleRequiresIdentifierBinderFederation)
  declarations <- concat <$> traverse
    (preparedDeclarations outer resourceDeclarations) exported
  pure PreparedModule
    { preparedModuleIdentity = path
    , preparedModuleNamespaces = dependentDeclarationLayer declarations
    }
  where
    preparedDeclarations outer declarations exported@(ModuleExport name _ _ _) =
      traverse (attachRuntime outer exported)
        [ scoped
        | layer <- scopeDependentDeclarationLayers outer
        , scoped <- dependentDeclarationLayerMembers layer
        , Just declaration <- [scopedDependentDeclarationValue scoped]
        , declaration `elem` declarations
        , either (const False) id
            (dependentDeclarationContainsName
              UnrestrictedReduction [] scoped name)
        ]
    attachRuntime outer (ModuleExport name presentation isDefinition value)
        scoped = do
      public <- declarationPublicScope outer scoped
      let dependency = ModulePresentationOwner path
          runtime = RuntimeSingletonPayload
            { runtimeDeclarationName = name
            , runtimeDeclarationIsDefinition = isDefinition
            , runtimeDeclarationValue = EvaluatedRuntimeValue
                (handoffScopeValue outer value)
            , runtimeDeclarationPresentation = case presentation of
                CanonicalModuleMemberPresentation ->
                  ReferencedRuntimePresentation [dependency]
                TransparentModuleMemberPresentation ->
                  TransparentRuntimePresentation
            , runtimeDeclarationOrigin = Just
                (DependencyAddress [SimpleIdentifierString name])
            , runtimeDeclarationDefinition = scopedDeclarationDefinition scoped
            , runtimeDeclarationPublicScope = Just public
            , runtimeDeclarationReevaluatesForRestrictedReduction = False
            }
      pure (attachRuntimePayload runtime scoped)

attachRuntimePayload
  :: RuntimeSingletonPayload
  -> ScopedDependentDeclaration
  -> ScopedDependentDeclaration
attachRuntimePayload runtime scoped = case scoped of
  ScopedDatraDependentDeclaration captured family declaration _ ->
    ScopedDatraDependentDeclaration captured family declaration (Just runtime)
  _ -> scoped

declarationPublicScope
  :: Scope
  -> ScopedDependentDeclaration
  -> Either InterpretingError Scope
declarationPublicScope outer scoped =
  case scopedDependentDeclarationValue scoped of
    Just declaration -> case dependentDeclarationImplementation declaration of
      Begin declarations _ -> evaluateDeclarationScope outer [] declarations
      SyntaxBoundary inner -> publicFrom inner
      _ -> Right outer
    Nothing -> Right outer
  where
    publicFrom expressionValue = case expressionValue of
      Begin declarations _ -> evaluateDeclarationScope outer [] declarations
      SyntaxBoundary inner -> publicFrom inner
      _ -> Right outer

moduleBaseScope
  :: Scope
  -> ModuleSource
  -> Either InterpretingError Scope
moduleBaseScope base
    (ModuleSource path _) = do
  let seeded = withPresentationOwner
        (ModulePresentationOwner path)
        base
  if takeFileName path == standardLibraryFileName
    then installDatraHost seeded
    else standardLibraryModuleSource >>= installModuleSource seeded False

-- Resource-level scope access and import wrap the declarations which produce
-- a module value. Prepare those lexical scopes once so value evaluation and
-- retained export definitions close over precisely the same bindings.
prepareModuleResource
  :: Scope
  -> Expression
  -> Either InterpretingError (Scope, Expression)
prepareModuleResource base expressionValue = case expressionValue of
  SyntaxBoundary body -> prepareModuleResource base body
  ScopedExpression source body -> do
    value <- evalInScope base [] source
    contribution <- prepareOpenedScopeContribution base (source, value)
    prepareModuleResource
      (installOpenedScopeContribution PreferentialImport contribution base)
      body
  WithScopes sources body -> do
    let distinctSources = nub sources
    values <- traverse (evalInScope base []) distinctSources
    contributions <- traverse
      (prepareOpenedScopeContribution base)
      (zip distinctSources values)
    prepareModuleResource
      (foldl
        (flip (installOpenedScopeContribution StrictImport))
        base
        contributions)
      body
  _ -> Right (base, expressionValue)

moduleExportNames :: ModuleSource -> Either InterpretingError [String]
moduleExportNames source = do
  prepared <- prepareModuleWithBase (rootScope source) source
  concat <$> traverse declarationExports
    (dependentDeclarationLayerMembers (preparedModuleNamespaces prepared))
  where
    declarationExports scoped = case scopedDependentDeclarationRuntime scoped of
      Just runtime -> case runtimeDeclarationValue runtime of
        EvaluatedRuntimeValue value ->
          map moduleExportName <$> moduleExportsFromValue value
        ContextualRuntimeValue {} -> Right []
      Nothing -> Right []

moduleExportsFromValue
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
moduleExportsFromValue value =
  case moduleNamedMembers value >>= traverse namedMemberPayload of
    Right exports -> Right exports
    Left failure@(ModuleEvaluationFailed reason) ->
      case reason of
        ModuleRequiresNamedExports -> invalid
        ModuleExportRequiresIdentifier -> invalid
        _ -> Left failure
    Left failure -> Left failure
  where
    invalid = Left (ModuleEvaluationFailed
      ModuleScopeRequiresTotalMapOfSimpleIdentifierTypes)

-- Module consumers first use the collection projection when it is finite.
-- A transfinite namespace still has a finite manifest of declaration-family
-- descriptors, exposed by the same named-map view without enumerating its
-- concrete member order. Syntax discovery and lexical opening must share this
-- boundary so neither path materializes a Stream.
moduleNamedMembers
  :: InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
moduleNamedMembers value =
  case namedMembers value of
    Right members -> Right members
    Left (ModuleEvaluationFailed ModuleRequiresNamedExports) ->
      case namedMapViewForValue value of
        Just view -> map namedMemberPair <$> namedMapDeclaredMembers view
        Nothing -> Right []
    Left failure -> Left failure
  where
    namedMemberPair member =
      (namedMemberName member, namedMemberValue member)

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
    Nothing -> case argumentativeMapMembers value of
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
      ModuleRequiresNamedExports)
    memberAt position = maybe invalid Right
      (interpretedMapValueAt (interpretedMap value) position)
    field member = case simpleIdentifierName member of
      Just name -> Right (name, member)
      Nothing -> Left (ModuleEvaluationFailed ModuleExportRequiresIdentifier)

-- A module may yield a federation that mixes ordinary named binders
-- with dependent argument binders.  The dependent fibers remain in the
-- complete federation used as the synthesized function domain; this view is
-- only for installing the ordinary names as qualified declarations.
moduleExportMembers
  :: InterpretedValue
  -> Either InterpretingError [ModuleExport]
moduleExportMembers value =
  case namedMembers value of
    Right members -> traverse namedMemberPayload members
    Left _ -> mixedMembers
  where
    mixedMembers = do
      members <- case argumentativeMapMembers value of
        Just arguments -> Right arguments
        Nothing -> do
          count <- maybe invalid Right
            (naturalAtOrdinal
              (interpretedMapFinalOrderType (interpretedMap value)))
          traverse memberAt (naturalsBelow count)
      catMaybes <$> traverse export members
    invalid = Left (ModuleEvaluationFailed
      ModuleRequiresIdentifierBinderFederation)
    memberAt index = maybe invalid Right
      (interpretedMapValueAt (interpretedMap value) (finiteOrdinal index))
    export member = case simpleIdentifierName member of
      Just name -> Just <$> namedMemberPayload (name, member)
      Nothing
        | interpretedValueKind member == DependentArgumentTypeValueKind ->
            Right Nothing
        | otherwise -> invalid

namedMemberPayload
  :: (String, InterpretedValue)
  -> Either InterpretingError ModuleExport
namedMemberPayload (name, selected) = do
  payload <- moduleMemberPayload selected
  pure (ModuleExport
    name
    (if hasTrailingIdentifierMarker canonicalValueMarker selected
      then CanonicalModuleMemberPresentation
      else TransparentModuleMemberPresentation)
    (hasTrailingIdentifierMarker definitionMarker selected)
    payload)

-- A module member remains a named declaration descriptor in its enclosing
-- federation. Consumers project its evaluated payload through the ordinary
-- map-access operation, so opening a scope, installing a declaration, and reading
-- syntax metadata all observe the same already-evaluated declaration value.
moduleMemberPayload
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
moduleMemberPayload selected = accessValues selected (naturalValue 1)

resourceBlock
  :: Expression
  -> Either InterpretingError
      ([DependentDeclaration Expression], Expression)
resourceBlock (Begin bindings result) = Right (bindings, result)
resourceBlock _ = Left (ModuleEvaluationFailed ModuleRequiresBlock)

-- PARTIALLY OBSOLETE: dependency traversal is valid, but selected runtime
-- values are still converted back into ASTs through
-- 'obsoleteValueExpressionIn'. Removing that conversion should leave only the
-- source-definition traversal in this resolver.

evaluateLookup
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
evaluateLookup reduction scope resolving query =
  case interpretedSemanticResult query of
    CanonicalAsciiString key ->
      do
        exists <- scopeNameExists reduction scope resolving key
        lookupResult reduction scope resolving [key | exists]
    _ -> case interpretedStringTemplate query of
      Just template -> do
        family <- compileLookupCaptureFamily template
        keys <- filterMRight
          (matchCanonicalTemplate template)
          (scopeLookupKeys scope)
        lookupTemplateResult reduction scope resolving template family keys
      Nothing -> Left (LookupRequiresString (interpretedValueKind query))

lookupResult
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> [String]
  -> Either InterpretingError InterpretedValue
lookupResult reduction scope resolving keys =
  Right (makeCheckedLazyMapValue
    (finiteOrdinal (fromIntegral (length keys)))
    (\position -> case naturalAtOrdinal position of
      Just index -> case valueAt index keys of
        Just key -> Just <$> lookupRow reduction scope resolving key
        Nothing -> Right Nothing
      Nothing -> Right Nothing))
  where
    valueAt 0 (value : _) = Just value
    valueAt index (_ : remaining) = valueAt (index - 1) remaining
    valueAt _ [] = Nothing

lookupTemplateResult
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> EvaluatedStringTemplate
  -> OrdinalIndexedFamily
  -> [String]
  -> Either InterpretingError InterpretedValue
lookupTemplateResult reduction scope resolving template family keys =
  Right (makeCheckedLazyMapValue
    (finiteOrdinal (fromIntegral (length keys)))
    (rowAt . naturalAtOrdinal))
  where
    traversal = foliageMap (ordinalIndexedFamilyOrderType family)

    rowAt Nothing = Right Nothing
    rowAt (Just requested) = seek 0 0 []
      where
        seek rank emitted emittedKeys = do
          sourcePosition <- maybe
            (Left AmbiguousStringTemplate)
            Right
            (foliageMapPositionAt traversal rank)
          witness <- maybe
            (Left AmbiguousStringTemplate)
            Right
            (ordinalIndexedFamilyValueAt family sourcePosition)
          key <- renderLookupTemplateKey template witness
          if key `elem` keys && key `notElem` emittedKeys
            then if emitted == requested
              then Just <$> lookupRow reduction scope resolving key
              else seek (rank + 1) (emitted + 1) (key : emittedKeys)
            else seek (rank + 1) emitted emittedKeys

lookupRow
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> Either InterpretingError InterpretedValue
lookupRow reduction scope resolving key = do
  resolved <- resolveIdentifierAccess reduction scope resolving key
  lookupRowValue key resolved

lookupRowValue
  :: String
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
lookupRowValue key resolved = do
  keyValue <- asciiStringValue key
  pure (makeAtlasMapPreservingSingleton 2
    [ simpleIdentifierTypeValue
        (simpleIdentifierStringText lookupKeyFieldName) keyValue
    , simpleIdentifierTypeValue
        (simpleIdentifierStringText lookupValueFieldName) resolved
    ])

compileLookupCaptureFamily
  :: EvaluatedStringTemplate
  -> Either InterpretingError OrdinalIndexedFamily
compileLookupCaptureFamily template =
  case captures of
    [] -> Left AmbiguousStringTemplate
    _ -> case ordinalIndexedValueFamily
        (makeAtlasMap 2 (map captureBound captures)) of
      Just family -> Right family
      Nothing ->
        case [capture | capture <- captures
              , Nothing <- [ordinalIndexedValueFamily
                  (captureBound capture)]] of
          capture : _ -> Left (LookupCaptureHasNoGenericMapView
            (captureIndex capture)
            (renderInterpretedValue (captureSchema capture)))
          [] -> Left (LookupCaptureHasNoGenericMapView
            0 (renderInterpretedValue
              (makeAtlasMap 2 (map captureBound captures))))
  where
    captures = templateCaptures template

templateCaptures :: EvaluatedStringTemplate -> [LookupCapture]
templateCaptures template =
  [ LookupCapture index schema bound
  | EvaluatedStringTemplateCapture index schema bound <-
      evaluatedStringTemplateSegments template
  ]

renderLookupTemplateKey
  :: EvaluatedStringTemplate
  -> InterpretedValue
  -> Either InterpretingError String
renderLookupTemplateKey template witness = do
  witnesses <- captureWitnesses (length captures) witness
  concat <$> traverse (renderSegment witnesses)
    (evaluatedStringTemplateSegments template)
  where
    captures = templateCaptures template
    renderSegment _ (EvaluatedStringTemplateLiteral literal) = Right literal
    renderSegment witnesses
        (EvaluatedStringTemplateCapture index _ _) = do
      selected <- maybe
        (Left AmbiguousStringTemplate)
        Right
        (naturalListAt index witnesses)
      maybe (Left AmbiguousStringTemplate) Right
        (canonicalCaptureText selected)

-- | Render the single declaration-family row used for syntax discovery and
-- non-canonical collection traversal. Capture schemas describe the family;
-- concrete canonical declarations are produced separately from capture
-- witnesses in foliage order.
renderDeclarationDescriptorKey :: EvaluatedStringTemplate -> String
renderDeclarationDescriptorKey = concatMap renderSegment
  . evaluatedStringTemplateSegments
  where
    renderSegment (EvaluatedStringTemplateLiteral literal) = literal
    renderSegment (EvaluatedStringTemplateCapture _ schema _) =
      renderInterpretedValue schema

captureWitnesses
  :: Int
  -> InterpretedValue
  -> Either InterpretingError [InterpretedValue]
captureWitnesses 1 witness = Right [witness]
captureWitnesses count witness =
  traverse member [0 .. count - 1]
  where
    member index = maybe
      (Left AmbiguousStringTemplate)
      Right
      (interpretedMapValueAt
        (interpretedMap witness)
        (finiteOrdinal (fromIntegral index)))

-- Capture families are enumerated before their keys are rendered, so this
-- conversion is only for one concrete witness. A non-concrete conversion is
-- not an exceptional host state; it simply cannot name a declaration member.
canonicalCaptureText :: InterpretedValue -> Maybe String
canonicalCaptureText value = do
  rendered <- either (const Nothing) Just
    (toStringValue canonicalStringCodec value)
  case interpretedSemanticResult rendered of
    CanonicalAsciiString text -> Just text
    _ -> case asciiStringFromInterpretedMap (interpretedMap rendered) of
      Just text | interpretedValueHasTotalMap rendered -> Just text
      _ -> Nothing

-- | Canonical reverse matching mirrors function-domain preparation. The
-- existing pointwise string specification recovers the selected member of
-- the capture schema; identifiers are then erased to positional payloads, and
-- the payload must render byte-for-byte to the captured substring.
matchCanonicalTemplate
  :: EvaluatedStringTemplate
  -> String
  -> Either InterpretingError Bool
matchCanonicalTemplate template input =
  maybe False (const True) <$>
    decodeCanonicalTemplate template input

decodeCanonicalTemplate
  :: EvaluatedStringTemplate
  -> String
  -> Either InterpretingError (Maybe [InterpretedValue])
decodeCanonicalTemplate template input = do
  matches <- matchExactSegments view preparedCaptureCandidates
    (evaluatedStringTemplateSegments template) input
  let distinct = nubBy samePrepared matches
  case distinct of
    [] -> Right Nothing
    [matched] -> Right (Just matched)
    _ -> Left AmbiguousStringTemplate
  where
    samePrepared left right =
      map interpretedSemanticResult left == map interpretedSemanticResult right
    view segment = case segment of
      EvaluatedStringTemplateLiteral literal -> Right literal
      EvaluatedStringTemplateCapture _ schema _ -> Left schema

preparedCaptureCandidates
  :: InterpretedValue
  -> String
  -> Either InterpretingError [InterpretedValue]
preparedCaptureCandidates schema captured = do
  source <- asciiStringValue captured
  pure $ case evalValues canonicalStringCodec source schema of
    Left _ -> []
    Right selected ->
      [ prepared
      | Right prepared <-
          [argumentSchemaValuesComplete
            (argumentSchemaFromValue schema)
            selected]
      , Just rendered <- [canonicalCaptureText prepared]
      , rendered == captured
      ]

naturalListAt :: Natural -> [value] -> Maybe value
naturalListAt 0 (value : _) = Just value
naturalListAt index (_ : remaining) = naturalListAt (index - 1) remaining
naturalListAt _ [] = Nothing

anyMRight
  :: (value -> Either error Bool)
  -> [value]
  -> Either error Bool
anyMRight _ [] = Right False
anyMRight predicate (value : remaining) = do
  accepted <- predicate value
  if accepted then Right True else anyMRight predicate remaining

filterMRight
  :: (value -> Either error Bool)
  -> [value]
  -> Either error [value]
filterMRight predicate = retain
  where
    retain [] = Right []
    retain (value : remaining) = do
      accepted <- predicate value
      retained <- retain remaining
      pure (if accepted then value : retained else retained)

scopeLookupKeys :: Scope -> [String]
scopeLookupKeys scope = stableUnique
  [ name
  | layer <- scopeDependentDeclarationLayers scope
  , scoped <- dependentDeclarationLayerMembers layer
  , Just name <- [dependentDeclarationSingletonName scoped]
  ]
  where
    stableUnique = go Set.empty
    go _ [] = []
    go seen (name : remaining)
      | Set.member name seen = go seen remaining
      | otherwise = name : go (Set.insert name seen) remaining

scopeNameExists
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> Either InterpretingError Bool
scopeNameExists reduction scope resolving name
  = declarationLayerContains (scopeDependentDeclarationLayers scope)
  where
    declarationLayerContains [] = Right False
    declarationLayerContains (layer : outer) = do
      found <- anyMRight
        (\declaration -> dependentDeclarationContainsName
          reduction resolving declaration name)
        (dependentDeclarationCandidates name layer)
      if found then Right True else declarationLayerContains outer

resolveIdentifier
  :: Scope -> ResolutionStack -> String -> Either InterpretingError InterpretedValue
resolveIdentifier = resolveIdentifierAccess UnrestrictedReduction

resolveIdentifierAccess
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> Either InterpretingError InterpretedValue
resolveIdentifierAccess reduction scope resolving name =
  do
    member <- firstDeclarationLayer
      (scopeDependentDeclarationLayers scope)
    case member of
      Just selected -> Right (resolvedNamedMemberValue selected)
      Nothing -> Left (UnknownIdentifier name)
  where
    firstDeclarationLayer [] = Right Nothing
    firstDeclarationLayer (layer : outer) = do
      member <- memberInLayer layer
      case member of
        Nothing -> firstDeclarationLayer outer
        Just selected ->
          case dependentDeclarationLayerImportPolicy layer of
            LocalDeclarationLayer -> Right (Just selected)
            PreferentialImport -> Right (Just selected)
            StrictImport -> do
              peer <- firstStrictMember outer
              case peer of
                Nothing -> Right (Just selected)
                Just _ -> Left (AmbiguousStrictImport name)
    firstStrictMember [] = Right Nothing
    firstStrictMember (layer : outer) =
      case dependentDeclarationLayerImportPolicy layer of
        StrictImport -> do
          member <- memberInLayer layer
          case member of
            Nothing -> firstStrictMember outer
            Just selected -> Right (Just selected)
        LocalDeclarationLayer -> firstStrictMember outer
        PreferentialImport -> firstStrictMember outer
    memberInLayer layer = do
      members <- catMaybes <$> traverse
        (\declaration -> dependentDeclarationMemberByName
          reduction resolving declaration name)
        (dependentDeclarationCandidates name layer)
      case members of
        [] -> Right Nothing
        [member] -> Right (Just member)
        _ -> Left (NamedAccessFailed (NamedFieldAmbiguous name))

resolvedNamedMemberValue :: NamedMember -> InterpretedValue
resolvedNamedMemberValue member =
  case identifierUnderlyingValue selected of
    Just underlying
      | hasTrailingIdentifierMarker canonicalValueMarker selected ->
          withCanonicalReference [] (namedMemberName member) underlying
      | otherwise -> underlying
    Nothing -> selected
  where
    selected = namedMemberValue member

evaluateDeclarationDefinitionWith
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> Maybe Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateDeclarationDefinitionWith reduction captured resolving name annotation expressionValue =
  evaluateDeferredDeclarationWith
    reduction captured resolving name expressionValue Right $ \activeResolving ->
      evaluateDeclarationDefinitionActive reduction captured activeResolving
        annotation expressionValue

evaluateDeferredDeclarationWith
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> Expression
  -> (InterpretedValue -> Either InterpretingError result)
  -> (ResolutionStack -> Either InterpretingError result)
  -> Either InterpretingError result
evaluateDeferredDeclarationWith reduction captured resolving name expressionValue
    seedResult evaluate
  | resolutionKey `elem` resolving
  , Just implementation <- recursiveFunctionImplementation expressionValue = do
      seed <- evalInScopeWith reduction captured resolving implementation
      seedResult (case interpretedFunctionBody seed of
        Just (EvaluatedRuntimeFunctionBody _ function) ->
          makeFunctionValue function
        _ -> seed)
  | otherwise = evaluate (resolutionKey : resolving)
  where
    resolutionKey = ResolutionKey name expressionValue

evaluateDeclarationDefinitionActive
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> Maybe Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
evaluateDeclarationDefinitionActive reduction captured activeResolving
    annotation expressionValue = do
  case annotation of
    Nothing -> pure ()
    Just typeExpression ->
      () <$ evalInScopeWith reduction captured activeResolving typeExpression
  resolveInferredEitherAlias annotation <$> evaluateDefinition
  where
    evaluateDefinition =
      case expressionValue of
        contextual
          | isContextualAccessOf ContextualThis contextual
          , Just (_, value) <- contextualValue ContextualThis captured ->
              value activeResolving reduction
        IdentifierReference reference
          | Just role <- contextualRoleForIdentifier reference
          , Just (_, value) <- contextualValue role captured ->
              value activeResolving reduction
        _ -> evalInScopeWith reduction captured
          activeResolving expressionValue

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
  case attachedFunctionImplementation expressionValue of
    Just implementation
      | not (sourceFunctionBody implementation) ->
      Just implementation
    _ -> case expressionValue of
      Begin _ result -> recursiveFunctionImplementation result
      DeclarationExpression declaration -> recursiveFunctionImplementation
        (dependentDeclarationImplementation declaration)
      EitherType left right ->
        case recursiveFunctionImplementation left of
          Just implementation -> Just implementation
          Nothing -> recursiveFunctionImplementation right
      OptionalType operand -> recursiveFunctionImplementation operand
      _ -> Nothing
  where
    sourceFunctionBody FunctionBody {} = True
    sourceFunctionBody _ = False

-- A block installs declarations from left to right. Ordinary definitions capture
-- only earlier ordinary definitions, while every let definition is predeclared
-- throughout the block. Lets are forced before yield and their results replace
-- the deferred definitions. Names are checked before evaluating any binding.
evaluateDeclarationScope
  :: Scope
  -> ResolutionStack
  -> [DependentDeclaration Expression]
  -> Either InterpretingError Scope
evaluateDeclarationScope = evaluateDeclarationScopeUsing
  (obsoleteScopeRebuilderWithContextualThisAndValidation False True)

evaluateDeclarationScopeWithoutContextualThis
  :: Scope
  -> ResolutionStack
  -> [DependentDeclaration Expression]
  -> Either InterpretingError Scope
evaluateDeclarationScopeWithoutContextualThis =
  evaluateDeclarationScopeUsing
    (obsoleteScopeRebuilderWithContextualThisAndValidation False False)

evaluateDeclarationScopeWithin
  :: Scope
  -> ResolutionStack
  -> [DependentDeclaration Expression]
  -> Either InterpretingError Scope
evaluateDeclarationScopeWithin = evaluateDeclarationScopeUsing obsoleteScopeRebuilderWithin

evaluateDeclarationScopeUsing
  :: (Scope -> [DependentDeclaration Expression] -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [ScopedDependentDeclaration]
      , ResolutionStack -> Scope -> Either InterpretingError ()
      ))
  -> Scope
  -> ResolutionStack
  -> [DependentDeclaration Expression]
  -> Either InterpretingError Scope
evaluateDeclarationScopeUsing build enclosing resolving entries = do
  (rebuild, eagerFamilies, validateConsistency) <-
    build enclosing entries
  let forced =
        [ (name, scoped)
        | scoped <- eagerFamilies
        , Just name <- [dependentDeclarationSingletonName scoped]
        , not (productiveRecursiveDeclaration name scoped)
        ]
      (seeded, ordinary) = partition
        (dependentDeclarationHasRecursiveSeed . snd) forced
      retainLet retained (name, _) = do
        value <- resolveIdentifier (rebuild retained) resolving name
        pure ((name, value) : retained)
  retained <- foldM retainLet [] (seeded <> ordinary)
  let evaluated = rebuild retained
  validateConsistency resolving evaluated
  pure evaluated

dependentDeclarationHasRecursiveSeed
  :: ScopedDependentDeclaration
  -> Bool
dependentDeclarationHasRecursiveSeed scoped =
  case scopedDependentDeclarationValue scoped >>=
      recursiveFunctionImplementation . dependentDeclarationImplementation of
    Just _ -> True
    Nothing -> False

productiveRecursiveDeclaration
  :: String
  -> ScopedDependentDeclaration
  -> Bool
productiveRecursiveDeclaration name scoped =
  case scopedDependentDeclarationValue scoped >>= recursivePrefixFor
      (== IdentifierReference (SimpleIdentifierString name))
      . dependentDeclarationImplementation of
    Just _ -> True
    Nothing -> False

scopePresentationOwners :: Scope -> [PresentationOwner]
scopePresentationOwners = maybe [] pure . scopePresentationOwner

childPresentationOwner
  :: Scope
  -> [DependentDeclaration Expression]
  -> PresentationOwner
childPresentationOwner enclosing =
  LexicalPresentationOwner (scopePresentationOwner enclosing)

-- OBSOLETE: rebuild a declaration scope from its finite source declarations
-- whenever an
-- eager let becomes available.  Recursive lets make their captured scopes
-- cyclic; recursively walking those scopes to replace a binding can therefore
-- black-hole. Rebuilding ties one fresh, shared knot and places retained
-- values into every lexical snapshot without traversing it.
obsoleteScopeRebuilderWithContextualThisAndValidation
  :: Bool
  -> Bool
  -> Scope
  -> [DependentDeclaration Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [ScopedDependentDeclaration]
      , ResolutionStack -> Scope -> Either InterpretingError ()
      )
obsoleteScopeRebuilderWithContextualThisAndValidation
    validateFamilies introducesThis enclosing entries = do
  let owner = childPresentationOwner enclosing entries
      scopedEnclosing = withPresentationOwner owner
        (enterScope entries genericContinuationHandoff enclosing)
  obsoleteScopeRebuilderActivated validateFamilies introducesThis scopedEnclosing entries

obsoleteScopeRebuilderWithin
  :: Scope
  -> [DependentDeclaration Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [ScopedDependentDeclaration]
      , ResolutionStack -> Scope -> Either InterpretingError ()
      )
obsoleteScopeRebuilderWithin enclosing entries =
  let owner = childPresentationOwner enclosing entries
      scopedEnclosing = withPresentationOwner owner enclosing
  in obsoleteScopeRebuilderActivated True True scopedEnclosing entries

obsoleteScopeRebuilderActivated
  :: Bool
  -> Bool
  -> Scope
  -> [DependentDeclaration Expression]
  -> Either InterpretingError
      ( [(String, InterpretedValue)] -> Scope
      , [ScopedDependentDeclaration]
      , ResolutionStack -> Scope -> Either InterpretingError ()
      )
obsoleteScopeRebuilderActivated validateFamilies introducesThis scopedEnclosing entries = do
  let positionedMembers = zip [0 :: Int ..] entries
      finalPosition = length entries
      scopedMembersLayer = dependentDeclarationLayer scopedMembers
      -- Every declaration scope contributes its own contextual level.  An
      -- inherited @_this@ is the next outer level, not evidence that this
      -- block has already installed its local one.
      introduceThis = introducesThis
      buildFrame retained =
        (scopeAt finalPosition, positionedScopeMembers)
        where
          positionedScopeMembers =
            [ makeScoped position declaration
            | (position, declaration) <- positionedMembers
            ]

          makeScoped position declaration =
            ScopedDatraDependentDeclaration
              captured familyCaptured declaration retainedRuntime
            where
              captured = scopeAt position
              familyCaptured = familyScopeAt position
              retainedRuntime = do
                name <- literalIdentifierName
                  (dependentDeclarationHead declaration)
                  >>= pure . simpleIdentifierStringText
                value <- lookup name retained
                pure RuntimeSingletonPayload
                  { runtimeDeclarationName = name
                  , runtimeDeclarationIsDefinition =
                      dependentDeclarationIsDefinition declaration
                  , runtimeDeclarationValue = EvaluatedRuntimeValue value
                  , runtimeDeclarationPresentation = DirectRuntimePresentation
                  , runtimeDeclarationOrigin = Nothing
                  , runtimeDeclarationDefinition = Just
                      ( captured
                      , Nothing
                      , dependentDeclarationImplementation declaration
                      )
                  , runtimeDeclarationPublicScope = Nothing
                  , runtimeDeclarationReevaluatesForRestrictedReduction = True
                  }

          scopeAt position = scopeAtWith position
          familyScopeAt position = scopeAtWith position
          scopeAtWith position =
            extendContextualRuntimeDeclarations runtimeDeclarations namedScope
            where
              visible =
                [ scoped
                | ((declaredAt, declaration), scoped) <-
                    zip positionedMembers positionedScopeMembers
                , declaredAt < position
                    || dependentDeclarationIsLet declaration
                ]
              dependent = visible
              namedScope = scopedEnclosing
                { scopeDependentDeclarationLayers =
                    [dependentDeclarationLayer dependent
                      | not (null dependent)]
                      <> scopeDependentDeclarationLayers scopedEnclosing
                }
              runtimeDeclarations =
                [ declarationContextualDeclaration ContextualThis visible
                   | introduceThis
                   ]

      rebuild = fst . buildFrame
      scopedMembers = snd (buildFrame [])
      eagerFamilies =
        [ scoped
        | scoped <- scopedMembers
        , Just declaration <- [scopedDependentDeclarationValue scoped]
        , dependentDeclarationIsLet declaration
        ]
      consistencyCandidates =
        nub
          [ name
          | layer <- scopeDependentDeclarationLayers scopedEnclosing
          , scoped <- dependentDeclarationLayerMembers layer
          , scopedDependentDeclarationIsDefinition scoped
          , Just name <- [dependentDeclarationSingletonName scoped]
          ]
      validateConsistency resolving evaluated = do
        consistencyNames <- filterMRight
          (overlapsDeclarations resolving) consistencyCandidates
        mapM_ (validateConsistencyName resolving evaluated) consistencyNames
      overlapsDeclarations resolving name = anyMRight
        (\scoped -> dependentDeclarationContainsName
          UnrestrictedReduction resolving scoped name)
        (dependentDeclarationCandidates name scopedMembersLayer)
      validateConsistencyName resolving evaluated name =
        do
          let bounded = ShadowingConsistencyReduction
                name shadowingConsistencyFuel
          original <- resolveIdentifierAccess
            bounded
            scopedEnclosing
            resolving
            name
          replacement <- resolveIdentifierAccess
            bounded
            evaluated
            resolving
            name
          if interpretedSemanticResult original
              == interpretedSemanticResult replacement
            then Right ()
            else Left (InconsistentShadowing name)
  mapM_ (checkLetShadow scopedEnclosing) eagerFamilies
  if validateFamilies
    then validateDeclarationFamilies scopedMembers
    else Right ()
  pure
    ( rebuild
    , eagerFamilies
    , validateConsistency
    )
  where
    checkLetShadow enclosing scoped = mapM_ check
      protectedNames
      where
        protectedNames = nub
          [ name
          | layer <- scopeDependentDeclarationLayers enclosing
          , declaration <- dependentDeclarationLayerMembers layer
          , scopedDependentDeclarationIsDefinition declaration
          , Just name <- [dependentDeclarationSingletonName declaration]
          ]
        check name = do
          overlaps <- dependentDeclarationContainsName
            UnrestrictedReduction [] scoped name
          if overlaps
            then Left (LetBindingCannotShadowConsistentIdentifier name)
            else Right ()

validateDeclarationFamilies
  :: [ScopedDependentDeclaration]
  -> Either InterpretingError ()
validateDeclarationFamilies = go []
  where
    go _ [] = Right ()
    go earlier (scoped : remaining) = do
      case scopedDependentDeclarationValue scoped of
        Nothing -> go earlier remaining
        Just declaration ->
          validate scoped earlier remaining declaration

    validate scoped earlier remaining declaration = do
      family <- evalInScope
        (scopedDependentDeclarationFamilyScope scoped) []
        (dependentDeclarationNameFamilyExpression declaration)
      requireDependentNameSubfederation False
        (evalInScope
          (scopedDependentDeclarationFamilyScope scoped) [])
        family
      mapM_ (requireDistinct declaration family) earlier
      go ((declaration, family) : earlier) remaining

    requireDistinct declaration family (_, previous)
      | Right _ <- eitherValue previous family = Right ()
      | otherwise = Left (OverlappingBindings
          (dependentDeclarationLabel declaration))

    dependentDeclarationLabel = renderSourceExpression
      . dependentDeclarationNameExpression

interpretStringTemplateWith
  :: ScopeActivation
  -> Interpreter
  -> [StringTemplateInterpolation Expression]
  -> Either InterpretingError InterpretedValue
interpretStringTemplateWith protection interpret parts = do
  evaluated <- traverse interpretPart parts
  case map fst evaluated of
    [] -> asciiStringValue ""
    firstValue : remaining -> do
      result <- foldM concatenateTemplateValues firstValue remaining
      runProtectedOperation protection [result] $ \actuals ->
        case actuals of
          [actual] ->
            let segments = templateSegments evaluated
                captures =
                  [ ()
                  | EvaluatedStringTemplateCapture {} <- segments
                  ]
                templated = templateValue actual
            in Right
              (if null captures
                then templated
                else withStringTemplatePlan
                  (EvaluatedStringTemplate segments)
                  templated)
          _ -> Right neverValue
  where
    interpretPart
        (StringTemplateInterpolation (AsciiStringLiteral value)) =
      (, Nothing) <$> asciiStringValue value
    interpretPart (StringTemplateInterpolation expressionValue) = do
      value <- interpret expressionValue
      converted <- runProtectedOperationWithContract
        protection
        genericOperationResultDecision
        contextuallySpecify
        [value] $ \actuals ->
          case actuals of
            [actual] -> checkedString
              (toStringValue canonicalStringCodec actual)
            _ -> Right (neverValue, Nothing)
      pure (converted, Just (captureSchema expressionValue value))

    captureSchema expressionValue value =
      case captureExpression expressionValue of
        (Just name, annotation)
          | Just underlying <- identifierUnderlyingValue value ->
              simpleIdentifierTypeValue name
                (presentCaptureSchema annotation underlying)
        _ -> value

    templateSegments = snd . foldl appendPart (0, [])
    appendPart (captureIndex, segments) (converted, maybeCaptureSchema) =
      case maybeCaptureSchema of
        Nothing ->
          (captureIndex, appendLiteral (concreteString converted) segments)
        Just schema ->
          case concreteStringMaybe converted of
            Just literal ->
              (captureIndex, appendLiteral literal segments)
            Nothing ->
              ( captureIndex + 1
              , segments <>
                  [ EvaluatedStringTemplateCapture
                      captureIndex
                      schema
                      (argumentSchemaPositionalDomain
                        (argumentSchemaFromValue schema))
                  ]
              )

    appendLiteral "" segments = segments
    appendLiteral literal segments =
      case reverse segments of
        EvaluatedStringTemplateLiteral previous : remaining ->
          reverse remaining <>
            [EvaluatedStringTemplateLiteral (previous <> literal)]
        _ -> segments <> [EvaluatedStringTemplateLiteral literal]

    concreteString converted =
      case concreteStringMaybe converted of
        Just value -> value
        Nothing -> ""

    concreteStringMaybe converted =
      case interpretedSemanticResult converted of
        CanonicalAsciiString value -> Just value
        _ | interpretedValueHasTotalMap converted ->
              asciiStringFromInterpretedMap (interpretedMap converted)
          | otherwise -> Nothing

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

dependentDeclarationNamedView
  :: ReductionContext
  -> ResolutionStack
  -> ScopedDependentDeclaration
  -> Either InterpretingError NamedMapView
dependentDeclarationNamedView reduction resolving scoped =
  case scopedDependentDeclarationRuntimeProjection scoped of
    Just projection -> Right projection
    Nothing -> case scopedDependentDeclarationRuntime scoped of
      Just runtime
        | reduction == UnrestrictedReduction
            || not
              (runtimeDeclarationReevaluatesForRestrictedReduction runtime) -> do
            value <- runtimeDeclarationResolvedValue resolving scoped runtime
            let member = case scopedDependentDeclarationValue scoped of
                  Just declaration -> namedDeclarationDescriptorMember
                    declaration (runtimeDeclarationName runtime) value
                  Nothing -> runtimeSingletonDescriptorMember runtime value
            pure (singletonRuntimeDeclarationView member)
      _ -> case scopedDependentDeclarationValue scoped of
        Just declaration -> dynamicView declaration
        Nothing -> Left AmbiguousStringTemplate
  where
    captured = scopedDependentDeclarationScope scoped
    familyCaptured = scopedDependentDeclarationFamilyScope scoped
    dynamicView = dynamicDependentDeclarationNamedView
      reduction familyCaptured captured resolving

-- Literal syntax families have no finite runtime manifest: their concrete
-- names are selected on demand through the layer's indexed member and
-- containment operations. Enumerating them while constructing @this@ would
-- recursively evaluate their capture schemas through that same view.
singletonRuntimeDeclarationView :: NamedMember -> NamedMapView
singletonRuntimeDeclarationView member = NamedMapView (NamedMapProjection
  (Right ordinalProjection)
  (Right ordinalProjection)
  memberByName
  containsName
  (const (Right [member])))
  where
    name = namedMemberName member
    ordinalProjection = NamedMapOrdinalProjection
      (finiteOrdinal 1)
      (\position -> Right
        (if position == finiteOrdinal 0 then Just member else Nothing))
    memberByName candidate = Right
      (if candidate == name then Just member else Nothing)
    containsName candidate = Right (candidate == name)

runtimeSingletonDescriptorMember
  :: RuntimeSingletonPayload
  -> InterpretedValue
  -> NamedMember
runtimeSingletonDescriptorMember runtime payload = NamedMember name marked
  where
    name = runtimeDeclarationName runtime
    named = simpleIdentifierTypeValue name payload
    marked
      | runtimeDeclarationIsDefinition runtime =
          withTrailingIdentifierMarker definitionMarker named
      | otherwise = named

dynamicDependentDeclarationNamedView
  :: ReductionContext
  -> Scope
  -> Scope
  -> ResolutionStack
  -> DependentDeclaration Expression
  -> Either InterpretingError NamedMapView
dynamicDependentDeclarationNamedView reduction familyCaptured captured resolving
    declaration = Right (NamedMapView delayedProjection)
  where
    -- Preparing a declaration evaluates its capture schemas. Recursive module
    -- scopes must therefore delay preparation until a concrete named, ordinal,
    -- or manifest operation is requested; merely constructing @this@ is not
    -- such an operation.
    delayedProjection = NamedMapProjection
      collectionProjection
      (preparedView >>= namedProjectionOrdinal . namedMapProjection)
      (\name -> preparedViewFor name >>= (`namedMapMemberByName` name))
      (\name -> preparedViewFor name >>= (`namedMapContainsName` name))
      (\() -> preparedView >>= namedMapDeclaredMembers)

    collectionProjection =
      preparedView >>= namedProjectionCollection . namedMapProjection

    preparedView = do
      prepared <- prepareDependentDeclaration
        reduction familyCaptured resolving declaration
      preparedBranchesView prepared

    preparedViewFor name = do
      prepared <- prepareDependentDeclarationForName
        reduction familyCaptured resolving name declaration
      preparedBranchesView prepared

    preparedBranchesView prepared = do
      views <- traverse branchView prepared
      case views of
        [] -> Right (namedMapView
          (finiteOrdinal 0)
          (const (Right Nothing))
          (const (Right Nothing))
          (const (Right False)))
        [single] -> Right single
        first : remaining -> do
          let combined = foldl appendNamedMapViews first remaining
              projection = namedMapProjection combined
              selectedMember name = do
                selected <- selectPreparedDeclaration decode name prepared
                traverse (materializeSelection name) selected
              selectedAt position = do
                ordinal <- namedProjectionOrdinal projection
                member <- namedOrdinalProjectionMemberAt ordinal position
                case member of
                  Nothing -> Right Nothing
                  Just candidate -> selectedMember (namedMemberName candidate)
              selectedOrdinal =
                (\ordinalProjection -> ordinalProjection
                  { namedOrdinalProjectionMemberAt = selectedAt
                  }) <$> namedProjectionOrdinal projection
          pure (NamedMapView projection
            { namedProjectionCollection = namedProjectionCollection projection
            , namedProjectionOrdinal = selectedOrdinal
            , namedProjectionMemberByName = selectedMember
            , namedProjectionContainsName =
                fmap (maybe False (const True))
                  . flip (selectPreparedDeclaration decode) prepared
            })

    decode = decodeCanonicalTemplate
    branchView branch = do
      let evaluatedCaptures = preparedDeclarationCaptures branch
          template = preparedDeclarationTemplate branch
          captureBounds = map evaluatedDeclarationCaptureBound evaluatedCaptures
          ordinalProjection = case ordinalIndexedProductFamily captureBounds of
            Just family ->
              let sourceOrder = ordinalIndexedFamilyOrderType family
                  traversal = foliageMap sourceOrder
                  localOrder =
                    maybe omega finiteOrdinal (naturalAtOrdinal sourceOrder)
              in Right (NamedMapOrdinalProjection
                localOrder
                (memberAt evaluatedCaptures template family traversal))
            Nothing -> Left (captureOrdinalCapabilityFailure
              evaluatedCaptures captureBounds)
          collection
            | dependentDeclarationIsCanonicalValue declaration =
                ordinalProjection
            | otherwise = Right (NamedMapOrdinalProjection
                (finiteOrdinal 1)
                (\position ->
                  if position == finiteOrdinal 0
                    then do
                      members <- declaredMembers branch
                      pure (case members of
                        member : _ -> Just member
                        [] -> Nothing)
                    else Right Nothing))
      let selectedMember name = do
            selected <- selectPreparedDeclaration decode name [branch]
            traverse (materializeSelection name) selected
      pure (NamedMapView (NamedMapProjection
        collection
        ordinalProjection
        selectedMember
        (fmap (maybe False (const True))
          . flip (selectPreparedDeclaration decode) [branch])
        (const (declaredMembers branch))))

    captureOrdinalCapabilityFailure evaluatedCaptures captureBounds =
      case
          [ (index, schema)
          | (index, capture) <- zip [0 ..] evaluatedCaptures
          , let schema = evaluatedDeclarationCaptureSchema capture
                bound = evaluatedDeclarationCaptureBound capture
          , Nothing <- [ordinalIndexedValueFamily bound]
          ] of
        (index, schema) : _ -> LookupCaptureHasNoGenericMapView
          index (renderInterpretedValue schema)
        [] -> LookupCaptureHasNoGenericMapView
          0 (renderInterpretedValue (makeAtlasMap 2 captureBounds))

    memberAt evaluatedCaptures template family traversal position = case do
        rank <- naturalAtOrdinal position
        sourcePosition <- foliageMapPositionAt traversal rank
        ordinalIndexedFamilyValueAt family sourcePosition of
      Nothing -> Right Nothing
      Just witness -> do
        values <- captureWitnesses (length evaluatedCaptures) witness
        name <- renderLookupTemplateKey template witness
        Just <$> materializeMember evaluatedCaptures template name values

    -- A declaration descriptor represents the callable family, not one
    -- concrete member of that family. Its implementation is therefore
    -- evaluated only when concrete capture values invoke the descriptor; in
    -- particular, an @it@ implementation has no contextual argument while
    -- the descriptor manifest itself is being discovered.
    descriptorMember branch = do
      let template = preparedDeclarationTemplate branch
      let name = renderDeclarationDescriptorKey template
      payload <- declarationFamilyValue name branch
      pure (namedDeclarationDescriptorMember declaration name
        (attachDeclarationSyntax template payload))

    -- A declaration family with no name captures is the declaration value
    -- itself. Introducing a synthetic unit-domain callable here would replace
    -- the behavior of an ordinary callable declaration (for example @List@)
    -- with the behavior of its descriptor wrapper.
    declarationFamilyValue name branch
      | null (preparedDeclarationCaptures branch) =
          evaluateMaterializedDeclaration
            reduction captured resolving
            (dependentDeclarationImplementation declaration)
            [] [] (preparedDeclarationTemplate branch)
      | otherwise = declarationFamilyFunction name branch

    declarationFamilyFunction name branch = do
      let captures = preparedDeclarationCaptures branch
          schema = orderedArgumentSchema 2 (map captureSlot captures)
          template = preparedDeclarationTemplate branch
          implementation = dependentDeclarationImplementation declaration
          capabilityEnvelope = do
            evaluated <- either (const Nothing) Just
              (evaluateDeclarationDefinitionWith
                reduction captured resolving name Nothing implementation)
            interpretedFunction evaluated
          prepare argument = do
            (prepared, bindings) <-
              overloadArgumentSchemaComplete schema argument
            pure (PreparedFunctionArgument argument prepared bindings)
          evaluatePrepared activeReduction prepared = do
            values <- captureWitnesses
              (length captures) (functionPreparedArgument prepared)
            evaluateMaterializedDeclaration
              activeReduction captured resolving
              implementation
              captures values template
          invoke _ activeReduction prepared = do
            payload <- evaluatePrepared activeReduction prepared
            pure (EvaluatedFunctionInvocation payload Nothing)
          insertion = RuntimeFunctionInsertion
            { applyRuntimeFunction = \argument ->
                prepare argument >>= evaluatePrepared UnrestrictedReduction
            }
      domain <- argumentSchemaDomain schema
      pure (makeFunctionValue
            (EvaluatedFunction
              domain
              (maybe anyTypeValue functionCodomain capabilityEnvelope)
              Nothing
              (capabilityEnvelope >>= functionSource)
              (capabilityEnvelope >>= functionBody)
              (FunctionSource
                (IdentifierReference (SimpleIdentifierString name)))
              (Just prepare)
              (Just invoke)
              False
              (Just insertion)))

    captureSlot capture =
      maybe
        (argumentSlotSchema Nothing False schema Nothing)
        (\name -> dependentArgumentSlotSchema name False schema)
        (evaluatedDeclarationCaptureName capture)
      where
        schema = evaluatedDeclarationCaptureSchema capture

    declaredMembers branch = pure <$> descriptorMember branch

    materializeSelection name selected =
      case selected of
        PreparedDeclarationDescriptor branch ->
          descriptorMember branch
        PreparedDeclarationConcrete branch values ->
          materializeSelected name branch values

    materializeSelected name branch values =
      materializeMember
        (preparedDeclarationCaptures branch)
        (preparedDeclarationTemplate branch)
        name
        values

    materializeMember evaluatedCaptures template name values =
      materializeDependentDeclaration
        reduction captured resolving declaration
        evaluatedCaptures template name values

dependentDeclarationContainsName
  :: ReductionContext
  -> ResolutionStack
  -> ScopedDependentDeclaration
  -> String
  -> Either InterpretingError Bool
dependentDeclarationContainsName reduction resolving scoped name = do
  case scopedDependentDeclarationRuntimeProjection scoped of
    Just projection -> namedMapContainsName projection name
    Nothing
      | retainedName == Just name -> Right True
      | otherwise -> case scopedDependentDeclarationValue scoped of
          Nothing -> Right False
          Just declaration -> sourceContains declaration
  where
    captured = scopedDependentDeclarationScope scoped
    familyCaptured = scopedDependentDeclarationFamilyScope scoped
    retainedName = runtimeDeclarationName
      <$> scopedDependentDeclarationRuntime scoped
    sourceContains declaration
      = evaluateSource declaration $ \active ->
          prepareDependentDeclarationForName
            reduction familyCaptured active name declaration
    evaluateSource declaration prepare = evaluateDeferredDeclarationWith
          reduction captured resolving name
          (dependentDeclarationImplementation declaration)
          (const (Right True)) $ \active -> do
            prepared <- prepare active
            maybe False (const True) <$>
              selectPreparedDeclaration decode name prepared
    decode = decodeCanonicalTemplate

runtimeDeclarationResolvedValue
  :: ResolutionStack
  -> ScopedDependentDeclaration
  -> RuntimeSingletonPayload
  -> Either InterpretingError InterpretedValue
runtimeDeclarationResolvedValue resolving scoped runtime = do
  value <- case runtimeDeclarationValue runtime of
    EvaluatedRuntimeValue evaluated -> Right evaluated
    ContextualRuntimeValue surface _ _ _ ->
      contextualFunction surface
        (contextualLevels resolving surface
          (scopedDependentDeclarationScope scoped))
  pure (case runtimeDeclarationPresentation runtime of
    DirectRuntimePresentation -> value
    ReferencedRuntimePresentation dependencies ->
      withCanonicalReference dependencies
        (runtimeDeclarationName runtime) value
    TransparentRuntimePresentation -> withoutCanonicalPresentation value)

dependentDeclarationMemberByName
  :: ReductionContext
  -> ResolutionStack
  -> ScopedDependentDeclaration
  -> String
  -> Either InterpretingError (Maybe NamedMember)
dependentDeclarationMemberByName reduction resolving scoped name = do
  case scopedDependentDeclarationRuntimeProjection scoped of
    Just projection -> namedMapMemberByName projection name
    Nothing -> case scopedDependentDeclarationRuntime scoped of
      Just runtime
        | runtimeDeclarationName runtime == name
        , reduction == UnrestrictedReduction
            || not
              (runtimeDeclarationReevaluatesForRestrictedReduction runtime) -> do
            value <- runtimeDeclarationResolvedValue resolving scoped runtime
            pure (Just (case scopedDependentDeclarationValue scoped of
              Just declaration -> namedDeclarationDescriptorMember
                declaration name value
              Nothing -> runtimeSingletonDescriptorMember runtime value))
      _ -> case scopedDependentDeclarationValue scoped of
        Nothing -> Right Nothing
        Just declaration -> sourceMember declaration
  where
    captured = scopedDependentDeclarationScope scoped
    familyCaptured = scopedDependentDeclarationFamilyScope scoped
    sourceMember declaration
      = evaluateSource declaration $ \active ->
          prepareDependentDeclarationForName
            reduction familyCaptured active name declaration
    evaluateSource declaration prepare = evaluateDeferredDeclarationWith
          reduction captured resolving name
          (dependentDeclarationImplementation declaration)
          (seedMember declaration) $ \active -> do
            prepared <- prepare active
            selected <- selectPreparedDeclaration decode name prepared
            traverse (materialize declaration active) selected
    decode = decodeCanonicalTemplate
    seedMember declaration payload =
      Right (Just (namedDeclarationMember declaration name payload))
    materialize declaration active selected =
      case selected of
        PreparedDeclarationDescriptor branch -> do
          payload <- evaluateDeclarationDefinitionActive
            reduction captured active Nothing
            (dependentDeclarationImplementation declaration)
          let template = preparedDeclarationTemplate branch
          pure (namedDeclarationDescriptorMember declaration name
            (attachDeclarationSyntax template payload))
        PreparedDeclarationConcrete branch decoded ->
          materializeDependentDeclarationActive
            reduction captured active declaration
            (preparedDeclarationCaptures branch)
            (preparedDeclarationTemplate branch)
            name
            decoded

prepareDependentDeclaration
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> DependentDeclaration Expression
  -> Either InterpretingError
      [PreparedDependentDeclaration]
prepareDependentDeclaration reduction captured resolving declaration =
  prepareDependentDeclarationBranches reduction captured resolving
    (identifierExpressionBranches (dependentDeclarationHead declaration))

prepareDependentDeclarationForName
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> String
  -> DependentDeclaration Expression
  -> Either InterpretingError [PreparedDependentDeclaration]
prepareDependentDeclarationForName reduction captured resolving requested
    declaration =
  prepareDependentDeclarationBranches reduction captured resolving
    (identifierExpressionMatchingBranches
      (dependentDeclarationHead declaration) requested)

-- Parenthesized dependent names are evaluated expressions rather than
-- literal-expression syntax. Their result therefore has the same ordinary
-- inclusion obligation as an explicit @source of Str@ check. Arguments may
-- use an optional string family; declarations must themselves be strings.
requireDependentNameSubfederation
  :: Bool
  -> Interpreter
  -> InterpretedValue
  -> Either InterpretingError ()
requireDependentNameSubfederation allowOptional interpret value = do
  stringType <- interpret
    (IdentifierReference (SimpleIdentifierString "Str"))
  let checked
        | allowOptional = maybe value id (optionalUnderlying value)
        | otherwise = value
  requireValueSubfederation checked stringType

prepareDependentDeclarationBranches
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> [[StringTemplateInterpolation Expression]]
  -> Either InterpretingError
      [PreparedDependentDeclaration]
prepareDependentDeclarationBranches reduction captured resolving =
  traverse prepareBranch
  where
    prepareBranch parts = do
      let captureExpressions =
            [ captureExpression value
            | StringTemplateInterpolation value <- parts
            , case value of
                AsciiStringLiteral {} -> False
                _ -> True
            ]
      evaluatedCaptures <- traverse evaluateCapture captureExpressions
      let segments = dependentTemplateSegments parts evaluatedCaptures
      pure (PreparedDependentDeclaration
        evaluatedCaptures
        (EvaluatedStringTemplate segments))
    evaluateCapture (name, expressionValue) = do
      schema <- evalInScopeWith reduction captured resolving expressionValue
      pure (evaluatedDeclarationCapture name expressionValue schema)

selectPreparedDeclaration
  :: (EvaluatedStringTemplate
      -> String
      -> Either InterpretingError (Maybe [InterpretedValue]))
  -> String
  -> [PreparedDependentDeclaration]
  -> Either InterpretingError
      (Maybe PreparedDependentDeclarationSelection)
selectPreparedDeclaration decode name prepared =
  case
      [ branch
      | branch <- prepared
      , renderDeclarationDescriptorKey
          (preparedDeclarationTemplate branch) == name
      ] of
    [branch] -> Right (Just (PreparedDeclarationDescriptor branch))
    _ : _ -> Left AmbiguousStringTemplate
    [] -> fmap (fmap (uncurry PreparedDeclarationConcrete))
      (selectPreparedBranch decode name prepared)

selectPreparedBranch
  :: (EvaluatedStringTemplate
      -> String
      -> Either InterpretingError (Maybe [InterpretedValue]))
  -> String
  -> [PreparedDependentDeclaration]
  -> Either InterpretingError
      (Maybe (PreparedDependentDeclaration, [InterpretedValue]))
selectPreparedBranch decode name prepared = do
  matches <- fmap concat (traverse match prepared)
  case matches of
    [] -> Right Nothing
    [selected] -> Right (Just selected)
    _ -> Left AmbiguousStringTemplate
  where
    match branch = do
      decoded <- decode (preparedDeclarationTemplate branch) name
      pure (maybe [] (\values -> [(branch, values)]) decoded)

materializeDependentDeclaration
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> DependentDeclaration Expression
  -> [EvaluatedDeclarationCapture]
  -> EvaluatedStringTemplate
  -> String
  -> [InterpretedValue]
  -> Either InterpretingError NamedMember
materializeDependentDeclaration reduction captured resolving declaration
    evaluatedCaptures template name values =
  evaluateDeferredDeclarationWith
    reduction captured resolving name implementation seedMember $ \active ->
      materializeDependentDeclarationActive
        reduction captured active declaration
        evaluatedCaptures template name values
  where
    implementation = dependentDeclarationImplementation declaration
    seedMember payload = Right (namedDeclarationMember declaration name payload)

materializeDependentDeclarationActive
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> DependentDeclaration Expression
  -> [EvaluatedDeclarationCapture]
  -> EvaluatedStringTemplate
  -> String
  -> [InterpretedValue]
  -> Either InterpretingError NamedMember
materializeDependentDeclarationActive reduction captured resolving declaration
    evaluatedCaptures template name values = do
  payload <- evaluateMaterializedDeclaration
    reduction captured resolving implementation evaluatedCaptures values template
  pure (namedDeclarationMember declaration name payload)
  where
    implementation = dependentDeclarationImplementation declaration

evaluateMaterializedDeclaration
  :: ReductionContext
  -> Scope
  -> ResolutionStack
  -> Expression
  -> [EvaluatedDeclarationCapture]
  -> [InterpretedValue]
  -> EvaluatedStringTemplate
  -> Either InterpretingError InterpretedValue
evaluateMaterializedDeclaration reduction captured resolving implementation
    evaluatedCaptures values template = do
  input <- dependentDeclarationInput
    [ (captureName, Just schema, value)
    | (capture, value) <- zip evaluatedCaptures values
    , let captureName = evaluatedDeclarationCaptureName capture
          schema = evaluatedDeclarationCaptureSchema capture
    ]
  supplied <- makeArgumentativeMap values
  let contextualArgument = do
        members <- traverse contextualCapture
          (zip evaluatedCaptures values)
        makeArgumentativeMapPreservingSingleton members
      runtimeDeclarations =
        [ contextualRuntimeDeclaration ContextualIt False Nothing
            (const (const contextualArgument))
        | not (null evaluatedCaptures)
        ] <>
        [ evaluatedRuntimeDeclaration identifier value
        | (identifier, value) <- functionPreparedBindings input
        ]
      implementationScope =
        extendContextualRuntimeDeclarations runtimeDeclarations captured
  implementationValue <- evaluateDeclarationDefinitionActive reduction
      implementationScope
      resolving
      Nothing
      implementation
  payload <- if null evaluatedCaptures
    then Right implementationValue
    else applyDependentDeclarationImplementation
      (scopeActivation implementationScope)
      reduction
      input
      supplied
      implementationValue
  pure (attachDeclarationSyntax template payload)
  where
    contextualCapture (capture, value) =
      case captureName of
        Just name -> assignIdentifierValues name presentation value
        Nothing -> specifyValues value presentation
      where
        captureName = evaluatedDeclarationCaptureName capture
        presentation = evaluatedDeclarationCapturePresentation capture

dependentDeclarationInput
  :: [(Maybe String, Maybe InterpretedValue, InterpretedValue)]
  -> Either InterpretingError PreparedFunctionArgument
dependentDeclarationInput captures = do
  let supplied = makeAtlasMap 2 (map captureValue captures)
      schema = orderedArgumentSchema 2 (map captureSchema captures)
  (prepared, bindings) <- overloadArgumentSchemaComplete schema supplied
  pure (PreparedFunctionArgument supplied prepared bindings)
  where
    captureSchema (captureName, annotation, value) =
      maybe
        (argumentSlotSchema Nothing False domainValue Nothing)
        (\name -> dependentArgumentSlotSchema name False domainValue)
        captureName
      where
        domainValue = maybe value id annotation
    captureValue (_, _, value) = value

applyDependentDeclarationImplementation
  :: ScopeActivation
  -> ReductionContext
  -> PreparedFunctionArgument
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
applyDependentDeclarationImplementation activation reduction input supplied payload =
  case interpretedRuntimeFunctionInsertion payload of
    -- A runtime insertion is the already-selected forward operation, so it
    -- receives the capture schema's resolved positional argument.  An ordinary
    -- function still receives the argumentative source below and performs its
    -- own overload selection.
    Just insertion ->
      applyRuntimeFunction insertion (functionPreparedArgument input)
    Nothing
      | isFunctionFamily payload ->
          fst <$> applyFunction activation reduction payload supplied
      | otherwise -> Right payload

attachDeclarationSyntax
  :: EvaluatedStringTemplate
  -> InterpretedValue
  -> InterpretedValue
attachDeclarationSyntax template payload =
  case interpretedFunction payload of
    Nothing -> payload
    Just _ ->
      let evaluatedTemplate = concatMap evaluatedPiece
            (evaluatedStringTemplateSegments template)
      in withFunctionSyntax
        (FunctionSyntax [evaluatedTemplate])
        payload
  where
    evaluatedPiece segment = case segment of
      EvaluatedStringTemplateLiteral literal ->
        map (StringTemplateInterpolation . LiteralString) (words literal)
      EvaluatedStringTemplateCapture _ schema _ ->
        let stringFederation = templateValue
              (stringFederationValue canonicalStringCodec schema)
        in [StringTemplateInterpolation
          (specializeStringExpression schema (ValueString stringFederation))]

namedDeclarationMember
  :: DependentDeclaration Expression
  -> String
  -> InterpretedValue
  -> NamedMember
namedDeclarationMember declaration name payload =
  NamedMember name marked
  where
    named = simpleIdentifierTypeValue name payload
    -- Definition protection belongs on the concrete member used by lookup.
    -- Canonical-value metadata intentionally remains descriptor-only: putting
    -- $val here would replace the member's payload presentation with its
    -- canonical declaration name.
    marked = markDefinitionEntry declaration named

namedDeclarationDescriptorMember
  :: DependentDeclaration Expression
  -> String
  -> InterpretedValue
  -> NamedMember
namedDeclarationDescriptorMember declaration name payload = NamedMember name marked
  where
    named = simpleIdentifierTypeValue name payload
    marked = markDeclarationEntry declaration named

markDeclarationEntry
  :: DependentDeclaration Expression
  -> InterpretedValue
  -> InterpretedValue
markDeclarationEntry declaration =
  markDefinitionEntry declaration . markCanonical
  where
    markCanonical value
      | dependentDeclarationIsCanonicalValue declaration =
          withTrailingIdentifierMarker canonicalValueMarker value
      | otherwise = value

markDefinitionEntry
  :: DependentDeclaration Expression
  -> InterpretedValue
  -> InterpretedValue
markDefinitionEntry declaration value
  | dependentDeclarationIsDefinition declaration =
      withTrailingIdentifierMarker definitionMarker value
  | otherwise = value

captureExpression :: Expression -> (Maybe String, Expression)
captureExpression (SyntaxBoundary inner) = captureExpression inner
captureExpression
    (DependentArgument nameExpression (Just annotation))
      | Just (SimpleIdentifierString name) <-
          literalIdentifierName nameExpression =
            (Just name, annotation)
captureExpression expressionValue = (Nothing, expressionValue)

-- Capture validation uses the evaluated type, while materialized declaration
-- arguments retain a simple source-level type name for their assignment
-- evidence. Local declaration scopes do not add the import presentation that
-- an ordinary identifier lookup would otherwise contribute.
presentCaptureSchema :: Expression -> InterpretedValue -> InterpretedValue
presentCaptureSchema expressionValue schema =
  case expressionValue of
    SyntaxBoundary inner -> presentCaptureSchema inner schema
    IdentifierReference (SimpleIdentifierString name) ->
      withCanonicalReference [] name schema
    _ -> schema

evaluatedDeclarationCapture
  :: Maybe String
  -> Expression
  -> InterpretedValue
  -> EvaluatedDeclarationCapture
evaluatedDeclarationCapture name annotation schema =
  EvaluatedDeclarationCapture
    name
    schema
    (argumentSchemaPositionalDomain (argumentSchemaFromValue schema))
    (presentCaptureSchema annotation schema)

appendLiteralSegment
  :: String
  -> [EvaluatedStringTemplateSegment]
  -> [EvaluatedStringTemplateSegment]
appendLiteralSegment "" segments = segments
appendLiteralSegment literal segments = case reverse segments of
  EvaluatedStringTemplateLiteral previous : remaining ->
    reverse remaining <>
      [EvaluatedStringTemplateLiteral (previous <> literal)]
  _ -> segments <> [EvaluatedStringTemplateLiteral literal]

dependentTemplateSegments
  :: [StringTemplateInterpolation Expression]
  -> [EvaluatedDeclarationCapture]
  -> [EvaluatedStringTemplateSegment]
dependentTemplateSegments = go 0 []
  where
    go _ segments [] _ = segments
    go index segments
        (StringTemplateInterpolation (AsciiStringLiteral literal) : remaining)
        captures =
      go index (appendLiteralSegment literal segments) remaining captures
    go index segments
        (StringTemplateInterpolation _ : remaining)
        (capture : captures) =
      go (index + 1)
        (segments <>
          [ EvaluatedStringTemplateCapture
              index
              (evaluatedDeclarationCaptureSchema capture)
              (evaluatedDeclarationCaptureBound capture)
          ])
        remaining captures
    go _ segments _ [] = segments

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
recursiveCollectionElement :: RecursiveCollection -> Expression
recursiveCollectionElement collection =
  case collection of
    RecursiveList element -> element
    RecursiveStream element -> element

recursiveCollection :: Scope -> Expression -> Maybe RecursiveCollection
recursiveCollection scope expressionValue =
  case expressionValue of
    recursiveStep
      | Just (EitherType empty element, self) <-
          twoCellMapExpression recursiveStep
      , isEmptyMapExpression empty
      , isSelf self -> Just (RecursiveList element)
    EitherType empty recursiveStep
      | isEmptyMapExpression empty
      , Just (element, self) <- twoCellMapExpression recursiveStep
      , isSelf self -> Just (RecursiveList element)
    recursiveStep
      | Just (headExpression, self) <-
          twoCellMapExpression recursiveStep
      , isSelf self -> Just (RecursiveStream
          (requiredStreamElement headExpression))
    _ -> Nothing
  where
    isSelf = isContextualDeclarationReference ContextualThis scope
    requiredStreamElement headExpression =
      case headExpression of
        EitherType empty element
          | isEmptyMapExpression empty -> element
        _ -> headExpression

twoCellMapExpression :: Expression -> Maybe (Expression, Expression)
twoCellMapExpression expressionValue =
  case expressionValue of
    MapConcatenation left right -> Just (left, right)
    MapSequence [first, second] -> Just (first, second)
    AtlasMap [first, second] -> Just (first, second)
    SyntaxBoundary inner -> twoCellMapExpression inner
    _ -> Nothing

isEmptyMapExpression :: Expression -> Bool
isEmptyMapExpression expressionValue =
  case expressionValue of
    AtlasMap [] -> True
    MapSequence [] -> True
    SyntaxBoundary inner -> isEmptyMapExpression inner
    _ -> False

-- Generic bounds form one ordered telescope. Static function signatures use
-- each binder's upper bound, while invocation repeats the checks with the
-- actual witnesses.

closureResolver :: Scope -> Resolver
closureResolver scope = resolver
  where
    resolver = Resolver
      resolve scopeIndex contextualDepth definitionReference
    definitionReference path
      | dependencyPathRoot path == ContextualRoot ContextualThis = True
      | otherwise = case dependencyPathSegments path of
          [] -> False
          name : _ -> definitionName name
    definitionName name =
      any protectedDeclaration
          [ scoped
          | layer <- scopeDependentDeclarationLayers scope
          , scoped <- dependentDeclarationCandidates name layer
          ]
      where
        protectedDeclaration scoped =
          scopedDependentDeclarationIsDefinition scoped
            && either (const False) id
              (dependentDeclarationContainsName
                UnrestrictedReduction [] scoped name)
    scopeIndex expressionValue = do
      index <- either (const Nothing) Just (evalInScope scope [] expressionValue)
      (_, position) <- interpretedExplicitOrdinal index
      declarations <- scopeContextualDeclarationMembers ContextualThis scope
      view <- either (const Nothing) id
        (scopeEntriesNamedView UnrestrictedReduction [] declarations)
      member <- either (const Nothing) id
        (namedMapOrdinalMemberAt view position)
      pure (namedMemberName member)
    contextualDepth role depth = do
      let selected = contextualAccessAt role depth
      value <- either (const Nothing) Just (evalInScope scope [] selected)
      expressionValue <- either (const Nothing) Just
        (obsoleteValueExpressionIn scope value)
      let dependencyName =
            contextualSurfaceName role <> "_" <> show depth
      pure Dependency
        { dependencyKey = ContextualDependency role depth expressionValue
        , dependencyAddress = DependencyAddress
            [SimpleIdentifierString dependencyName]
        , dependencyDeclaration = singletonDependencyDeclaration
            dependencyName expressionValue
        , dependencyResolver = emptyResolver
        }
    resolve path
      | dependencyPathRoot path == ContextualRoot ContextualThis =
          case dependencyPathSegments path of
            [name] -> resolveAmbient [name]
            _ -> Nothing
      | otherwise = resolveAmbient (dependencyPathSegments path)
    resolveAmbient [] = Nothing
    resolveAmbient [context, name]
      | context == contextualPrivateName ContextualThis =
          resolveAmbient [name]
    resolveAmbient (name : fields@(_ : _))
      | Just runtime <- runtimeDeclarationByName name scope
      , Just public <- runtimeDeclarationPublicScope runtime
      , Just dependency <- resolveDependency
          (closureResolver public)
          (DependencyPath AmbientRoot fields) =
          Just dependency
            { dependencyAddress = prependDependencyAddress
                (originAddress name)
                (dependencyAddress dependency)
            -- OBSOLETE normalization seam: captured dependencies must retain
            -- their selected syntax instead of being reshaped externally.
            , dependencyDeclaration = dependentDeclarationWithImplementation
                (normalizeExpression
                  (dependentDeclarationImplementation
                    (dependencyDeclaration dependency)))
                (dependencyDeclaration dependency)
            }
    resolveAmbient (name : fields) = do
      case (fields, declarationDefinitionByName scope name) of
        ([], Just (lexical, _, expressionValue)) ->
          Just Dependency
            { dependencyKey = BindingDependency name expressionValue
            , dependencyAddress = originAddress name
            , dependencyDeclaration = singletonDependencyDeclaration
                name expressionValue
            , dependencyResolver = closureResolver lexical
            }
        _ -> do
          value <- either (const Nothing) Just
            (resolveIdentifier scope [] name)
          selected <- either (const Nothing) Just
            (foldM namedAccessValue value fields)
          if hasTrailingIdentifierMarker canonicalValueMarker selected
            then Nothing
            else do
              expressionValue <- either (const Nothing) Just
                (obsoleteValueExpressionIn scope selected)
              pure Dependency
                { dependencyKey = SelectedDependency
                    (map SimpleIdentifierString (name : fields)) expressionValue
                , dependencyAddress = appendDependencyAddress
                    (originAddress name)
                    (map SimpleIdentifierString fields)
                , dependencyDeclaration = singletonDependencyDeclaration
                    (last (name : fields)) expressionValue
                , dependencyResolver = emptyResolver
                }
    originAddress name
      | Just runtime <- runtimeDeclarationByName name scope
      , Just origin <- runtimeDeclarationOrigin runtime = origin
      | otherwise = DependencyAddress [SimpleIdentifierString name]

    prependDependencyAddress
        (DependencyAddress prefix)
        (DependencyAddress suffix) = DependencyAddress (prefix <> suffix)
    appendDependencyAddress
        (DependencyAddress prefix) suffix = DependencyAddress (prefix <> suffix)

singletonDependencyDeclaration
  :: String
  -> Expression
  -> DependentDeclaration Expression
singletonDependencyDeclaration name implementation = DependentDeclaration
  (literalIdentifierExpression (SimpleIdentifierString name))
  [DeclarationLet] implementation

emptyResolver :: Resolver
emptyResolver = Resolver
  (const Nothing)
  (const Nothing)
  (\_ _ -> Nothing)
  (const False)

-- OBSOLETE: render/parse/rewrite rematerialization from an evaluated value back
-- into an AST. Runtime values must retain the evidence needed by closures
-- without reconstructing source.
obsoleteValueExpressionIn
  :: Scope
  -> InterpretedValue
  -> Either InterpretingError Expression
obsoleteValueExpressionIn definitions = obsoleteClosedSourceExpressionIn definitions
  . renderCanonicalResult . interpretedSemanticResult

obsoleteClosedSourceExpressionIn
  :: Scope
  -> String
  -> Either InterpretingError Expression
obsoleteClosedSourceExpressionIn definitions text = do
  expressionValue <- either
    (const (Left NoCanonicalStringConversion))
    (Right . normalizeExpression)
    (parseSourceExpression text)
  rewritten <- Bifunctor.first
    (const NoCanonicalStringConversion)
    (rewriteStandaloneSyntax
      syntaxExpressionType definitions expressionValue)
  pure (inlineDependencies (closureResolver definitions) rewritten)
