module Evaluation.Scope
  ( scopedDependentDeclarationScope
  , scopedDependentDeclarationFamilyScope
  , scopedDependentDeclarationValue
  , scopedIdentifierBranches
  , scopedIdentifierMatchingBranches
  , scopedDependentDeclarationRuntime
  , scopedDependentDeclarationRuntimeProjection
  , scopedDependentDeclarationIsDefinition
  , dependentDeclarationSingletonName
  , dependentDeclarationLayer
  , runtimeDeclarationLayer
  , withDeclarationLayerImportPolicy
  , extendImportedDeclarationLayer
  , dependentDeclarationCandidates
  , extendRuntimeDeclarations
  , extendImportedRuntimeScope
  , extendContextualRuntimeDeclarations
  , runtimeDeclarationByName
  , declarationDefinitionByName
  , scopedDeclarationDefinition
  , runtimePublicScopeForValue
  , evaluatedRuntimeDeclaration
  , contextualRuntimeDeclaration
  , constantContextualRuntimeDeclaration
  , rootScope
  , withPresentationOwner
  , enterScope
  , enterRuntimeScope
  , enterScopeWithReceiver
  , handoffScopeValue
  , scopeProtectedValues
  ) where

import Control.Applicative ((<|>))
import DatraLanguage.AST
import DatraLanguage.ContextualDeclaration
import DatraTypes
import DatraTypes.Resolution
import DatraTypes.Scope
import DatraTypes.Scope.Protection
import Evaluation.Scope.Protection
import StringInterpolation

scopedDependentDeclarationScope :: ScopedDependentDeclaration -> Scope
scopedDependentDeclarationScope scoped = case scoped of
  ScopedDatraDependentDeclaration captured _ _ _ -> captured
  ScopedRuntimeSingletonDeclaration captured _ -> captured
  ScopedProjectedDependentDeclaration captured _ -> captured

scopedDependentDeclarationFamilyScope :: ScopedDependentDeclaration -> Scope
scopedDependentDeclarationFamilyScope scoped = case scoped of
  ScopedDatraDependentDeclaration _ familyCaptured _ _ -> familyCaptured
  ScopedRuntimeSingletonDeclaration captured _ -> captured
  ScopedProjectedDependentDeclaration captured _ -> captured

scopedDependentDeclarationValue
  :: ScopedDependentDeclaration
  -> Maybe (DependentDeclaration Expression)
scopedDependentDeclarationValue scoped = case scoped of
  ScopedDatraDependentDeclaration _ _ declaration _ -> Just declaration
  ScopedRuntimeSingletonDeclaration {} -> Nothing
  ScopedProjectedDependentDeclaration {} -> Nothing

scopedIdentifierBranches
  :: ScopedDependentDeclaration
  -> [[StringTemplateInterpolation Expression]]
scopedIdentifierBranches scoped = case scoped of
  ScopedDatraDependentDeclaration _ _ declaration _ ->
    identifierExpressionBranches (dependentDeclarationHead declaration)
  ScopedRuntimeSingletonDeclaration _ runtime ->
    [[StringTemplateInterpolation (AsciiStringLiteral name)]]
    where
      name = runtimeDeclarationName runtime
  ScopedProjectedDependentDeclaration {} -> []

scopedIdentifierMatchingBranches
  :: String
  -> ScopedDependentDeclaration
  -> [[StringTemplateInterpolation Expression]]
scopedIdentifierMatchingBranches requested scoped = case scoped of
  ScopedDatraDependentDeclaration _ _ declaration _ ->
    identifierExpressionMatchingBranches
      (dependentDeclarationHead declaration) requested
  ScopedRuntimeSingletonDeclaration _ runtime
    | runtimeDeclarationName runtime == requested ->
        scopedIdentifierBranches scoped
    | otherwise -> []
  ScopedProjectedDependentDeclaration {} ->
    -- A projected runtime map owns its membership operation and cannot expose
    -- an unevaluated source template here.
    [[]]

scopedDependentDeclarationRuntime
  :: ScopedDependentDeclaration
  -> Maybe RuntimeSingletonPayload
scopedDependentDeclarationRuntime scoped = case scoped of
  ScopedDatraDependentDeclaration _ _ _ runtime -> runtime
  ScopedRuntimeSingletonDeclaration _ runtime -> Just runtime
  ScopedProjectedDependentDeclaration {} -> Nothing

scopedDependentDeclarationRuntimeProjection
  :: ScopedDependentDeclaration
  -> Maybe NamedMapView
scopedDependentDeclarationRuntimeProjection scoped = case scoped of
  ScopedDatraDependentDeclaration {} -> Nothing
  ScopedRuntimeSingletonDeclaration {} -> Nothing
  ScopedProjectedDependentDeclaration _ projection -> Just projection

scopedDependentDeclarationIsDefinition
  :: ScopedDependentDeclaration
  -> Bool
scopedDependentDeclarationIsDefinition scoped =
  maybe False dependentDeclarationIsDefinition
      (scopedDependentDeclarationValue scoped)
    || maybe False runtimeDeclarationIsDefinition
      (scopedDependentDeclarationRuntime scoped)

dependentDeclarationSingletonName
  :: ScopedDependentDeclaration
  -> Maybe String
dependentDeclarationSingletonName scoped =
  case scopedIdentifierBranches scoped of
    [[StringTemplateInterpolation (AsciiStringLiteral name)]] -> Just name
    _ -> Nothing

dependentDeclarationLayer
  :: [ScopedDependentDeclaration]
  -> DependentDeclarationLayer
dependentDeclarationLayer =
  makeDependentDeclarationLayer SourceDeclarationLayer

runtimeDeclarationLayer
  :: [ScopedDependentDeclaration]
  -> DependentDeclarationLayer
runtimeDeclarationLayer =
  makeDependentDeclarationLayer RuntimeDeclarationLayer

makeDependentDeclarationLayer
  :: DeclarationLayerOrigin
  -> [ScopedDependentDeclaration]
  -> DependentDeclarationLayer
makeDependentDeclarationLayer origin =
  DependentDeclarationLayer origin LocalDeclarationLayer

withDeclarationLayerImportPolicy
  :: DeclarationLayerImportPolicy
  -> DependentDeclarationLayer
  -> DependentDeclarationLayer
withDeclarationLayerImportPolicy policy layer = layer
  { dependentDeclarationLayerImportPolicy = policy }

extendImportedDeclarationLayer
  :: DeclarationLayerImportPolicy
  -> DependentDeclarationLayer
  -> Scope
  -> Scope
extendImportedDeclarationLayer policy layer scope = scope
  { scopeDependentDeclarationLayers =
      withDeclarationLayerImportPolicy policy layer
        : scopeDependentDeclarationLayers scope }

dependentDeclarationCandidates
  :: String
  -> DependentDeclarationLayer
  -> [ScopedDependentDeclaration]
dependentDeclarationCandidates name layer =
  filter
    (not . null . scopedIdentifierMatchingBranches name)
    (dependentDeclarationLayerMembers layer)

scopedRuntimeDeclarations
  :: Scope
  -> RuntimeSingletonPayload
  -> [ScopedDependentDeclaration]
scopedRuntimeDeclarations scope runtime =
  [ScopedRuntimeSingletonDeclaration scope runtime]

scopedContextualSurfaceDeclarations
  :: Scope
  -> [RuntimeSingletonPayload]
  -> [ScopedDependentDeclaration]
scopedContextualSurfaceDeclarations captured declarations =
  [ ScopedDatraDependentDeclaration
      captured
      captured
      declaration
      Nothing
  | runtime <- declarations
  , ContextualRuntimeValue role _ _ _ <- [runtimeDeclarationValue runtime]
  , let declaration = contextualSurfaceDeclaration role
  ]

extendRuntimeDeclarations :: [RuntimeSingletonPayload] -> Scope -> Scope
extendRuntimeDeclarations = extendRuntimeDeclarationsWithPolicy
  LocalDeclarationLayer

extendImportedRuntimeScope
  :: DeclarationLayerImportPolicy
  -> [RuntimeSingletonPayload]
  -> Maybe NamedMapView
  -> Scope
  -> Scope
extendImportedRuntimeScope _ [] Nothing scope = scope
extendImportedRuntimeScope policy declarations projection parent = scope
  where
    scope = parent
      { scopeDependentDeclarationLayers =
          withDeclarationLayerImportPolicy policy
            (runtimeDeclarationLayer
              ( concatMap (scopedRuntimeDeclarations scope) declarations
                <> maybe [] (pure . ScopedProjectedDependentDeclaration scope)
                  projection
              ))
            : scopeDependentDeclarationLayers parent
      }

extendRuntimeDeclarationsWithPolicy
  :: DeclarationLayerImportPolicy
  -> [RuntimeSingletonPayload]
  -> Scope
  -> Scope
extendRuntimeDeclarationsWithPolicy _ [] scope = scope
extendRuntimeDeclarationsWithPolicy policy declarations parent = scope
  where
    scope = parent
      { scopeDependentDeclarationLayers =
          withDeclarationLayerImportPolicy policy
            (runtimeDeclarationLayer
              (concatMap
                (scopedRuntimeDeclarations scope)
                declarations))
            : scopeDependentDeclarationLayers parent
      }

-- A contextual surface declaration belongs to the semantic scope which makes
-- its private value available. Ordinary runtime declaration extension remains
-- context-free: callers which establish a contextual scope opt into this paired
-- private/surface layer explicitly.
extendContextualRuntimeDeclarations
  :: [RuntimeSingletonPayload]
  -> Scope
  -> Scope
extendContextualRuntimeDeclarations [] scope = scope
extendContextualRuntimeDeclarations declarations parent = surfaceScope
  where
    primitiveScope = extendRuntimeDeclarations declarations parent
    surfaceDeclarations =
      scopedContextualSurfaceDeclarations primitiveScope declarations
    surfaceScope
      | null surfaceDeclarations = primitiveScope
      | otherwise = primitiveScope
          { scopeDependentDeclarationLayers =
              runtimeDeclarationLayer surfaceDeclarations
                : scopeDependentDeclarationLayers primitiveScope
          }

runtimeDeclarationByName :: String -> Scope -> Maybe RuntimeSingletonPayload
runtimeDeclarationByName name scope = firstLayer
  (scopeDependentDeclarationLayers scope)
  where
    firstLayer [] = Nothing
    firstLayer (layer : remaining) =
      case
          [ runtime
          | scoped <- dependentDeclarationCandidates name layer
          , Just runtime <- [scopedDependentDeclarationRuntime scoped]
          , runtimeDeclarationName runtime == name
          ] of
        runtime : _ -> Just runtime
        [] -> firstLayer remaining

declarationDefinitionByName
  :: Scope
  -> String
  -> Maybe (Scope, Maybe Expression, Expression)
declarationDefinitionByName scope name = firstLayer
  (scopeDependentDeclarationLayers scope)
  where
    firstLayer [] = Nothing
    firstLayer (layer : remaining) =
      case dependentDeclarationCandidates name layer of
        scoped : _ -> scopedDeclarationDefinition scoped
        [] -> firstLayer remaining

scopedDeclarationDefinition
  :: ScopedDependentDeclaration
  -> Maybe (Scope, Maybe Expression, Expression)
scopedDeclarationDefinition scoped =
  runtimeDefinition <|> sourceDefinition
  where
    runtimeDefinition = scopedDependentDeclarationRuntime scoped
      >>= runtimeDeclarationDefinition
    sourceDefinition = do
      declaration <- scopedDependentDeclarationValue scoped
      pure
        ( scopedDependentDeclarationScope scoped
        , Nothing
        , dependentDeclarationImplementation declaration
        )

-- | Recover the retained declaration scope which produced an evaluated
-- namespace value.  Namespace opening is based on the selected value and its
-- declaration provenance, never on the syntactic shape of the expression
-- which selected it.  An identifier reference, an alias, and a dependent
-- declaration application therefore all use this same path.
runtimePublicScopeForValue :: InterpretedValue -> Scope -> Maybe Scope
runtimePublicScopeForValue selected scope = firstLayer
  (scopeDependentDeclarationLayers scope)
  where
    firstLayer [] = Nothing
    firstLayer (layer : outer) = case
        [ public
        | scoped <- dependentDeclarationLayerMembers layer
        , Just runtime <- [scopedDependentDeclarationRuntime scoped]
        , EvaluatedRuntimeValue value <- [runtimeDeclarationValue runtime]
        , interpretedSemanticResult value == interpretedSemanticResult selected
        , Just public <- [runtimeDeclarationPublicScope runtime]
        ] of
      public : _ -> Just public
      [] -> firstLayer outer

evaluatedRuntimeDeclaration
  :: String
  -> InterpretedValue
  -> RuntimeSingletonPayload
evaluatedRuntimeDeclaration name value = RuntimeSingletonPayload
  { runtimeDeclarationName = name
  , runtimeDeclarationIsDefinition = False
  , runtimeDeclarationValue = EvaluatedRuntimeValue value
  , runtimeDeclarationPresentation = DirectRuntimePresentation
  , runtimeDeclarationOrigin = Nothing
  , runtimeDeclarationDefinition = Nothing
  , runtimeDeclarationPublicScope = Nothing
  , runtimeDeclarationReevaluatesForRestrictedReduction = False
  }

contextualRuntimeDeclaration
  :: ContextualRole
  -> Bool
  -> Maybe [ScopedDependentDeclaration]
  -> (ResolutionStack
      -> ReductionContext
      -> Either InterpretingError InterpretedValue)
  -> RuntimeSingletonPayload
contextualRuntimeDeclaration role includesDependencies declarations value =
  RuntimeSingletonPayload
    { runtimeDeclarationName = contextualPrivateName role
    , runtimeDeclarationIsDefinition = True
    , runtimeDeclarationValue = ContextualRuntimeValue
        role includesDependencies declarations value
    , runtimeDeclarationPresentation = DirectRuntimePresentation
    , runtimeDeclarationOrigin = Nothing
    , runtimeDeclarationDefinition = Nothing
    , runtimeDeclarationPublicScope = Nothing
    , runtimeDeclarationReevaluatesForRestrictedReduction = False
    }

constantContextualRuntimeDeclaration
  :: ContextualRole
  -> InterpretedValue
  -> RuntimeSingletonPayload
constantContextualRuntimeDeclaration role value =
  contextualRuntimeDeclaration role False Nothing (const (const (Right value)))

rootScope :: salt -> Scope
rootScope salt = Scope
  { scopeDependentDeclarationLayers = []
  , scopePresentationOwner = Nothing
  , scopeActivation = initialScopeActivation salt
  , scopeHandoff = Nothing
  }

withPresentationOwner :: PresentationOwner -> Scope -> Scope
withPresentationOwner owner scope = scope
  { scopePresentationOwner = Just owner }

enterScope
  :: salt
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope
enterScope salt decide parent = Scope
  { scopeDependentDeclarationLayers = scopeDependentDeclarationLayers parent
  , scopePresentationOwner = scopePresentationOwner parent
  , scopeActivation = enterScopeActivation salt (scopeActivation parent)
  , scopeHandoff = Just (ScopeHandoff (scopeActivation parent) decide)
  }

enterRuntimeScope
  :: salt
  -> [RuntimeSingletonPayload]
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope
enterRuntimeScope salt declarations decide parent =
  extendRuntimeDeclarations declarations (enterScope salt decide parent)

enterScopeWithReceiver
  :: salt
  -> ScopeActivation
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope
enterScopeWithReceiver salt receiver decide parent =
  (enterScope salt decide parent)
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

scopeProtectedValues :: Scope -> [InterpretedValue]
scopeProtectedValues scope =
  [ value
  | layer <- scopeDependentDeclarationLayers scope
  , scoped <- dependentDeclarationLayerMembers layer
  , Just runtime <- [scopedDependentDeclarationRuntime scoped]
  , EvaluatedRuntimeValue value <- [runtimeDeclarationValue runtime]
  , valueIsScopeProtected value
  ]

