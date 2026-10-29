-- | Close a function over exactly the identifier definitions it references.
-- Dependency blocks are executable Datra, not snapshots of an ambient scope.
module FunctionClosure
  ( DependencyKey (..)
  , DependencyAddress (..)
  , DependencyPath (..)
  , DependencyRoot (..)
  , Dependency (..)
  , Resolver (..)
  , closeFunction
  , inlineDependencies
  ) where

import DatraLanguage.DependentDeclaration
  ( bindingNames
  , dependentDeclarationWithImplementation
  , prependDependentDeclarationName
  )
import Data.List (nub)
import DatraLanguage.AST
import DatraLanguage.ContextualDeclaration
import Control.Monad.Trans.State.Strict (State, get, modify', put, runState)
import Numeric.Natural (Natural)

-- Keys identify bindings during this traversal only; they never enter source.
-- The resolver belongs to the definition's original environment.
newtype DependencyAddress = DependencyAddress
  { dependencyAddressSegments :: [IdentifierString]
  }
  deriving (Eq, Show)

data DependencyKey
  = BindingDependency String Expression
  | SelectedDependency [IdentifierString] Expression
  | ContextualDependency ContextualRole Natural Expression
  | ModuleDependency FilePath DependencyKey
  deriving (Eq, Show)

data Dependency = Dependency
  { dependencyKey :: DependencyKey
  , dependencyAddress :: DependencyAddress
  , dependencyDeclaration :: DependentDeclaration Expression
  , dependencyResolver :: Resolver
  }

data DependencyRoot
  = AmbientRoot
  | ContextualRoot ContextualRole
  deriving (Eq, Show)

data DependencyPath = DependencyPath
  { dependencyPathRoot :: DependencyRoot
  , dependencyPathSegments :: [String]
  }
  deriving (Eq, Show)

data Resolver = Resolver
  { resolveDependency :: DependencyPath -> Maybe Dependency
  , resolveDependencyModule :: String -> Maybe Resolver
  , resolveScopeIndex :: Expression -> Maybe String
  , resolveContextualDepth :: ContextualRole -> Natural -> Maybe Dependency
  , resolveDefinitionReference :: DependencyPath -> Bool
  }

data DependencyMode = BindDependencies | InlineDependencies deriving (Eq)

data ActiveReference = ActiveReference
  { activeReferenceExpression :: Expression
  , activeReferenceIsClosureSelf :: Bool
  }

type References = [(DependencyKey, ActiveReference)]
type Collected =
  [ ( DependencyKey
    , DependencyAddress
    , DependentDeclaration Expression
    )
  ]

data ClosureState = ClosureState
  { closureSelfReferenced :: Bool
  , closureSelfReferencedInDefinition :: Bool
  , closureCollected :: Collected
  }

data BoundName
  = LexicalBound String
  | ContextualBound ContextualRole
  | FixedThisBound
  deriving (Eq)

closeFunction
  :: Resolver
  -> Maybe DependencyKey
  -> Bool
  -> Bool
  -> Expression
  -> Expression
closeFunction resolver self explicitSelf selfIncludesDependencies expression =
  close BindDependencies resolver self
    explicitSelf selfIncludesDependencies expression

-- Reuse the same scope-aware dependency graph when reconstructing values from
-- a source library.  Keeping dependencies as recursive local bindings avoids
-- repeatedly expanding shared branches, while an active back-edge can refer
-- directly to the binding whose definition is being collected.
inlineDependencies :: Resolver -> Expression -> Expression
inlineDependencies resolver expression =
  close InlineDependencies resolver Nothing False False expression

close :: DependencyMode -> Resolver
  -> Maybe DependencyKey -> Bool -> Bool -> Expression -> Expression
close mode resolver self
    explicitSelf selfIncludesDependencies original =
  case mode of
    InlineDependencies
      | null definitions -> selfRewritten
      | otherwise -> transparentDependencyBlock definitions selfRewritten
    BindDependencies ->
      case (null definitions, recursiveInDefinitions, selfBound) of
        (True, _, False) -> selfRewritten
        (True, _, True) -> Fun selfRewritten
        (False, True, _) -> Fun (Begin selfDefinitions selfRewritten)
        (False, False, True) | selfIncludesDependencies ->
          Fun (Begin definitions selfRewritten)
        (False, False, True) -> Begin definitions (Fun selfRewritten)
        (False, False, False) -> Begin definitions selfRewritten
  where
    expression = original
    active = maybe []
      (\key ->
        [ ( key
          , ActiveReference (contextualAccess ContextualThis) True
          )
        ]) self
    initiallyBound
      | explicitSelf =
          [ FixedThisBound
          , ContextualBound ContextualThis
          , LexicalBound (contextualPrivateName ContextualThis)
          ]
      | otherwise = []
    (rewritten, ClosureState recursive recursiveInDefinitions collected) =
      runState
        (rewrite mode False active resolver initiallyBound expression)
        (ClosureState False False [])
    definitions = dependencyDefinitions collected
    selfBound = explicitSelf || recursive
    selfRewritten = rewritten
    selfDefinitions = definitions

rewrite :: DependencyMode -> Bool -> References -> Resolver -> [BoundName]
  -> Expression -> State ClosureState Expression
rewrite mode inDefinition active resolver bound
    (MapAccess thisValue index)
  | isContextualAccessOf ContextualThis thisValue
  , Just name <- resolveScopeIndex resolver index = do
      -- Pure captured selectors have a fixed result. Retain the calculation's
      -- dependencies as well as the selected declaration, without rebuilding
      -- unrelated entries of the original scope map.
      _ <- rewrite mode inDefinition active resolver bound index
      value <- rewrite mode inDefinition active resolver bound
        (IdentifierReference (IdentifierString name))
      pure (IdentifierOperation (IdentifierString name) value Nothing)
rewrite mode inDefinition active resolver bound expression
  | FunctionApplication
      (IdentifierReference identifier)
      (EllipsisNatural requestedDepth) <- expression
  , Just role <- contextualRoleForIdentifier identifier
  , let localDepth = contextualBoundDepth role bound =
      if requestedDepth < localDepth
        then pure expression
        else case resolveContextualDepth resolver role
            (requestedDepth - localDepth) of
          Just dependency -> collectDependency
            mode inDefinition active dependency
          Nothing -> pure expression
rewrite _ _ _ _ bound expression
  | Just path <- referencePath expression
  , Just lexicalName <- dependencyPathLexicalName path
  , LexicalBound lexicalName `elem` bound = pure expression
rewrite mode inDefinition active resolver bound expression
  | Just path <- referencePath expression
  , Just lexicalName <- dependencyPathLexicalName path
  , LexicalBound lexicalName `notElem` bound
  , Just dependency <- resolveDependency resolver path = do
      collectDependency mode inDefinition active dependency
rewrite _ _ _ _ _ expression
  | Just path <- referencePath expression
  , referencePathIsInternalContext path = pure expression
rewrite _ _ _ resolver _ expression
  | Just path <- referencePath expression
  , resolveDefinitionReference resolver path = pure expression

rewrite mode inDefinition active resolver bound expression =
  case expression of
    -- A short scope access evaluates its RHS name inside the child scope
    -- opened by the rewritten source. It is not an ambient dependency to
    -- capture or rename independently.
    ScopeAccess source body@IdentifierReference {} ->
      ScopeAccess
        <$> rewrite mode inDefinition active resolver bound source
        <*> pure body
    InModule path body
      | Just imported <- resolveDependencyModule resolver path ->
          rewrite mode inDefinition active imported bound body
    FunctionApplication
        (FunctionTypeExpression generics domain codomain)
        (FunctionBody entries result) -> do
      let parameters = parameterNames domain
      closedGenerics <- traverse
        (\binder -> do
          closedBound <- rewrite mode inDefinition active resolver bound
            (genericBinderBound binder)
          pure binder
            { genericBinderBound = closedBound })
        generics
      closedDomain <- rewrite mode inDefinition active resolver
        (map LexicalBound parameters <> bound) domain
      closedCodomain <- rewrite mode inDefinition active resolver
        (map LexicalBound parameters <> bound) codomain
      body <- rewrite mode inDefinition active resolver
        ( ContextualBound ContextualIt
        : LexicalBound (contextualPrivateName ContextualIt)
        : map LexicalBound parameters <> bound)
        (FunctionBody entries result)
      pure (FunctionApplication
        (FunctionTypeExpression closedGenerics closedDomain closedCodomain)
        body)
    FunctionBody entries result -> block FunctionBody entries result
    Begin entries result -> block Begin entries result
    OptionalType operand
      | Nothing <- optionalIdentifierExpression expression ->
          recur
            (FunctionApplication
              (IdentifierReference (IdentifierString "Maybe"))
              operand)
    _ -> traverseExpressionChildren recur expression
  where
    recur = rewrite mode inDefinition active resolver bound
    block constructor entries result = do
      let names = concatMap declarationBindingNames entries
          -- Source validity and declaration ordering have already been checked
          -- by the evaluator. Every block also binds its declaration map as
          -- @_this@ unless an explicit fixed point already occupies that name;
          -- either way it is local to the reconstructed expression and must
          -- never become a captured import.
          contextualBound
            | FixedThisBound `elem` bound = map LexicalBound names <> bound
            | otherwise =
                ContextualBound ContextualThis
                : LexicalBound (contextualPrivateName ContextualThis)
                : map LexicalBound names <> bound
          inside = rewrite mode inDefinition active
            resolver { resolveScopeIndex = const Nothing }
            contextualBound
      constructor
        <$> traverse (traverseDependentDeclaration inside) entries
        <*> inside result

collectDependency
  :: DependencyMode
  -> Bool
  -> References
  -> Dependency
  -> State ClosureState Expression
collectDependency mode inDefinition active dependency =
  case lookup (dependencyKey dependency) active of
    Just reference -> do
      if activeReferenceIsClosureSelf reference
        then modify' (\state -> state
          { closureSelfReferenced = True
          , closureSelfReferencedInDefinition =
              closureSelfReferencedInDefinition state || inDefinition
          })
        else pure ()
      pure (activeReferenceExpression reference)
    Nothing -> do
      collected <- closureCollected <$> get
      case [ ()
           | (key, _, _) <- collected
           , key == dependencyKey dependency
           ] of
        _ : _ -> pure (dependencyReference (dependencyAddress dependency))
        [] -> do
          let address = dependencyAddress dependency
              key = dependencyKey dependency
              reference = dependencyReference address
              pending =
                ( key
                , address
                , dependencyDeclaration dependency
                )
          modify' (\state -> state
            { closureCollected = collected <> [pending] })
          value <- rewrite mode True
            ((key, ActiveReference reference False) : active)
            (dependencyResolver dependency)
            []
            (dependentDeclarationImplementation
              (dependencyDeclaration dependency))
          state <- get
          let transitive = closureCollected state
          put state
            { closureCollected =
                [ if existingKey == key
                    then
                      ( existingKey
                      , existingAddress
                      , dependentDeclarationWithImplementation value declaration
                      )
                    else entry
                | entry@(existingKey, existingAddress, declaration) <- transitive
                ]
            }
          pure reference

dependencyReference :: DependencyAddress -> Expression
dependencyReference (DependencyAddress []) =
  IdentifierReference (IdentifierString "_")
dependencyReference (DependencyAddress (root : fields)) =
  foldl ScopeAccess
    (IdentifierReference (prependIdentifier root))
    (map IdentifierReference fields)

prependIdentifier :: IdentifierString -> IdentifierString
prependIdentifier (IdentifierString name) = IdentifierString ('_' : name)

-- Captured declarations are grouped by their structural origin. Only the
-- declaration entering the closure gets translated by the injective @_@
-- prefix; members retain their names inside a recreated scope.
dependencyDefinitions :: Collected -> [DependentDeclaration Expression]
dependencyDefinitions = scopeDefinitions True

scopeDefinitions :: Bool -> Collected -> [DependentDeclaration Expression]
scopeDefinitions prefixHere collected =
  directDefinitions <> map childDefinition childNames
  where
    directDefinitions =
      [ capturedDeclaration prefixHere name declaration
      | (_, DependencyAddress [name], declaration) <- collected
      ]
    childNames = nub
      [ name
      | (_, DependencyAddress (name : _ : _), _) <- collected
      ]
    childDefinition name = DependentDeclaration
      (SimpleIdentifierDeclarationHead renderedName)
      True False False childScope
      where
        renderedName = if prefixHere then prependIdentifier name else name
        childScope = Begin
          (scopeDefinitions False
            [ (key, DependencyAddress remaining, declaration)
            | (key, DependencyAddress (first : remaining), declaration)
                <- collected
            , first == name
            ])
          (contextualAccess ContextualThis)

capturedDeclaration
  :: Bool
  -> IdentifierString
  -> DependentDeclaration Expression
  -> DependentDeclaration Expression
capturedDeclaration prefixHere _ declaration =
  translated
  where
    eager = declaration { dependentDeclarationIsLet = True }
    translated
      | prefixHere = prependDependentDeclarationName "_" eager
      | otherwise = eager

contextualBoundDepth :: ContextualRole -> [BoundName] -> Natural
contextualBoundDepth role =
  fromIntegral . length . filter (== ContextualBound role)

-- A retained begin block is itself a singleton type.  Selecting the result
-- from an ordered pair outside that block recovers the yielded value's own
-- type family while keeping the recursive lexical scope executable.  The
-- leading value keeps the sequence explicit through source normalization;
-- semicolon sequencing preserves a map-valued result as one member.
transparentDependencyBlock
  :: [DependentDeclaration Expression]
  -> Expression
  -> Expression
transparentDependencyBlock definitions result =
  MapAccess
    (Begin definitions (MapSequence [EllipsisNatural 0, result]))
    (EllipsisNatural 1)

referencePath :: Expression -> Maybe DependencyPath
referencePath
    (ScopeAccess
      thisValue
      (IdentifierReference (IdentifierString name)))
  | isContextualAccessOf ContextualThis thisValue =
      Just (DependencyPath (ContextualRoot ContextualThis) [name])
referencePath expression
  | FunctionApplication
      (IdentifierReference (IdentifierString name))
      (EllipsisNatural 0)
      <- expression = Just (DependencyPath AmbientRoot [name])
referencePath (IdentifierReference (IdentifierString name)) =
  Just (DependencyPath AmbientRoot [name])
referencePath
    (ScopeAccess source (IdentifierReference (IdentifierString name))) =
  appendPath name <$> referencePath source
  where
    appendPath field path = path
      { dependencyPathSegments = dependencyPathSegments path <> [field] }
referencePath _ = Nothing

dependencyPathLexicalName :: DependencyPath -> Maybe String
dependencyPathLexicalName path = case dependencyPathSegments path of
  name : _ -> Just name
  [] -> Nothing

referencePathIsInternalContext :: DependencyPath -> Bool
referencePathIsInternalContext path =
  dependencyPathRoot path == ContextualRoot ContextualThis

parameterNames :: Expression -> [String]
parameterNames value@(IdentifierOperation _ _ _) = bindingNames value
parameterNames value
  | Just (named@IdentifierOperation {}, _) <-
      optionalIdentifierExpression value = bindingNames named
parameterNames value = concatMap parameterNames (expressionChildren value)

declarationBindingNames :: DependentDeclaration Expression -> [String]
declarationBindingNames declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) -> [name]
    StringTemplateDeclarationHead [StringTemplateLiteral name] -> [name]
    _ -> []
