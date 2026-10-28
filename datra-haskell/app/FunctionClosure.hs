-- | Close a function over exactly the identifier definitions it references.
-- Dependency blocks are executable Datra, not snapshots of an ambient scope.
module FunctionClosure
  ( DependencyKey (..)
  , DependencyAddress (..)
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
import Control.Monad.Trans.State.Strict (State, get, put, runState)
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
  | ContextualDependency String Natural Expression
  | ModuleDependency FilePath DependencyKey
  deriving (Eq, Show)

data Dependency = Dependency
  { dependencyKey :: DependencyKey
  , dependencyAddress :: DependencyAddress
  , dependencyDeclaration :: Maybe (DependentDeclaration Expression)
  , dependencyExpression :: Expression
  , dependencyResolver :: Resolver
  }

data Resolver = Resolver
  { resolveDependency :: [String] -> Maybe Dependency
  , resolveDependencyModule :: String -> Maybe Resolver
  , resolveScopeIndex :: Expression -> Maybe String
  , resolveContextualDepth :: String -> Natural -> Maybe Dependency
  , resolveDefinitionReference :: [String] -> Bool
  }

data DependencyMode = BindDependencies | InlineDependencies deriving (Eq)

type References = [(DependencyKey, Expression)]
type Collected =
  [ ( DependencyKey
    , DependencyAddress
    , Maybe (DependentDeclaration Expression)
    , Expression
    )
  ]

closeFunction
  :: Resolver
  -> Maybe DependencyKey
  -> Bool
  -> Bool
  -> Expression
  -> Expression
closeFunction resolver self explicitSelf selfIncludesDependencies expression =
  close BindDependencies 0 [] [] resolver self
    explicitSelf selfIncludesDependencies expression

-- Reuse the same scope-aware dependency graph when reconstructing values from
-- a source library.  Keeping dependencies as recursive local bindings avoids
-- repeatedly expanding shared branches, while an active back-edge can refer
-- directly to the binding whose definition is being collected.
inlineDependencies :: Resolver -> Expression -> Expression
inlineDependencies resolver expression =
  close InlineDependencies 0 [] [] resolver Nothing False False expression

close :: DependencyMode -> Int -> References -> [String] -> Resolver
  -> Maybe DependencyKey -> Bool -> Bool -> Expression -> Expression
close mode depth ancestors occupied resolver self
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
    reserved = occupied <> declaredNames expression
    root@(IdentifierString rootText) = fresh (functionName depth) reserved
    active = maybe ancestors
      (\key -> (key, IdentifierReference root) : ancestors) self
    initiallyBound
      | explicitSelf = [fixedThisMarker, contextualMarker "_this", "_this"]
      | otherwise = []
    (rewritten, collected) = runState
      (rewrite mode depth (rootText : reserved) active resolver
        initiallyBound expression)
      []
    definitions = dependencyDefinitions collected
    recursiveInBody = root `elem` referenceNames rewritten
    recursiveInDefinitions =
      root `elem` concatMap declarationReferenceNames definitions
    recursive = recursiveInBody || recursiveInDefinitions
    selfBound = explicitSelf || recursive
    selfRewritten
      | recursive = replaceReference root
          (contextualAccess (IdentifierString "_this")) rewritten
      | otherwise = rewritten
    selfDefinitions
      | recursive = map
          (mapDependentDeclaration
            (replaceReference root
              (contextualAccess (IdentifierString "_this"))))
          definitions
      | otherwise = definitions

rewrite :: DependencyMode -> Int -> [String] -> References -> Resolver -> [String]
  -> Expression -> State Collected Expression
rewrite mode depth reserved active resolver bound
    (MapAccess thisValue index)
  | isContextualAccessOf (IdentifierString "_this") thisValue
  , Just name <- resolveScopeIndex resolver index = do
      -- Pure captured selectors have a fixed result. Retain the calculation's
      -- dependencies as well as the selected declaration, without rebuilding
      -- unrelated entries of the original scope map.
      _ <- rewrite mode depth reserved active resolver bound index
      value <- rewrite mode depth reserved active resolver bound
        (IdentifierReference (IdentifierString name))
      pure (IdentifierOperation (IdentifierString name) value Nothing)
rewrite mode depth reserved active resolver bound expression
  | FunctionApplication
      (IdentifierReference (IdentifierString name))
      (EllipsisNatural requestedDepth) <- expression
  , name == "_this" || name == "_it"
  , let localDepth = contextualBoundDepth name bound =
      if requestedDepth < localDepth
        then pure expression
        else case resolveContextualDepth resolver name
            (requestedDepth - localDepth) of
          Just dependency -> collectDependency
            mode depth reserved active dependency
          Nothing -> pure expression
rewrite _ _ _ _ _ bound expression
  | Just path@(first : _) <- referencePath expression
  , let lexicalName = case path of
          ["\0this", name] -> name
          _ -> first
  , lexicalName `elem` bound = pure expression
rewrite mode depth reserved active resolver bound expression
  | Just path@(first : _) <- referencePath expression
  , let lexicalName = case path of
          ["\0this", name] -> name
          _ -> first
  , lexicalName `notElem` bound
  , Just dependency <- resolveDependency resolver path = do
      collectDependency mode depth reserved active dependency
rewrite _ _ _ _ _ _ expression
  | Just path <- referencePath expression
  , referencePathIsInternalContext path = pure expression
rewrite _ _ _ _ resolver _ expression
  | Just path <- referencePath expression
  , resolveDefinitionReference resolver path = pure expression

rewrite mode depth reserved active resolver bound expression =
  case expression of
    -- A short scope access evaluates its RHS name inside the child scope
    -- opened by the rewritten source. It is not an ambient dependency to
    -- capture or rename independently.
    ScopeAccess source body@IdentifierReference {} ->
      ScopeAccess
        <$> rewrite mode depth reserved active resolver bound source
        <*> pure body
    InModule path body
      | Just imported <- resolveDependencyModule resolver path ->
          rewrite mode (depth + 1) reserved active imported bound body
    FunctionApplication
        (FunctionTypeExpression generics domain codomain)
        (FunctionBody entries result) -> do
      let parameters = parameterNames domain
      closedGenerics <- traverse
        (\binder -> do
          closedBound <- rewrite mode depth reserved active resolver bound
            (genericBinderBound binder)
          pure binder
            { genericBinderBound = closedBound })
        generics
      closedDomain <- rewrite mode depth reserved active resolver
        (parameters <> bound) domain
      closedCodomain <- rewrite mode depth reserved active resolver
        (parameters <> bound) codomain
      body <- rewrite mode depth reserved active resolver
        (contextualMarker "_it" : "_it" : parameters <> bound)
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
    recur = rewrite mode depth reserved active resolver bound
    block constructor entries result = do
      let names = concatMap declarationBindingNames entries
          -- Source validity and declaration ordering have already been checked
          -- by the evaluator. Every block also binds its declaration map as
          -- @_this@ unless an explicit fixed point already occupies that name;
          -- either way it is local to the reconstructed expression and must
          -- never become a captured import.
          contextualBound
            | fixedThisMarker `elem` bound = names <> bound
            | otherwise =
                contextualMarker "_this" : "_this" : names <> bound
          inside = rewrite mode depth reserved active
            resolver { resolveScopeIndex = const Nothing }
            contextualBound
      constructor
        <$> traverse (traverseDependentDeclaration inside) entries
        <*> inside result

collectDependency
  :: DependencyMode
  -> Int
  -> [String]
  -> References
  -> Dependency
  -> State Collected Expression
collectDependency mode depth reserved active dependency =
  case lookup (dependencyKey dependency) active of
    Just reference -> pure reference
    Nothing -> do
      collected <- get
      case [ ()
           | (key, _, _, _) <- collected
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
                , dependencyExpression dependency
                )
              occupied = reserved
                <> dependencyGeneratedRoots (collected <> [pending])
          put (collected <>
            [pending])
          value <- rewrite mode (depth + 1) occupied
            ((key, reference) : active)
            (dependencyResolver dependency)
            []
            (dependencyExpression dependency)
          transitive <- get
          put
            [ if existingKey == key
                then (existingKey, existingAddress, declaration, value)
                else entry
            | entry@(existingKey, existingAddress, declaration, _) <- transitive
            ]
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

dependencyGeneratedRoots :: Collected -> [String]
dependencyGeneratedRoots collected = nub
  [ name
  | (_, DependencyAddress (root : _), _, _) <- collected
  , let IdentifierString name = prependIdentifier root
  ]

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
      [ capturedDeclaration prefixHere name declaration value
      | (_, DependencyAddress [name], declaration, value) <- collected
      ]
    childNames = nub
      [ name
      | (_, DependencyAddress (name : _ : _), _, _) <- collected
      ]
    childDefinition name = DependentDeclaration
      (SimpleIdentifierDeclarationHead renderedName)
      True False False childScope
      where
        renderedName = if prefixHere then prependIdentifier name else name
        childScope = Begin
          (scopeDefinitions False
            [ (key, DependencyAddress remaining, declaration, value)
            | (key, DependencyAddress (first : remaining), declaration, value)
                <- collected
            , first == name
            ])
          (contextualAccess (IdentifierString "_this"))

capturedDeclaration
  :: Bool
  -> IdentifierString
  -> Maybe (DependentDeclaration Expression)
  -> Expression
  -> DependentDeclaration Expression
capturedDeclaration prefixHere name maybeDeclaration value =
  translated
  where
    declaration = case maybeDeclaration of
      Just original -> dependentDeclarationWithImplementation value original
      Nothing -> DependentDeclaration
        (SimpleIdentifierDeclarationHead name)
        True False False value
    eager = declaration { dependentDeclarationIsLet = True }
    translated
      | prefixHere = prependDependentDeclarationName "_" eager
      | otherwise = eager

contextualMarker :: String -> String
contextualMarker = ("\0context:" <>)

fixedThisMarker :: String
fixedThisMarker = "\0context:fixed-this"

contextualBoundDepth :: String -> [String] -> Natural
contextualBoundDepth name =
  fromIntegral . length . filter (== contextualMarker name)

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

referencePath :: Expression -> Maybe [String]
referencePath
    (ScopeAccess
      thisValue
      (IdentifierReference (IdentifierString name)))
  | isContextualAccessOf (IdentifierString "_this") thisValue =
      Just ["\0this", name]
referencePath expression
  | FunctionApplication
      (IdentifierReference (IdentifierString name))
      (EllipsisNatural 0)
      <- expression = Just [name]
referencePath (IdentifierReference (IdentifierString name)) = Just [name]
referencePath
    (ScopeAccess source (IdentifierReference (IdentifierString name))) =
  (<> [name]) <$> referencePath source
referencePath _ = Nothing

-- The sentinel is the exact internal expansion of a lookup rooted at the
-- contextual @_this@ binding; it is never an ambient dependency.
referencePathIsInternalContext :: [String] -> Bool
referencePathIsInternalContext ("\0this" : _) = True
referencePathIsInternalContext _ = False

-- Generated roots use the same quoted namespace as their dependencies.
functionName :: Int -> String
functionName depth = replicate (depth + 2) '_' <> "fun"

fresh :: String -> [String] -> IdentifierString
fresh candidate reserved = go (0 :: Int)
  where
    go suffix
      | name `elem` reserved = go (suffix + 1)
      | otherwise = IdentifierString name
      where name = candidate <> if suffix == 0 then "" else "_" <> show suffix

parameterNames :: Expression -> [String]
parameterNames value@(IdentifierOperation _ _ _) = bindingNames value
parameterNames value
  | Just (named@IdentifierOperation {}, _) <-
      optionalIdentifierExpression value = bindingNames named
parameterNames value = concatMap parameterNames (expressionChildren value)

declaredNames :: Expression -> [String]
declaredNames value = nub (bindingNames value <> concatMap declaredNames (expressionChildren value))

referenceNames :: Expression -> [IdentifierString]
referenceNames (IdentifierReference name) = [name]
referenceNames value = concatMap referenceNames (expressionChildren value)

declarationReferenceNames
  :: DependentDeclaration Expression
  -> [IdentifierString]
declarationReferenceNames declaration =
  headReferences (dependentDeclarationHead declaration)
    <> referenceNames (dependentDeclarationImplementation declaration)
  where
    headReferences headValue = case headValue of
      SimpleIdentifierDeclarationHead {} -> []
      StringTemplateDeclarationHead parts -> concatMap partReferences parts
      EvaluatedDeclarationHead expressionValue -> referenceNames expressionValue
    partReferences part = case part of
      StringTemplateLiteral {} -> []
      StringTemplateInterpolation expressionValue ->
        referenceNames expressionValue

declarationBindingNames :: DependentDeclaration Expression -> [String]
declarationBindingNames declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) -> [name]
    StringTemplateDeclarationHead [StringTemplateLiteral name] -> [name]
    _ -> []

replaceReference :: IdentifierString -> Expression -> Expression -> Expression
replaceReference target replacement expression =
  case expression of
    IdentifierReference name | name == target -> replacement
    _ -> mapExpressionChildren (replaceReference target replacement) expression
