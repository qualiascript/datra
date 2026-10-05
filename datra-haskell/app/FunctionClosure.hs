-- | Close a function over exactly the identifier definitions it references.
-- Dependency blocks are executable Datra, not snapshots of an ambient scope.
module FunctionClosure
  ( Dependency (..)
  , Resolver (..)
  , closeFunction
  , inlineDependencies
  , canonicalDependencyNames
  ) where

import BlockScope (bindingNames)
import Data.List (nub, stripPrefix)
import DatraLanguage.AST
import DatraLanguage.Identifier (requiresShadowingConsistency)
import Control.Monad.Trans.State.Strict (State, get, put, runState)

-- Keys identify bindings during this traversal only; they never enter source.
-- The resolver belongs to the definition's original environment.
data Dependency = Dependency
  { dependencyKey :: String
  , dependencyName :: String
  , dependencyExpression :: Expression
  , dependencyResolver :: Resolver
  }

data Resolver = Resolver
  { resolveDependency :: [String] -> Maybe Dependency
  , resolveDependencyModule :: String -> Maybe Resolver
  , resolveScopeIndex :: Expression -> Maybe String
  }

data DependencyMode = BindDependencies | InlineDependencies deriving (Eq)

type References = [(String, IdentifierString)]
type Collected = [(String, IdentifierString, Expression)]

closeFunction :: Resolver -> Maybe String -> Bool -> Bool -> Expression -> Expression
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
  -> Maybe String -> Bool -> Bool -> Expression -> Expression
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
    active = maybe ancestors (\key -> (key, root) : ancestors) self
    initiallyBound = ["'this" | explicitSelf]
    (rewritten, collected) = runState
      (rewrite mode depth (rootText : reserved) active resolver
        initiallyBound expression)
      []
    definitions =
      [ Let (assigned name value)
      | (_, name, value) <- collected
      ]
    recursiveInBody = root `elem` referenceNames rewritten
    recursiveInDefinitions = root `elem` concatMap referenceNames definitions
    recursive = recursiveInBody || recursiveInDefinitions
    selfBound = explicitSelf || recursive
    selfRewritten
      | recursive = replaceReference root
          (IdentifierReference (IdentifierString "'this")) rewritten
      | otherwise = rewritten
    selfDefinitions
      | recursive = map
          (replaceReference root (IdentifierReference (IdentifierString "'this")))
          definitions
      | otherwise = definitions

rewrite :: DependencyMode -> Int -> [String] -> References -> Resolver -> [String]
  -> Expression -> State Collected Expression
rewrite mode depth reserved active resolver bound
    (MapAccess (IdentifierReference (IdentifierString "'this")) index)
  | Just name <- resolveScopeIndex resolver index = do
      -- Pure captured selectors have a fixed result. Retain the calculation's
      -- dependencies as well as the selected declaration, without rebuilding
      -- unrelated entries of the original scope map.
      selector <- rewrite mode depth reserved active resolver bound index
      value <- rewrite mode depth reserved active resolver bound
        (IdentifierReference (IdentifierString name))
      pure (Begin [Let selector]
        (IdentifierOperation (IdentifierString name) value Nothing))
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
      case lookup (dependencyKey dependency) active of
        Just name -> pure (IdentifierReference name)
        Nothing -> do
          collected <- get
          case [(name, value) | (key, name, value) <- collected, key == dependencyKey dependency] of
            (name, _) : _ -> pure (IdentifierReference name)
            [] -> do
              let name = fresh
                    ("___" <> dependencyName dependency)
                    (reserved <> [text | (_, IdentifierString text, _) <- collected])
                  occupied = reserved
                    <> [text | (_, IdentifierString text, _) <- collected]
                    <> [nameText name]
              value <- rewrite mode (depth + 1) occupied
                ((dependencyKey dependency, name) : active)
                (dependencyResolver dependency)
                []
                (dependencyExpression dependency)
              transitive <- get
              put (transitive <> [(dependencyKey dependency, name, value)])
              pure (IdentifierReference name)
rewrite _ _ _ _ _ _ expression
  | Just path <- referencePath expression
  , referencePathRequiresShadowingConsistency path = pure expression

rewrite mode depth reserved active resolver bound expression =
  case expression of
    InModule path body
      | Just imported <- resolveDependencyModule resolver path ->
          rewrite mode (depth + 1) reserved active imported bound body
    MapSpecification (FunctionBody entries result) (FunctionType domain codomain) -> do
      let parameters = parameterNames domain
      closedDomain <- rewrite mode depth reserved active resolver
        (parameters <> bound) domain
      closedCodomain <- rewrite mode depth reserved active resolver
        (parameters <> bound) codomain
      body <- rewrite mode depth reserved active resolver
        ("'it" : parameters <> bound) (FunctionBody entries result)
      pure (MapSpecification body (FunctionType closedDomain closedCodomain))
    FunctionBody entries result -> block FunctionBody entries result
    Begin entries result -> block Begin entries result
    Program entries result -> block Program entries result
    OptionalType operand
      | Nothing <- optionalIdentifierExpression expression ->
          recur
            (FunctionApplication
              (IdentifierReference (IdentifierString "Maybe"))
              operand)
    SyntaxType _ signature -> recur signature
    MapSpecification implementation (SyntaxType _ signature) ->
      recur (MapSpecification implementation signature)
    _ -> traverseExpressionChildren recur expression
  where
    recur = rewrite mode depth reserved active resolver bound
    block constructor entries result = do
      let names = concatMap bindingNames entries
          -- Source validity and declaration ordering have already been checked
          -- by the evaluator. Every block also binds its declaration map as
          -- @'this@ unless an explicit fixed point already occupies that name;
          -- either way it is local to the reconstructed expression and must
          -- never become a captured import.
          inside = rewrite mode depth reserved active
            resolver { resolveScopeIndex = const Nothing }
            ("'this" : names <> bound)
      constructor <$> traverse inside entries <*> inside result

-- A retained begin block is itself a singleton type.  Selecting the result
-- from an ordered pair outside that block recovers the yielded value's own
-- type family while keeping the recursive lexical scope executable.  The
-- leading value keeps the sequence explicit through source normalization;
-- semicolon sequencing preserves a map-valued result as one member.
transparentDependencyBlock :: [Expression] -> Expression -> Expression
transparentDependencyBlock definitions result =
  MapAccess
    (Begin definitions (MapSequence [EllipsisNatural 0, result]))
    (EllipsisNatural 1)

referencePath :: Expression -> Maybe [String]
referencePath
    (MapAccess
      (NamedAccess
        (IdentifierReference (IdentifierString "'this"))
        (IdentifierString name))
      (EllipsisNatural 1)) =
  Just ["\0this", name]
referencePath (IdentifierReference (IdentifierString name)) = Just [name]
referencePath (NamedAccess source (IdentifierString name)) = (<> [name]) <$> referencePath source
referencePath _ = Nothing

-- A reference rooted in a shadowing-consistent binding is one stable lexical
-- path. If the complete path cannot be captured, never reinterpret its root as
-- a separate dependency. The sentinel is the exact internal expansion of a
-- lookup rooted at the shadowing-consistent @'this@ binding.
referencePathRequiresShadowingConsistency :: [String] -> Bool
referencePathRequiresShadowingConsistency ("\0this" : _) = True
referencePathRequiresShadowingConsistency (name : _) =
  requiresShadowingConsistency name
referencePathRequiresShadowingConsistency [] = False

assigned :: IdentifierString -> Expression -> Expression
assigned name expression = IdentifierOperation name expression (Just expression)

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
parameterNames (ForBinding (IdentifierString name) _ _) = [name]
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

-- Decode only a complete reconstruction block, never an arbitrary user name.
-- Removing exactly the scope prefix plus the user marker preserves all original
-- leading underscores, including names which resemble generated identifiers.
canonicalDependencyNames :: [Expression] -> Expression -> [(String, String)]
canonicalDependencyNames entries result
  | isClosedFunctionResult result =
    [(text, original) | entry <- entries, IdentifierString text <- entryName entry
      , Just original <- [stripPrefix "___" text]]
  | otherwise = []
  where
    isClosedFunctionResult (Fun value) = isFunction value
    isClosedFunctionResult value = isFunction value
    isFunction (MapSpecification (FunctionBody {}) (FunctionType {})) = True
    isFunction _ = False

nameText :: IdentifierString -> String
nameText (IdentifierString text) = text

entryName :: Expression -> [IdentifierString]
entryName (Let value) = entryName value
entryName (IdentifierOperation name _ _) = [name]
entryName _ = []

replaceReference :: IdentifierString -> Expression -> Expression -> Expression
replaceReference target replacement expression =
  case expression of
    IdentifierReference name | name == target -> replacement
    _ -> mapExpressionChildren (replaceReference target replacement) expression
