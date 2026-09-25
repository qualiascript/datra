-- | Close a function over exactly the identifier definitions it references.
-- Dependency blocks are executable Datra, not snapshots of an ambient scope.
module FunctionClosure
  ( Dependency (..)
  , Resolver (..)
  , closeFunction
  , canonicalDependencyNames
  ) where

import Data.List (nub, stripPrefix)
import Data.Char (isDigit)
import DatraLanguage.AST
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

type References = [(String, IdentifierString)]
type Collected = [(String, IdentifierString, Expression)]

closeFunction :: Resolver -> Maybe String -> Expression -> Expression
closeFunction resolver self expression =
  close 0 [] [] resolver self expression

close :: Int -> References -> [String] -> Resolver -> Maybe String -> Expression -> Expression
close depth ancestors occupied resolver self original =
  if null definitions && not recursive
    then rewritten
    else Begin (definitions <> [Let (assigned root rewritten)]) (IdentifierReference root)
  where
    expression = rebaseClosed depth occupied [] original
    reserved = occupied <> declaredNames expression
    root@(IdentifierString rootText) = fresh (functionName depth) reserved
    active = maybe ancestors (\key -> (key, root) : ancestors) self
    (rewritten, collected) = runState (rewrite depth (rootText : reserved) active resolver [] expression) []
    definitions = [assigned name value | (_, name, value) <- collected]
    recursive = root `elem` referenceNames rewritten

rewrite :: Int -> [String] -> References -> Resolver -> [String]
  -> Expression -> State Collected Expression
rewrite depth reserved active resolver bound (MapAccess This index)
  | Just name <- resolveScopeIndex resolver index = do
      -- Pure captured selectors have a fixed result. Retain the calculation's
      -- dependencies as well as the selected declaration, without rebuilding
      -- unrelated entries of the original scope map.
      selector <- rewrite depth reserved active resolver bound index
      value <- rewrite depth reserved active resolver bound
        (IdentifierReference (IdentifierString name))
      pure (Begin [Let selector]
        (IdentifierOperation (IdentifierString name) value Nothing))
rewrite depth reserved active resolver bound expression
  | Just path@(first : _) <- referencePath expression
  , first `notElem` bound
  , Just dependency <- resolveDependency resolver path = do
      case lookup (dependencyKey dependency) active of
        Just name -> pure (IdentifierReference name)
        Nothing -> do
          collected <- get
          case [name | (key, name, _) <- collected, key == dependencyKey dependency] of
            name : _ -> pure (IdentifierReference name)
            [] -> do
              let name = fresh
                    (replicate (depth + 2) '_' <> "_" <> dependencyName dependency)
                    (reserved <> [text | (_, IdentifierString text, _) <- collected])
                  value = close (depth + 1) active
                    (reserved <> [text | (_, IdentifierString text, _) <- collected] <> [nameText name])
                    (dependencyResolver dependency)
                    (Just (dependencyKey dependency))
                    (dependencyExpression dependency)
              put (collected <> [(dependencyKey dependency, name, value)])
              pure (IdentifierReference name)

rewrite depth reserved active resolver bound expression =
  case expression of
    InModule path body
      | Just imported <- resolveDependencyModule resolver path ->
          pure (close (depth + 1) active reserved imported Nothing body)
    MapSpecification (FunctionBody entries result) (FunctionType domain codomain) -> do
      closedDomain <- rewrite depth reserved active resolver bound domain
      closedCodomain <- rewrite depth reserved active resolver bound codomain
      body <- rewrite depth reserved active resolver
        ("it" : parameterNames domain <> bound) (FunctionBody entries result)
      pure (MapSpecification body (FunctionType closedDomain closedCodomain))
    FunctionBody entries result -> block FunctionBody entries result
    Begin entries result -> block Begin entries result
    Program entries result -> block Program entries result
    _ -> traverseExpressionChildren recur expression
  where
    recur = rewrite depth reserved active resolver bound
    block constructor entries result = do
      let names = concatMap bindingNames entries
          -- Source validity and declaration ordering have already been checked
          -- by the evaluator; bound names must never become captured imports.
          inside = rewrite depth reserved active
            resolver { resolveScopeIndex = const Nothing } (names <> bound)
      constructor <$> traverse inside entries <*> inside result

referencePath :: Expression -> Maybe [String]
referencePath (MapAccess (NamedAccess This (IdentifierString name)) (EllipsisNatural 1)) =
  Just ["\0this", name]
referencePath (IdentifierReference (IdentifierString name)) = Just [name]
referencePath (NamedAccess source (IdentifierString name)) = (<> [name]) <$> referencePath source
referencePath _ = Nothing

assigned :: IdentifierString -> Expression -> Expression
assigned name expression = IdentifierOperation name expression Nothing

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

bindingNames :: Expression -> [String]
bindingNames (Let value) = bindingNames value
bindingNames (IdentifierOperation (IdentifierString name) _ _) = [name]
bindingNames (EitherType named@(IdentifierOperation _ _ _) _) = bindingNames named
bindingNames _ = []

parameterNames :: Expression -> [String]
parameterNames value@(IdentifierOperation _ _ _) = bindingNames value
parameterNames (EitherType named@(IdentifierOperation _ _ _) _) = bindingNames named
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
canonicalDependencyNames entries result = case canonicalBlock entries result of
  Just (depth, root, _) ->
    [(text, original) | entry <- entries, name@(IdentifierString text) <- entryName entry
      , name /= root, Just original <- [stripPrefix (replicate (depth + 3) '_') text]]
  Nothing -> []

canonicalBlock :: [Expression] -> Expression -> Maybe (Int, IdentifierString, String)
canonicalBlock entries (IdentifierReference root@(IdentifierString rootText)) = do
  collisionSuffix <- stripPrefix "fun" (dropWhile (== '_') rootText)
  let depth = length (takeWhile (== '_') rootText) - 2
  if depth >= 0
      && (null collisionSuffix || case collisionSuffix of
        '_' : rest -> not (null rest) && all isDigit rest
        _ -> False)
    then case reverse entries of
      Let (IdentifierOperation declared _ _) : _ | declared == root ->
        Just (depth, root, collisionSuffix)
      _ -> Nothing
    else Nothing
canonicalBlock _ _ = Nothing

nameText :: IdentifierString -> String
nameText (IdentifierString text) = text

entryName :: Expression -> [IdentifierString]
entryName (Let value) = entryName value
entryName (IdentifierOperation name _ _) = [name]
entryName _ = []

-- Generated descendants will be renamed in their own scopes. Reserving their
-- old spellings in the parent would make every round trip invent new suffixes.
ordinaryDeclaredNames :: Expression -> [String]
ordinaryDeclaredNames (Begin entries result)
  | Just _ <- canonicalBlock entries result =
      concatMap contents entries <> ordinaryDeclaredNames result
  where
    contents (Let value) = contents value
    contents (IdentifierOperation _ annotation given) =
      ordinaryDeclaredNames annotation <> maybe [] ordinaryDeclaredNames given
    contents value = ordinaryDeclaredNames value
ordinaryDeclaredNames value =
  bindingNames value <> concatMap ordinaryDeclaredNames (expressionChildren value)

-- Move an already closed function into a dependency subblock without colliding
-- with the caller's generated bindings. Only blocks with our complete emitted
-- shape are rebased; user names and observable ordinary map fields are retained.
rebaseClosed :: Int -> [String] -> [(IdentifierString, IdentifierString)] -> Expression -> Expression
rebaseClosed depth occupied inherited expression = case expression of
  Begin entries result
    | Just (oldDepth, root, _) <- canonicalBlock entries result ->
        let candidate name@(IdentifierString text)
              | name == root = IdentifierString (functionName depth)
              | Just tailText <- stripPrefix (replicate (oldDepth + 2) '_') text =
                  IdentifierString (replicate (depth + 2) '_' <> tailText)
              | otherwise = name
            names = [name | declaration <- entries
                     , name <- entryName declaration]
            ordinaryNames = ordinaryDeclaredNames expression
            reserved = occupied <> ordinaryNames
            allocate namesSoFar name = namesSoFar <>
              [(name, fresh (nameText (candidate name))
                (reserved <> map (nameText . snd) namesSoFar))]
            assignedNames = foldl allocate [] names
            scope = assignedNames <> inherited
            enclosingNames = reserved <> map (nameText . snd) assignedNames
            entry (Let value) = Let (entry value)
            entry (IdentifierOperation name annotation given) =
              IdentifierOperation (renamed scope name)
                (rebaseClosed (depth + 1) enclosingNames scope annotation)
                (rebaseClosed (depth + 1) enclosingNames scope <$> given)
            entry value = rebaseClosed (depth + 1) enclosingNames scope value
        in Begin (map entry entries) (IdentifierReference (renamed scope root))
  IdentifierReference name -> IdentifierReference (renamed inherited name)
  NamedAccess This name -> NamedAccess This (renamed inherited name)
  _ -> mapExpressionChildren (rebaseClosed depth occupied inherited) expression
  where
    renamed names name = maybe name id (lookup name names)
