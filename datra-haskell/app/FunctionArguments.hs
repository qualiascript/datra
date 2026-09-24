-- | Preserve parameter identities while the ordinary federation machinery
-- checks each member. Matching never chooses an arbitrary permutation.
module FunctionArguments
  ( ParameterSchema (..), compileParameters, parameterBindings, parameterDomain, matchArguments
  ) where

import Control.Monad (foldM)
import Data.List (nubBy, permutations, sortOn)
import DatraLanguage.AST
import DatraTypes
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)

data ParameterSchema
  = Parameter (Maybe String) Bool InterpretedValue
  | Ordered [ParameterSchema]
  | Unordered [ParameterSchema]
  | Concatenated [ParameterSchema]

compileParameters :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression -> Either InterpretingError ParameterSchema
compileParameters evaluate expression = case expression of
  IdentifierOperation (IdentifierString name) annotation given ->
    Parameter (Just name) False <$> evaluate (maybe annotation (`MapSpecification` annotation) given)
  EitherType named@(IdentifierOperation (IdentifierString name) annotation _) missing
    | annotation == missing -> do
        schema <- compileParameters evaluate named
        case schema of
          Parameter _ _ target -> Right (Parameter (Just name) True target)
          _ -> Left (FunctionError "invalid optional parameter")
  AtlasMap members -> Ordered <$> traverse recur members
  MapSequence members -> Ordered <$> traverse recur members
  ArgumentMap members -> Unordered <$> traverse recur members
  MapConcatenation _ _ -> Concatenated <$> traverse recur (flatten expression)
    where flatten (MapConcatenation a b) = flatten a <> flatten b
          flatten value = [value]
  _ -> Parameter Nothing False <$> evaluate expression
  where recur = compileParameters evaluate

parameterBindings :: ParameterSchema -> [(String, InterpretedValue)]
parameterBindings schema = case schema of
  Parameter (Just name) _ target -> [(name, target)]
  Parameter Nothing _ _ -> []
  Ordered children -> concatMap parameterBindings children
  Unordered children -> concatMap parameterBindings children
  Concatenated children -> concatMap parameterBindings children

matchArguments :: ParameterSchema -> InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
matchArguments schema input = do
  presentations <- argumentPresentations input
  let routes = map (matches schema) presentations
  if any null routes
    then Left (FunctionError "input does not match every presentation of the parameter specification")
    else pure ()
  case nubBy sameBindings (concat routes) of
    [] -> Left (FunctionError "input does not match the function's parameter specification")
    [bindings] -> Right bindings
    _ -> Left (FunctionError "ambiguous argument bindings; supply identifiers to select the intended slots")
  where
    sameBindings left right = canonical left == canonical right
    canonical = sortOn fst . map (\(name,value) -> (name, interpretedCanonicalResult value))

matches :: ParameterSchema -> InterpretedValue -> [[(String, InterpretedValue)]]
matches schema input = case schema of
  Parameter name optional target ->
    let selected = case (name, identifierName (interpretedCanonicalResult input)) of
          (Just expected, Just actual) | expected == actual ->
            accessValues input (naturalValue 1)
          (Just _, Just _) -> Left (FunctionError "argument name mismatch")
          (Just _, Nothing) | not optional -> Left (FunctionError "argument name required")
          _ -> Right input
    in case selected >>= (`specifyValues` target) of
      Right _ -> case selected of
        Right value -> [maybe [] (\key -> [(key, value)]) name]
        Left _ -> []
      Left _ -> []
  Ordered children -> matchChildren children input
  Unordered children -> concatMap (`matchChildren` input) (permutations children)
  Concatenated children -> case inputMembers input of
    Just members -> matchSegments children members
    Nothing -> []

matchChildren :: [ParameterSchema] -> InterpretedValue -> [[(String,InterpretedValue)]]
matchChildren [child] input = matches child input
matchChildren children input = case inputMembers input of
  Just members | length members == length children ->
    map concat (sequence (zipWith matches children members))
  _ -> []

-- Concatenation flattens pages; split by each schema component's cardinality
-- while preserving the distinction between ordered and unordered segments.
matchSegments :: [ParameterSchema] -> [InterpretedValue] -> [[(String, InterpretedValue)]]
matchSegments [] [] = [[]]
matchSegments [] _ = []
matchSegments (schema:rest) members =
  let count = width schema
      (selected, remaining) = splitAt count members
      value = case selected of [one] -> one; _ -> makeAtlasMap 2 selected
  in if length selected /= count then [] else
    [bindings <> later | bindings <- matches schema value, later <- matchSegments rest remaining]
  where
    width (Parameter _ _ _) = 1
    width (Ordered entries) = length entries
    width (Unordered entries) = length entries
    width (Concatenated entries) = sum (map width entries)

inputMembers :: InterpretedValue -> Maybe [InterpretedValue]
inputMembers input = case interpretedCanonicalResult input of
  CanonicalMap _ _ -> members
  CanonicalConcatenation _ -> members
  CanonicalSpecification _ _ -> members
  _ -> Nothing
  where
    members = do
      count <- naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap input))
      traverse (interpretedMapValueAt (interpretedMap input) . finiteOrdinal)
        (if count == 0 then [] else [0 .. count - 1])

identifierName :: CanonicalResult -> Maybe String
identifierName result = case result of
  CanonicalIdentifierType name _ -> Just name
  CanonicalAssignment name _ _ -> Just name
  CanonicalSpecification source _ -> identifierName source
  _ -> Nothing

-- Function domains describe argument pages, not concatenation of the maps
-- represented by each type (Int, Int must be two slots, not overlapping ranges).
parameterDomain :: ParameterSchema -> Either InterpretingError InterpretedValue
parameterDomain schema = case schema of
  Parameter Nothing _ target -> pure target
  Parameter (Just name) optional target ->
    let named = simpleIdentifierTypeValue name target
    in if optional then eitherValue named target else pure named
  Ordered children -> makeAtlasMap 2 <$> traverse parameterDomain children
  Unordered children -> traverse parameterDomain children >>= makeArgumentMap
  Concatenated children -> do
    alternatives <- traverse pages children
    let presentations = map (makeAtlasMap 2 . concat) (sequence alternatives)
    case nubBy (\a b -> interpretedCanonicalResult a == interpretedCanonicalResult b) presentations of
      [] -> pure (makeAtlasMap 0 [])
      first:rest -> foldM eitherValue first rest
  where
    pages (Ordered entries) = (:[]) <$> traverse parameterDomain entries
    pages unordered@(Unordered _) = parameterDomain unordered >>= argumentRows
    pages (Concatenated entries) = map concat . sequence <$> traverse pages entries
    pages entry = (\value -> [[value]]) <$> parameterDomain entry
