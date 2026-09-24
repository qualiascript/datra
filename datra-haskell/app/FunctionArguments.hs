-- | Compile function parameter syntax into a default-bearing overload
-- template. Calls and the public overload operators therefore share exactly
-- the same matching rules.
module FunctionArguments
  ( ParameterSchema (..)
  , compileParameters
  , parameterBindings
  , parameterDomain
  , parameterTemplate
  , prepareArguments
  , matchArguments
  ) where

import Control.Monad (foldM)
import Data.List (nubBy)
import DatraLanguage.AST
import DatraTypes

data ParameterSchema
  = Parameter
      (Maybe String)
      Bool
      InterpretedValue
      (Maybe InterpretedValue)
  | Ordered [ParameterSchema]
  | Unordered [ParameterSchema]
  | Concatenated [ParameterSchema]

compileParameters
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError ParameterSchema
compileParameters evaluate expression =
  case expression of
    IdentifierOperation (IdentifierString name) annotation given ->
      Parameter (Just name) False
        <$> evaluate annotation
        <*> traverse evaluate given
    EitherType
        named@(IdentifierOperation (IdentifierString name) annotation _)
        missing
      | annotation == missing -> do
          schema <- compileParameters evaluate named
          case schema of
            Parameter _ _ target defaultValue ->
              Right (Parameter (Just name) True target defaultValue)
            _ -> Left (FunctionError "invalid optional parameter")
    AtlasMap members -> Ordered <$> traverse recur members
    MapSequence members -> Ordered <$> traverse recur members
    ArgumentMap members -> Unordered <$> traverse recur members
    MapConcatenation _ _ ->
      Concatenated <$> traverse recur (flatten expression)
      where
        flatten (MapConcatenation left right) =
          flatten left <> flatten right
        flatten value = [value]
    _ -> Parameter Nothing False <$> evaluate expression <*> pure Nothing
  where
    recur = compileParameters evaluate

parameterBindings :: ParameterSchema -> [(String, InterpretedValue)]
parameterBindings schema =
  case schema of
    Parameter (Just name) _ target _ -> [(name, target)]
    Parameter Nothing _ _ _ -> []
    Ordered children -> concatMap parameterBindings children
    Unordered children -> concatMap parameterBindings children
    Concatenated children -> concatMap parameterBindings children

-- | The callable type intentionally excludes defaults. Defaults are behavior
-- of the function value, while its body and signature see the annotation.
parameterDomain
  :: ParameterSchema
  -> Either InterpretingError InterpretedValue
parameterDomain schema =
  case schema of
    Parameter Nothing _ target _ -> pure target
    Parameter (Just name) optional target _ -> do
      let named = simpleIdentifierTypeValue name target
      if optional then eitherValue named target else pure named
    Ordered children -> makeAtlasMap 2 <$> traverse parameterDomain children
    Unordered children -> traverse parameterDomain children >>= makeArgumentMap
    Concatenated children -> do
      alternatives <- traverse pages children
      let presentations = map (makeAtlasMap 2 . concat) (sequence alternatives)
      case nubBy sameValue presentations of
        [] -> pure (makeAtlasMap 0 [])
        first : rest -> foldM eitherValue first rest
  where
    sameValue left right =
      interpretedCanonicalResult left == interpretedCanonicalResult right
    pages (Ordered entries) = (:[]) <$> traverse parameterDomain entries
    pages unordered@(Unordered _) = parameterDomain unordered >>= argumentRows
    pages (Concatenated entries) =
      map concat . sequence <$> traverse pages entries
    pages entry = (\value -> [[value]]) <$> parameterDomain entry

-- | Preserve defaults and map structure for the ordinary overload operation
-- performed at each call.
parameterTemplate
  :: ParameterSchema
  -> Either InterpretingError InterpretedValue
parameterTemplate schema =
  case schema of
    Parameter Nothing _ target defaultValue ->
      pure (maybe target id defaultValue)
    Parameter (Just name) optional target defaultValue -> do
      present <-
        case defaultValue of
          Nothing -> pure (simpleIdentifierTypeValue name target)
          Just value -> assignIdentifierValues name target value
      if optional then eitherValue present target else pure present
    Ordered children -> makeAtlasMap 2 <$> traverse parameterTemplate children
    Unordered children -> traverse parameterTemplate children >>= makeArgumentMap
    Concatenated [] -> pure (makeAtlasMap 0 [])
    Concatenated (first : remaining) -> do
      initial <- parameterTemplate first
      foldM
        (\left right -> parameterTemplate right >>= concatenateValues left)
        initial
        remaining

prepareArguments
  :: ParameterSchema
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
prepareArguments schema input = do
  template <- parameterTemplate schema
  fst <$> overloadValuesComplete template input

matchArguments
  :: ParameterSchema
  -> InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
matchArguments schema input = do
  template <- parameterTemplate schema
  snd <$> overloadValuesComplete template input
