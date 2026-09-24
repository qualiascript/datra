-- | Compile function parameter syntax into a default-bearing overload
-- template. Calls and the public overload operators therefore share exactly
-- the same matching rules.
module FunctionArguments
  ( compileParameters
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , parameterValues
  , prepareArguments
  , matchArguments
  ) where

import DatraLanguage.AST
import DatraTypes
import ModuleNames (isPrivateIdentifier)

compileParameters
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError ArgumentSchema
compileParameters evaluate expression =
  case expression of
    IdentifierOperation (IdentifierString name) annotation given ->
      argumentSlotSchema (Just name) False
        <$> evaluate annotation
        <*> traverse evaluate given
    EitherType
        (IdentifierOperation (IdentifierString name) annotation given)
        missing
      | annotation == missing -> do
          if isPrivateIdentifier name
            then Left (FunctionError
              "private parameter names cannot be optional")
            else pure ()
          argumentSlotSchema (Just name) True
            <$> evaluate annotation
            <*> traverse evaluate given
    AtlasMap members -> orderedArgumentSchema 2 <$> traverse recur members
    MapSequence members -> orderedArgumentSchema 2 <$> traverse recur members
    ArgumentMap members -> unorderedArgumentSchema <$> traverse recur members
    MapConcatenation _ _ ->
      concatenatedArgumentSchema <$> traverse recur (flatten expression)
      where
        flatten (MapConcatenation left right) =
          flatten left <> flatten right
        flatten value = [value]
    _ -> argumentSlotSchema Nothing False <$> evaluate expression <*> pure Nothing
  where
    recur = compileParameters evaluate

parameterBindings :: ArgumentSchema -> [(String, InterpretedValue)]
parameterBindings = argumentSchemaBindings

-- | The callable type intentionally excludes defaults. Defaults are behavior
-- of the function value, while its body and signature see the annotation.
parameterDomain
  :: ArgumentSchema
  -> Either InterpretingError InterpretedValue
parameterDomain = argumentSchemaDomain

parameterPositionalDomain :: ArgumentSchema -> InterpretedValue
parameterPositionalDomain = argumentSchemaPositionalDomain

parameterValues
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
parameterValues = argumentSchemaValuesComplete

prepareArguments
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
prepareArguments schema input = do
  fst <$> overloadArgumentSchemaComplete schema input

matchArguments
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
matchArguments schema input = do
  snd <$> overloadArgumentSchemaComplete schema input
