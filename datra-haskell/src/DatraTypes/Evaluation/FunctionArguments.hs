-- | Compile function parameter syntax into the shared, default-bearing
-- argument schema used by both function calls and overload operators.
module Evaluation.FunctionArguments
  ( compileParameters
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , parameterValues
  , prepareArguments
  , matchArguments
  , selectFunctionCandidate
  ) where

import DatraLanguage.AST
import DatraLanguage.Identifier (public)
import Evaluation.Error
  ( FunctionFailure (..)
  , InterpretingError (..)
  , OverloadFailure (..)
  , overloadFailureIsAmbiguous
  )
import Evaluation.Identifier (requireCanonicalTypeAnnotation)
import Evaluation.Overload
import Evaluation.Value (InterpretedValue)

compileParameters
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError ArgumentSchema
compileParameters evaluate expression =
  case expression of
    IdentifierOperation (IdentifierString name) annotation given ->
      parameterSlot (Just name) False annotation given
    EitherType
        (IdentifierOperation (IdentifierString name) annotation given)
        missing
      | annotation == missing -> do
          if not (isPublic name)
            then Left (PrivateParameterCannotBeOptional name)
            else pure ()
          parameterSlot (Just name) True annotation given
    AtlasMap members -> orderedArgumentSchema 2 <$> traverse recur members
    MapSequence members -> orderedArgumentSchema 2 <$> traverse recur members
    ArgumentMap members -> unorderedArgumentSchema <$> traverse recur members
    MapConcatenation _ _ ->
      concatenatedArgumentSchema <$> traverse recur (flatten expression)
      where
        flatten (MapConcatenation left right) =
          flatten left <> flatten right
        flatten value = [value]
    _ ->
      argumentSlotSchema Nothing False
        <$> evaluate expression
        <*> pure Nothing
  where
    isPublic name = not (null (public [(name, ())]))
    recur = compileParameters evaluate
    parameterSlot name optional annotation given = do
      annotationValue <- evaluate annotation
      requireCanonicalTypeAnnotation annotationValue
      argumentSlotSchema name optional annotationValue
        <$> traverse evaluate given

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
prepareArguments schema input =
  fst <$> overloadArgumentSchemaComplete schema input

matchArguments
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError [(String, InterpretedValue)]
matchArguments schema input =
  snd <$> overloadArgumentSchemaComplete schema input

-- | Select one successfully prepared function alternative and normalize the
-- overload failures that are meaningful at the call boundary. Ordinary type
-- mismatches remain a single function-applicability error; ambiguity and an
-- explicit skip of a required argument retain their stronger diagnostics.
selectFunctionCandidate
  :: [(candidate, Either InterpretingError prepared)]
  -> Either InterpretingError (candidate, prepared)
selectFunctionCandidate preparations =
  case
      [ (candidate, prepared)
      | (candidate, Right prepared) <- preparations
      ] of
    [candidate] -> Right candidate
    [] -> Left (normalizedFailure preparations)
    _ -> Left (FunctionEvaluationFailed AmbiguousFunctionSumApplication)
  where
    normalizedFailure attempts
      | any isAmbiguous attempts = FunctionEvaluationFailed
          AmbiguousFunctionArgumentBindings
      | Just failure <- firstCompletionFailure attempts = failure
      | otherwise = FunctionEvaluationFailed
          NoApplicableFunctionAlternative

    isAmbiguous (_, Left (OverloadError failure)) =
      overloadFailureIsAmbiguous failure
    isAmbiguous _ = False

    firstCompletionFailure [] = Nothing
    firstCompletionFailure
        ((_, Left failure@(OverloadError overloadFailure)) : remaining) =
      case overloadFailure of
        OverloadSkippedRequiredSlot -> Just failure
        OverloadMissingRequiredSlot -> Just failure
        _ -> firstCompletionFailure remaining
    firstCompletionFailure (_ : remaining) =
      firstCompletionFailure remaining
