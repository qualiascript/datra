-- | Compile function parameter syntax into the shared, default-bearing
-- argument schema used by both function calls and overload operators.
module Evaluation.FunctionArguments
  ( compileParameters
  , compileParametersWithGenerics
  , compileDependentParameter
  , parameterBindings
  , parameterDomain
  , parameterPositionalDomain
  , prepareArguments
  , matchArguments
  , selectFunctionCandidate
  ) where

import DatraLanguage.AST
import DatraLanguage.Identifier (isPrivateIdentifier)
import Data.Foldable (traverse_)
import Evaluation.Error
  ( FunctionFailure (..)
  , InterpretingError (..)
  , OverloadFailure (..)
  , overloadFailureIsAmbiguous
  )
import Evaluation.Overload
import Evaluation.Value (InterpretedValue)

compileParameters
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Either InterpretingError ArgumentSchema
compileParameters evaluate expressionValue =
  compileParametersWithGenerics [] evaluate expressionValue expressionValue

compileParametersWithGenerics
  :: [GenericBinder Expression]
  -> (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Expression
  -> Either InterpretingError ArgumentSchema
compileParametersWithGenerics generics evaluate written static =
  compileWith False written static
  where
    inferenceBoundary = case written of
      ArgumentativeMap _ -> True
      _ -> False
    compileWith allowPrivateOptional writtenValue staticValue =
      case staticValue of
        parameter
          | Just (name, annotation, given) <- namedParameter parameter ->
          case genericByName name of
            Just binder -> do
              annotationValue <- evaluate annotation
              pure (genericArgumentSlotSchema
                (genericDescriptor binder) annotationValue)
            Nothing ->
              genericEvidenceArgumentSchema (genericReferences writtenValue)
                <$> parameterSlot (Just name) False annotation given
        optional
          | Just (operation, _) <- optionalIdentifierExpression optional
          , Just (name, annotation, given) <- namedParameter operation -> do
              validateOptionalName allowPrivateOptional name True
              case genericByName name of
                Just binder -> do
                  annotationValue <- evaluate annotation
                  pure (genericArgumentSlotSchema
                    (genericDescriptor binder) annotationValue)
                Nothing ->
                  genericEvidenceArgumentSchema (genericReferences writtenValue)
                    <$> parameterSlot (Just name) True annotation given
        AtlasMap staticMembers
          | AtlasMap writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers ->
              orderedArgumentSchema 2
                <$> traverse (uncurry (compileWith True))
                  (zip writtenMembers staticMembers)
        MapSequence staticMembers
          | MapSequence writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers ->
              orderedArgumentSchema 2
                <$> traverse (uncurry (compileWith True))
                  (zip writtenMembers staticMembers)
        ArgumentativeMap staticMembers
          | ArgumentativeMap writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers -> do
              traverse_ validateArgumentativeMapName writtenMembers
              unorderedArgumentSchema
                <$> traverse (uncurry (compileWith False))
                  (zip writtenMembers staticMembers)
        _ -> do
          annotation <- evaluate staticValue
          pure (genericEvidenceArgumentSchema (genericReferences writtenValue)
            (argumentSchemaFromValue annotation))
    genericByName target = findGeneric generics
      where
        findGeneric [] = Nothing
        findGeneric (binder : remaining) =
          let GenericIdentifier (IdentifierString name) _ =
                genericBinderIdentifier binder
          in if name == target then Just binder else findGeneric remaining
    genericDescriptor binder =
      let GenericIdentifier (IdentifierString name) optional =
            genericBinderIdentifier binder
      in GenericArgumentBinder
          { genericArgumentBinderId = genericBinderId binder
          , genericArgumentPolarity = genericBinderPolarity binder
          , genericArgumentName = name
          , genericArgumentOptionalName = optional || not inferenceBoundary
          , genericArgumentInferred =
              inferenceBoundary && isPrivateIdentifier name
          }
    genericReferences expressionValue = nubBinderIds (go expressionValue)
      where
        go current = case current of
          IdentifierReference (IdentifierString name) ->
            maybe [] (pure . genericBinderId) (genericByName name)
          _ -> concatMap go (expressionChildren current)
        nubBinderIds [] = []
        nubBinderIds (binderId : remaining) =
          binderId : nubBinderIds (filter (/= binderId) remaining)
    validateOptionalName allowPrivate name optional
      | optional && not allowPrivate && isPrivateIdentifier name =
          Left (PrivateParameterCannotBeOptional name)
      | otherwise = Right ()
    validateArgumentativeMapName member =
      case member of
        optional
          | Just (operation, _) <- optionalIdentifierExpression optional
          , Just (name, _, _) <- namedParameter operation
          , isPrivateIdentifier name ->
              Left (PrivateParameterCannotBeOptional name)
        _ -> Right ()
    parameterSlot name optional annotation given = do
      annotationValue <- evaluate annotation
      argumentSlotSchema name optional annotationValue
        <$> traverse evaluate given

    namedParameter value = case value of
      DependentArgument
          (IdentifierReference (IdentifierString name)) (Just annotation) ->
        Just (name, annotation, Nothing)
      MapSpecification given
          (DependentArgument
            (IdentifierReference (IdentifierString name)) annotation) ->
        Just (name, maybe given id annotation, Just given)
      _ -> Nothing

compileDependentParameter
  :: String
  -> Bool
  -> InterpretedValue
  -> ArgumentSchema
compileDependentParameter = dependentArgumentSlotSchema

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
