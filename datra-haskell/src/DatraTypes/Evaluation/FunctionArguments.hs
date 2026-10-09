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
import DatraLanguage.Identifier (public)
import Data.Foldable (traverse_)
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
compileParameters evaluate expressionValue =
  compileParametersWithGenerics [] evaluate expressionValue expressionValue

compileParametersWithGenerics
  :: [GenericBinder Expression]
  -> (Expression -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Expression
  -> Either InterpretingError ArgumentSchema
compileParametersWithGenerics generics evaluate written static =
  compileWith False False written static
  where
    inferenceBoundary = case written of
      ArgumentMap _ -> True
      _ -> False
    compile = compileWith False
    compileMember = compileWith True
    compileWith directMember allowPrivateOptional writtenValue staticValue =
      case staticValue of
        ForBinding (IdentifierString name) optional bound -> do
          validateOptionalName allowPrivateOptional name optional
          annotationValue <- evaluate bound
          requireCanonicalTypeAnnotation annotationValue
          case genericByName name of
            Just binder -> pure (genericArgumentSlotSchema
              (genericDescriptor binder) annotationValue)
            Nothing -> pure (dependentArgumentSlotSchema name
              (optional || allowPrivateOptional) annotationValue)
        WithBinding (IdentifierString name) optional bound -> do
          validateOptionalName allowPrivateOptional name optional
          annotationValue <- evaluate bound
          requireCanonicalTypeAnnotation annotationValue
          case genericByName name of
            Just binder -> pure (genericArgumentSlotSchema
              (genericDescriptor binder) annotationValue)
            Nothing -> pure (dependentArgumentSlotSchema name
              (optional || allowPrivateOptional) annotationValue)
        IdentifierOperation (IdentifierString name) annotation given ->
          genericEvidenceArgumentSchema (genericReferences writtenValue)
            <$> parameterSlot (Just name) False annotation given
        optional
          | Just
              (IdentifierOperation (IdentifierString name) annotation given, _)
              <- optionalIdentifierExpression optional -> do
              validateOptionalName allowPrivateOptional name True
              genericEvidenceArgumentSchema (genericReferences writtenValue)
                <$> parameterSlot (Just name) True annotation given
        AtlasMap staticMembers
          | AtlasMap writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers ->
              orderedArgumentSchema 2
                <$> traverse (uncurry (compileMember True))
                  (zip writtenMembers staticMembers)
        MapSequence staticMembers
          | MapSequence writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers ->
              orderedArgumentSchema 2
                <$> traverse (uncurry (compileMember True))
                  (zip writtenMembers staticMembers)
        ArgumentMap staticMembers
          | ArgumentMap writtenMembers <- writtenValue
          , length writtenMembers == length staticMembers -> do
              traverse_ validateArgumentMapName writtenMembers
              unorderedArgumentSchema
                <$> traverse (uncurry (compileMember False))
                  (zip writtenMembers staticMembers)
        MapConcatenation staticMember (AtlasMap []) ->
          genericEvidenceArgumentSchema (genericReferences writtenValue)
            . projectedArgumentSchema <$> evaluate staticMember
        MapConcatenation _ _ ->
          concatenatedArgumentSchema
            <$> traverse
              (uncurry (compile allowPrivateOptional))
              (zip (flatten writtenValue) (flatten staticValue))
          where
            flatten (MapConcatenation left right) =
              flatten left <> flatten right
            flatten value = [value]
        _ -> do
          annotation <- evaluate staticValue
          pure (genericEvidenceArgumentSchema (genericReferences writtenValue)
            (if directMember
              then argumentSlotSchema Nothing False annotation Nothing
              else argumentSchemaFromValue annotation))
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
              inferenceBoundary && not (isPublic name)
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
    isPublic name = not (null (public [(name, ())]))
    validateOptionalName allowPrivate name optional
      | optional && not allowPrivate && not (isPublic name) =
          Left (PrivateParameterCannotBeOptional name)
      | otherwise = Right ()
    validateArgumentMapName member =
      case member of
        ForBinding (IdentifierString name) True _
          | not (isPublic name) ->
              Left (PrivateParameterCannotBeOptional name)
        optional
          | Just (IdentifierOperation (IdentifierString name) _ _, _) <-
              optionalIdentifierExpression optional
          , not (isPublic name) ->
              Left (PrivateParameterCannotBeOptional name)
        _ -> Right ()
    parameterSlot name optional annotation given = do
      annotationValue <- evaluate annotation
      requireCanonicalTypeAnnotation annotationValue
      argumentSlotSchema name optional annotationValue
        <$> traverse evaluate given

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
