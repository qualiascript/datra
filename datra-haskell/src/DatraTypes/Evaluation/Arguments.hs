-- | Argument maps are unions of ordered maps. Distribute optional names and
-- other Either slots before permuting, so repeated unnamed alternatives are
-- identified instead of being assigned artificial distinguishing tags.
module Evaluation.Arguments
  ( argumentRows
  , overloadArgumentRows
  , functionArgumentValue
  , argumentPresentations
  , makeArgumentMap
  , makeArgumentMapPreservingSingleton
  , argumentSourceHasConcreteMembers
  , makeDistinctUnion
  , argumentAlternatives
  ) where

import Control.Monad (foldM)
import Data.List (nubBy, permutations)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( FunctionFailure (..)
  , InterpretingError (FunctionEvaluationFailed)
  )
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Map (makeAtlasMap, hasConcreteSource, concatenateValues)
import Evaluation.Coalization (valueIsCoalition)
import Evaluation.Value

makeArgumentMap :: [InterpretedValue] -> Either InterpretingError InterpretedValue
makeArgumentMap [] = Right (makeAtlasMap 0 [])
makeArgumentMap [value] = Right value
makeArgumentMap members = makeArgumentMapPreservingSingleton members

-- Surface argument-map syntax retains its written singleton slot so matching
-- can distinguish its candidate name. Internal reconstruction keeps the
-- historical scalar result of 'makeArgumentMap'.
makeArgumentMapPreservingSingleton
  :: [InterpretedValue]
  -> Either InterpretingError InterpretedValue
makeArgumentMapPreservingSingleton [] = Right (makeAtlasMap 0 [])
makeArgumentMapPreservingSingleton originalMembers = do
  union <- makeDistinctUnion
    [ makeAtlasMap 2 ordering
    | choices <- sequence (map argumentAlternatives members)
    , ordering <- permutations choices
    ]
  pure
    (makeInterpretedValue
      (composedStructuralDatraType
        (map interpretedDatraType members))
      (ArgumentMapForm members union)
      NoInsertion
      (interpretedMap union)
      (interpretedAtlasMapFederation union)
      (if interpretedValueHasTotalMap union
        then TotalInterpretedMap else NonTotalInterpretedMap)
      (ArgumentMapSemantics
        (all totalPage members) (map interpretedSemantics members)))
  where
    members = concatMap flattenFiniteConcatenation originalMembers
    totalPage member =
      hasConcreteSource member || valueIsCoalition member

argumentSourceHasConcreteMembers :: InterpretedValue -> Bool
argumentSourceHasConcreteMembers value =
  case interpretedForm value of
    ArgumentMapForm members _ ->
      all hasConcreteSource members
    DependentIdentifierTypeForm identifier ->
      hasConcreteSource (evaluatedIdentifierUnderlying identifier)
    IdentifierStringProjectionForm identifier ->
      hasConcreteSource (evaluatedIdentifierUnderlying identifier)
    CoalizationForm operand -> argumentSourceHasConcreteMembers operand
    _ -> hasConcreteSource value

flattenFiniteConcatenation :: InterpretedValue -> [InterpretedValue]
flattenFiniteConcatenation value =
  case interpretedForm value of
    ConcatenatedMapForm _ _
      | not (containsDependentFamily value)
      , Right [row] <- argumentRows value -> row
    _ -> [value]
  where
    containsDependentFamily current =
      case interpretedForm current of
        DependentSumForm _ -> True
        EitherForm alternatives ->
          containsDependentFamily (evaluatedEitherLeft alternatives)
            || containsDependentFamily (evaluatedEitherRight alternatives)
        ConcatenatedMapForm left right ->
          containsDependentFamily left || containsDependentFamily right
        CoalizationForm operand -> containsDependentFamily operand
        _ -> False

-- The existing Either constructor still checks separation between different
-- members. Only identical alternatives are removed here.
makeDistinctUnion
  :: [InterpretedValue] -> Either InterpretingError InterpretedValue
makeDistinctUnion values =
  case nubBy sameValue (concatMap argumentAlternatives values) of
    [] -> Right (makeAtlasMap 0 [])
    first : rest -> foldM makeEitherValue first rest
  where
    sameValue left right =
      interpretedSemanticResult left == interpretedSemanticResult right

argumentAlternatives :: InterpretedValue -> [InterpretedValue]
argumentAlternatives value =
  case interpretedForm value of
    EitherForm alternatives ->
      argumentAlternatives (evaluatedEitherLeft alternatives)
        <> argumentAlternatives (evaluatedEitherRight alternatives)
    _ -> [value]

-- An assigned optional has already selected its present branch. Treating its
-- missing annotation as another supplied argument makes a value produced by
-- @<<@ ambiguous when passed straight into the corresponding function.
concreteOptionalArgument :: InterpretedValue -> Maybe InterpretedValue
concreteOptionalArgument value = do
  alternatives <-
    case interpretedForm value of
      EitherForm evaluated -> Just evaluated
      _ -> Nothing
  let present = evaluatedEitherLeft alternatives
      missing = evaluatedEitherRight alternatives
  case interpretedSemanticResult present of
    CanonicalAssignment _ annotation _
      | annotation == interpretedSemanticResult missing -> Just present
    _ -> Nothing

argumentInputAlternatives :: InterpretedValue -> [InterpretedValue]
argumentInputAlternatives value =
  case concreteOptionalArgument value of
    Just present -> [present]
    Nothing ->
      case interpretedForm value of
        EitherForm alternatives ->
          argumentInputAlternatives (evaluatedEitherLeft alternatives)
            <> argumentInputAlternatives (evaluatedEitherRight alternatives)
        _ -> [value]

argumentPresentations :: InterpretedValue -> Either InterpretingError [InterpretedValue]
argumentPresentations value = case interpretedForm value of
  ArgumentMapForm _ underlying -> pure (argumentAlternatives underlying)
  EitherForm _ -> pure (argumentAlternatives value)
  ConcatenatedMapForm left right -> do
    lefts <- argumentPresentations left
    rights <- argumentPresentations right
    sequence [concatenateValues a b | a <- lefts, b <- rights]
  FederationSpecificationForm _ _ branches -> pure branches
  _ -> pure [value]


argumentRows :: InterpretedValue -> Either InterpretingError [[InterpretedValue]]
argumentRows value = case interpretedForm value of
  ConcatenatedMapForm left right -> do
    lefts <- concatenationOperandRows left
    rights <- concatenationOperandRows right
    pure [a <> b | a <- lefts, b <- rights]
  ArgumentMapForm _ underlying ->
    concat <$> traverse argumentRows (argumentInputAlternatives underlying)
  EitherForm _ ->
    concat <$> traverse argumentRows (argumentInputAlternatives value)
  SequentialMapForm -> (:[]) <$> pages
  MapForm -> (:[]) <$> pages
  SpecificationForm _ -> (:[]) <$> pages
  _ -> pure [[value]]
  where
    pages = case naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap value)) of
      Nothing -> Left (FunctionEvaluationFailed
        FunctionArgumentsRequireFinitePages)
      Just count -> traverse (\position -> maybe
          (Left (FunctionEvaluationFailed
            (FunctionArgumentPageUnavailable position)))
          Right
          (interpretedMapValueAt (interpretedMap value) (finiteOrdinal position)))
        (if count == 0 then [] else [0 .. count - 1])

concatenationOperandRows
  :: InterpretedValue
  -> Either InterpretingError [[InterpretedValue]]
concatenationOperandRows value =
  case interpretedForm value of
    CoalizationForm operand -> argumentRows operand
    _ -> argumentRows value

-- | Overload matching preserves ordinary argument rows but turns the tagged
-- skip sentinel into an explicit positional hole. Its rank-zero payload is
-- never inspected here, so a literal @(...) ^ 0@ remains a supplied value.
overloadArgumentRows
  :: InterpretedValue
  -> Either InterpretingError [[Maybe InterpretedValue]]
overloadArgumentRows value =
  map (map supplied) <$> argumentRows value
  where
    supplied member =
      case interpretedForm member of
        SkipForm _ -> Nothing
        _ -> Just member

functionArgumentValue :: InterpretedValue -> Either InterpretingError InterpretedValue
functionArgumentValue value = case interpretedForm value of
  ConcatenatedMapForm _ _ -> argumentRows value >>= makeDistinctUnion . map (makeAtlasMap 2)
  _ -> pure value
