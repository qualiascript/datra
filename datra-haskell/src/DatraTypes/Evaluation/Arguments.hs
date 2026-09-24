-- | Argument maps are unions of ordered maps. Distribute optional names and
-- other Either slots before permuting, so repeated unnamed alternatives are
-- identified instead of being assigned artificial distinguishing tags.
module Evaluation.Arguments
  ( argumentRows
  , functionArgumentValue
  , argumentPresentations
  , makeArgumentMap
  , makeDistinctUnion
  , argumentAlternatives
  ) where

import Control.Monad (foldM)
import Data.List (nubBy, permutations)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError (FunctionError))
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Map (makeAtlasMap, hasConcreteSource, concatenateValues)
import Evaluation.Access.Federation (federationIsCoalition)
import Evaluation.Value

makeArgumentMap :: [InterpretedValue] -> Either InterpretingError InterpretedValue
makeArgumentMap [] = Right (makeAtlasMap 0 [])
makeArgumentMap [value] = Right value
makeArgumentMap members = do
  union <- makeDistinctUnion
    [ makeAtlasMap 2 ordering
    | choices <- sequence (map argumentAlternatives members)
    , ordering <- permutations choices
    ]
  pure
    (makeInterpretedValue
      (ArgumentMapForm members union)
      NoInsertion
      (interpretedMap union)
      (interpretedAtlasMapFederation union)
      (if interpretedValueHasTotalMap union
        then TotalInterpretedMap else NonTotalInterpretedMap)
      (ArgumentMapSemantics
        (all totalPage members) (map interpretedSemantics members)))
  where
    totalPage member =
      hasConcreteSource member
        || federationIsCoalition (interpretedAtlasMapFederation member)

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
      interpretedCanonicalResult left == interpretedCanonicalResult right

argumentAlternatives :: InterpretedValue -> [InterpretedValue]
argumentAlternatives value =
  case interpretedForm value of
    EitherForm alternatives ->
      argumentAlternatives (evaluatedEitherLeft alternatives)
        <> argumentAlternatives (evaluatedEitherRight alternatives)
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
    lefts <- argumentRows left
    rights <- argumentRows right
    pure [a <> b | a <- lefts, b <- rights]
  ArgumentMapForm _ underlying -> concat <$> traverse argumentRows (argumentAlternatives underlying)
  EitherForm _ -> concat <$> traverse argumentRows (argumentAlternatives value)
  SequentialMapForm -> (:[]) <$> pages
  MapForm -> (:[]) <$> pages
  SpecificationForm _ -> (:[]) <$> pages
  _ -> pure [[value]]
  where
    pages = case naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap value)) of
      Nothing -> Left (FunctionError "function arguments require finitely many pages")
      Just count -> traverse (\position -> maybe (Left (FunctionError "unavailable argument page")) Right
          (interpretedMapValueAt (interpretedMap value) (finiteOrdinal position)))
        (if count == 0 then [] else [0 .. count - 1])

functionArgumentValue :: InterpretedValue -> Either InterpretingError InterpretedValue
functionArgumentValue value = case interpretedForm value of
  ConcatenatedMapForm _ _ -> argumentRows value >>= makeDistinctUnion . map (makeAtlasMap 2)
  _ -> pure value
