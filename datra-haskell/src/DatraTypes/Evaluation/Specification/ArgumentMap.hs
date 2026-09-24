-- | Deterministic positional matching for argument-map specification.
--
-- Written order wins whenever it is valid. Otherwise a single valid reorder
-- is accepted, while multiple valid reorders are ambiguous. The generic
-- federation selector is injected so this policy remains independent of the
-- recursive composition dispatcher.
module Evaluation.Specification.ArgumentMap
  ( selectArgumentMapMember
  ) where

import BooleanType (DatraBoolean (..))
import Data.List (permutations)
import Evaluation.Federation.Structure
  ( concatenationOperands
  , sequenceOperands
  )
import Evaluation.Map (makeAtlasMap)
import Evaluation.Specification.Decision
import Evaluation.Value

type FederationSelector =
  InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember

selectArgumentMapMember
  :: FederationSelector
  -> InterpretedValue
  -> [InterpretedValue]
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectArgumentMapMember select source writtenMembers alternatives =
  if any isAlternativeMember writtenMembers
    then select source alternatives
    else
      case argumentPermutationDecision select source writtenMembers of
        DecisionProved () ->
          selectPositionalAlternative select source alternatives
        DecisionRefuted -> DecisionRefuted
        DecisionUndecidable -> DecisionUndecidable
  where
    -- Optional slots expand into several internal federation branches. Their
    -- branch count is not an argument-order ambiguity.
    isAlternativeMember member =
      case interpretedForm member of
        EitherForm _ -> True
        _ -> False

selectPositionalAlternative
  :: FederationSelector
  -> InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectPositionalAlternative select source target =
  case interpretedForm target of
    EitherForm alternatives ->
      decideAny
        [ mapDecision
            (EvaluatedEitherMember DatraFalse)
            (selectPositionalAlternative
              select source (evaluatedEitherLeft alternatives))
        , mapDecision
            (EvaluatedEitherMember DatraTrue)
            (selectPositionalAlternative
              select source (evaluatedEitherRight alternatives))
        ]
    _ ->
      case (sourceComponents source, sequenceOperands target) of
        (Just sourceMembers, Just targetMembers)
          | length sourceMembers == length targetMembers ->
              mapDecision
                EvaluatedSequentialAtlasMapMember
                (decideAll
                  (zipWith
                    (selectPositionalSlot select)
                    sourceMembers
                    targetMembers))
        _ -> selectPositionalSlot select source target

selectPositionalSlot
  :: FederationSelector
  -> InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectPositionalSlot select source target =
  case (interpretedForm source, interpretedForm target) of
    ( DependentIdentifierTypeForm _
      , DependentIdentifierTypeForm targetIdentifier
      )
      | privateSimpleIdentifier targetIdentifier -> DecisionRefuted
    (DependentIdentifierTypeForm _, _) -> select source target
    (_, DependentIdentifierTypeForm targetIdentifier) ->
      case evaluatedIdentifierDependency targetIdentifier of
        SimpleIdentifierDependency _ ->
          mapDecision
            EvaluatedDependentIdentifierTypeMember
            (select source (evaluatedIdentifierUnderlying targetIdentifier))
        DependentIdentifierDependency {} -> select source target
    _ -> select source target

argumentPermutationDecision
  :: FederationSelector
  -> InterpretedValue
  -> [InterpretedValue]
  -> Decision ()
argumentPermutationDecision select source writtenMembers =
  case sourceComponents source of
    Nothing ->
      mapDecision
        (const ())
        (select source (makeAtlasMap 2 writtenMembers))
    Just members
      | length members /= length writtenMembers -> DecisionRefuted
      | otherwise ->
          case match members writtenMembers of
            DecisionProved _ -> DecisionProved ()
            _ -> uniqueReorder members
  where
    match members targets =
      decideAll
        (zipWith (selectPositionalSlot select) members targets)
    uniqueReorder members =
      case [ ()
           | reordered <- drop 1 (permutations writtenMembers)
           , DecisionProved _ <- [match members reordered]
           ] of
        [()] -> DecisionProved ()
        []
          | any isUndecidable
              [ match members reordered
              | reordered <- permutations writtenMembers
              ] -> DecisionUndecidable
          | otherwise -> DecisionRefuted
        _ -> DecisionRefuted
    isUndecidable DecisionUndecidable = True
    isUndecidable _ = False

sourceComponents :: InterpretedValue -> Maybe [InterpretedValue]
sourceComponents source =
  case sequenceOperands source of
    Just members -> Just members
    Nothing ->
      case interpretedForm source of
        ConcatenatedMapForm _ _ -> Just (concatenationOperands source)
        _ -> Nothing

privateSimpleIdentifier :: EvaluatedDependentIdentifierType -> Bool
privateSimpleIdentifier identifier =
  case evaluatedIdentifierDependency identifier of
    SimpleIdentifierDependency ('_':_) -> True
    _ -> False
