-- | Specification for composite Atlas-map federations.
--
-- Every component is selected through 'selectFederationMember', so leaf
-- federation rules are lifted uniformly through sequences, concatenations,
-- and expansions.
module Evaluation.Specification.Composition
  ( selectFederationMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Control.Monad (foldM)
import BooleanType (DatraBoolean (..))
import Evaluation.Federation.Structure
  ( concatenationOperands
  , expansionOperands
  , sequenceOperands
  )
import Evaluation.Map (concatenateValues)
import Evaluation.Specification.ArgumentMap qualified as ArgumentMap
import Evaluation.Specification.Decision
import Evaluation.Specification.Federation
  ( selectAtomicFederationMember
  )
import Evaluation.Specification.String
  ( selectStringFederationMember
  )
import Evaluation.Value

-- | Select a total source map from any target federation. Atomic targets are
-- delegated to the leaf rule table; this module only supplies structural
-- recursion for federation constructors.
selectFederationMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectFederationMember source target
  | ArgumentMapForm members underlying <- interpretedForm target =
      ArgumentMap.selectArgumentMapMember
        selectFederationMember source members underlying
  | ArgumentMapForm _ underlying <- interpretedForm source =
      selectFederationMember underlying target
  | AssignmentForm assignment <- interpretedForm source =
      selectFederationMember
        (evaluatedSpecificationSourceValue assignment)
        target
  | not (interpretedValueHasTotalMap source) = DecisionRefuted
  | otherwise =
      case selectIdentifierMember source target of
        Just decision -> decision
        Nothing ->
          case interpretedForm target of
            EitherForm alternatives ->
              selectEitherMember source alternatives
            _ ->
              case selectStringFederationMember
                  selectFederationMember source target of
                Just decision -> decision
                Nothing ->
                  case selectAtomicFederationMember source target of
                    Just decision -> decision
                    Nothing ->
                      case interpretedAtlasMapFederation target of
                        SequentialAtlasMapFederation _ ->
                          selectSequentialMember source target
                        ConcatenatedAtlasMapFederation _ _ ->
                          selectConcatenatedMember source target
                        ExpansionAtlasMapFederation _ _ ->
                          selectExpansionMember source target
                        SingletonAtlasMapFederation _ -> DecisionUndecidable
                        PrimitiveAtlasMapFederation _ -> DecisionUndecidable

selectEitherMember
  :: InterpretedValue
  -> EvaluatedEither
  -> Decision EvaluatedAtlasMapFederationMember
selectEitherMember source alternatives =
  decideAny
    [ mapDecision
        (EvaluatedEitherMember DatraFalse)
        (selectFederationMember source (evaluatedEitherLeft alternatives))
    , mapDecision
        (EvaluatedEitherMember DatraTrue)
        (selectFederationMember source (evaluatedEitherRight alternatives))
    ]

selectIdentifierMember
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectIdentifierMember source target =
  case interpretedForm target of
    SpecificationForm specification ->
      selectIdentifierMember
        source
        (evaluatedSpecificationTarget specification)
    AssignmentForm specification ->
      selectIdentifierMember
        source
        (evaluatedSpecificationTarget specification)
    _ -> selectDirectIdentifierMember source target

selectDirectIdentifierMember
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectDirectIdentifierMember source target =
  case (interpretedForm source, interpretedForm target) of
    ( DependentIdentifierTypeForm sourceIdentifier
      , DependentIdentifierTypeForm targetIdentifier
      ) ->
        Just (selectMatchingIdentifierMember sourceIdentifier targetIdentifier)
    ( IdentifierStringProjectionForm sourceIdentifier
      , IdentifierStringProjectionForm targetIdentifier
      ) ->
        Just (selectMatchingIdentifierMember sourceIdentifier targetIdentifier)
    _ -> Nothing

selectMatchingIdentifierMember
  :: EvaluatedDependentIdentifierType
  -> EvaluatedDependentIdentifierType
  -> Decision EvaluatedAtlasMapFederationMember
selectMatchingIdentifierMember sourceIdentifier targetIdentifier =
  if sourceString /= targetString
    then DecisionRefuted
    else
      mapDecision
        EvaluatedDependentIdentifierTypeMember
        (selectFederationMember sourceUnderlying targetUnderlying)
  where
    sourceUnderlying = evaluatedIdentifierUnderlying sourceIdentifier
    targetUnderlying = evaluatedIdentifierUnderlying targetIdentifier
    selectedCanonical = interpretedCanonicalResult sourceUnderlying
    sourceString =
      identifierDependencyStringFor
        (evaluatedIdentifierDependency sourceIdentifier)
        selectedCanonical
    targetString =
      identifierDependencyStringFor
        (evaluatedIdentifierDependency targetIdentifier)
        selectedCanonical

selectSequentialMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectSequentialMember source target =
  case (sourceComponents, sequenceOperands target) of
    (Just sourceMembers, Just targetMembers)
      | length sourceMembers == length targetMembers ->
          mapDecision
            EvaluatedSequentialAtlasMapMember
            (decideAll
              (zipWith selectFederationMember sourceMembers targetMembers))
    _ -> DecisionRefuted
  where
    -- Canonical strings may present concrete components by concatenation.
    -- Match the retained operand boundaries against the target sequence;
    -- do not flatten a nested ordered map into its enclosing components.
    sourceComponents =
      case sequenceOperands source of
        Just members -> Just members
        Nothing ->
          case interpretedForm source of
            ConcatenatedMapForm _ _ -> Just (concatenationOperands source)
            _ -> Nothing

selectExpansionMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectExpansionMember source target =
  case (expansionOperands source, expansionOperands target) of
    (Just (sourceLeft, sourceRight), Just (targetLeft, targetRight)) ->
      combineExpansionDecisions
        (selectFederationMember sourceLeft targetLeft)
        (selectFederationMember sourceRight targetRight)
    _ -> DecisionRefuted

selectConcatenatedMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectConcatenatedMember source target =
  mapDecision
    EvaluatedConcatenatedAtlasMapMember
    (selectConcatenationPartitions
      (concatenationOperands source)
      (concatenationOperands target))

selectConcatenationPartitions
  :: [InterpretedValue]
  -> [InterpretedValue]
  -> Decision [EvaluatedAtlasMapFederationMember]
selectConcatenationPartitions [] [] = DecisionProved []
selectConcatenationPartitions _ [] = DecisionRefuted
selectConcatenationPartitions [] _ = DecisionRefuted
selectConcatenationPartitions sourceMembers (target : remainingTargets) =
  decideAny
    [ case concatenateGroup prefix of
        Nothing -> DecisionRefuted
        Just sourceGroup ->
          prependDecision
            (selectFederationMember sourceGroup target)
            (selectConcatenationPartitions suffix remainingTargets)
    | prefixLength <- [1 .. maximumPrefixLength]
    , let (prefix, suffix) = splitAt prefixLength sourceMembers
    ]
  where
    maximumPrefixLength =
      length sourceMembers - length remainingTargets

concatenateGroup :: [InterpretedValue] -> Maybe InterpretedValue
concatenateGroup [] = Nothing
concatenateGroup (first : rest) =
  either (const Nothing) Just (foldM concatenateValues first rest)

combineExpansionDecisions
  :: Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
combineExpansionDecisions
    (DecisionProved left)
    (DecisionProved right) =
      DecisionProved (EvaluatedExpansionAtlasMapMember left right)
combineExpansionDecisions DecisionRefuted _ = DecisionRefuted
combineExpansionDecisions _ DecisionRefuted = DecisionRefuted
combineExpansionDecisions _ _ = DecisionUndecidable
