-- | Deterministic positional matching for argument-map specification.
--
-- Written order wins whenever it is valid. Otherwise a single valid reorder
-- is accepted, while multiple valid reorders are ambiguous. The generic
-- federation selector is injected so this policy remains independent of the
-- recursive composition dispatcher.
module Evaluation.Specification.ArgumentMap
  ( prepareArgumentMapSource
  , selectArgumentMapMember
  ) where

import BooleanType (DatraBoolean (..))
import Data.List (permutations, sortOn)
import Evaluation.Coalization (coalizeValue)
import DatraOrdinal (Ordinal, addOrdinals, finiteOrdinal)
import Evaluation.Construction (makeExplicit)
import Evaluation.Federation.Structure
  ( concatenationOperands
  , sequenceOperands
  )
import Evaluation.Map (isEmptyMap, makeAtlasMap)
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
    then selectPositionalAlternative
      select reservations source alternatives
    else
      case argumentPermutationDecision select source writtenMembers of
        DecisionProved () ->
          selectPositionalAlternative
            select reservations source alternatives
        DecisionRefuted -> DecisionRefuted
        DecisionUndecidable -> DecisionUndecidable
  where
    reservations = argumentReservations source writtenMembers
    -- Optional slots already expand into the argument map's alternative
    -- federation. Running the explicit permutation validator as well repeats
    -- the same search and can turn branch count into factorial work.
    isAlternativeMember member =
      case interpretedForm member of
        EitherForm _ -> True
        ConcatenatedMapForm _ _ -> True
        _ -> False

prepareArgumentMapSource
  :: FederationSelector
  -> InterpretedValue
  -> [InterpretedValue]
  -> InterpretedValue
  -> InterpretedValue
prepareArgumentMapSource select source writtenMembers underlying =
  case select source underlying of
    DecisionProved _ -> source
    _ -> positionalArgumentSource
      (argumentReservations source writtenMembers)
      source

argumentReservations
  :: InterpretedValue
  -> [InterpretedValue]
  -> [Bool]
argumentReservations source writtenMembers =
  namedReservationFlags sourceMembers targetSlots
  where
    sourceMembers = maybe [source] id (sourceComponents source)
    targetSlots = concatMap
      (argumentTargetSlots
        (addOrdinals
          (interpretedMapFinalOrderType (interpretedMap source))
          (finiteOrdinal 1)))
      writtenMembers

selectPositionalAlternative
  :: FederationSelector
  -> [Bool]
  -> InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectPositionalAlternative select reservations source target =
  case interpretedForm target of
    EitherForm alternatives ->
      decideAny
        [ mapDecision
            (EvaluatedEitherMember DatraFalse)
            (selectPositionalAlternative
              select reservations source (evaluatedEitherLeft alternatives))
        , mapDecision
            (EvaluatedEitherMember DatraTrue)
            (selectPositionalAlternative
              select reservations source (evaluatedEitherRight alternatives))
        ]
    _ ->
      case (sourceComponents source, sequenceOperands target) of
        (Just sourceMembers, Just targetMembers)
          | length sourceMembers == length targetMembers
          , length reservations == length sourceMembers ->
              mapDecision
                EvaluatedSequentialAtlasMapMember
                (decideAll
                  (zipWith3
                    (selectPositionalSlot select)
                    reservations
                    sourceMembers
                    targetMembers))
        _ -> select
          (positionalArgumentSource reservations source)
          target

positionalArgumentSource :: [Bool] -> InterpretedValue -> InterpretedValue
positionalArgumentSource reservations source =
  case sourceComponents source of
    Just members
      | length members == length reservations ->
          makeAtlasMap
            (interpretedMapCardinality (interpretedMap source))
            (zipWith positionalMember reservations members)
    _ -> positionalMember (or reservations) source
  where
    positionalMember reserved member
      | reserved = member
      | Just (_, payload) <- sourceIdentifierParts member = payload
      | otherwise = member

argumentTargetSlots :: Ordinal -> InterpretedValue -> [InterpretedValue]
argumentTargetSlots probe target
  | isEmptyMap target = []
  | otherwise =
      case interpretedForm target of
        ConcatenatedMapForm left right ->
          argumentTargetSlots probe left <> argumentTargetSlots probe right
        CoalizationForm operand ->
          maybe [target] id (sequenceOperands operand)
        DependentSumForm dependent
          | Just access <- evaluatedDependentSumAccess dependent ->
              case access (makeExplicit ComputedOrigin probe) of
                Right projected -> argumentTargetSlots probe projected
                Left _ -> [target]
        _ -> maybe [target] id (sequenceOperands target)

-- The named pass is ordered and consumptive: the first source identifier
-- that is admitted by a remaining target slot claims that slot. Additional
-- occurrences of the same identifier are left for positional matching.
namedReservationFlags
  :: [InterpretedValue]
  -> [InterpretedValue]
  -> [Bool]
namedReservationFlags sources targets = go sources (zip [0 :: Int ..] targets)
  where
    go [] _ = []
    go (source:remainingSources) remainingTargets =
      case removeNamedTarget source remainingTargets of
        Just (_, laterTargets) -> True : go remainingSources laterTargets
        Nothing -> False : go remainingSources remainingTargets

-- Match identifiers first and remove both matched slots. Only the remaining
-- source and target slots participate in the positional pass.
selectSlots
  :: FederationSelector
  -> [InterpretedValue]
  -> [InterpretedValue]
  -> Decision [EvaluatedAtlasMapFederationMember]
selectSlots select sources targets
  | length sources /= length targets = DecisionRefuted
  | otherwise =
      decideAll
        [ decision
        | (_, decision) <- sortOn fst (named <> positional)
        ]
  where
    indexedTargets = zip [0 :: Int ..] targets
    (positionalSources, positionalTargets, named) =
      selectNamed (zip [0 :: Int ..] sources) indexedTargets [] []
    positional = zipWith
      (\(sourceIndex, source) (_, target) ->
        (sourceIndex, selectPositionalSlot select False source target))
      positionalSources
      positionalTargets

    selectNamed [] remaining positionalInputs selected =
      (reverse positionalInputs, remaining, selected)
    selectNamed ((sourceIndex, source):remainingSources) remainingTargets
        positionalInputs selected =
      case removeNamedTarget source remainingTargets of
        Just ((_, target), laterTargets) ->
          selectNamed remainingSources laterTargets positionalInputs
            ( ( sourceIndex
              , selectPositionalSlot select True source target
              ) : selected
            )
        Nothing ->
          selectNamed remainingSources remainingTargets
            ((sourceIndex, source) : positionalInputs) selected

removeNamedTarget
  :: InterpretedValue
  -> [(Int, InterpretedValue)]
  -> Maybe
      ( (Int, InterpretedValue)
      , [(Int, InterpretedValue)]
      )
removeNamedTarget source targets = do
  (sourceIdentifier, _) <- sourceIdentifierParts source
  case break
      (identifierMatchesTarget sourceIdentifier . snd)
      targets of
    (_, []) -> Nothing
    (before, matched:after) -> Just (matched, before <> after)

selectPositionalSlot
  :: FederationSelector
  -> Bool
  -> InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectPositionalSlot select identifierIsReserved source target =
  case interpretedForm target of
    EitherForm alternatives ->
      decideAny
        [ mapDecision
            (EvaluatedEitherMember DatraFalse)
            (selectPositionalSlot
              select identifierIsReserved source
              (evaluatedEitherLeft alternatives))
        , mapDecision
            (EvaluatedEitherMember DatraTrue)
            (selectPositionalSlot
              select identifierIsReserved source
              (evaluatedEitherRight alternatives))
        ]
    _ -> case sourceIdentifierParts source of
      Just (sourceIdentifier, sourcePayload) ->
        case interpretedForm target of
          DependentIdentifierTypeForm targetIdentifier
            | privateSimpleIdentifier targetIdentifier -> DecisionRefuted
            | identifierDependenciesCompatible
                (evaluatedIdentifierDependency sourceIdentifier)
                (evaluatedIdentifierDependency targetIdentifier) ->
                  select source target
            | identifierIsReserved -> DecisionRefuted
            | otherwise ->
                mapDecision
                  EvaluatedDependentIdentifierTypeMember
                  (select sourcePayload
                    (evaluatedIdentifierUnderlying targetIdentifier))
          _
            | identifierIsReserved -> DecisionRefuted
            | otherwise -> select sourcePayload target
      Nothing ->
        case interpretedForm target of
          DependentIdentifierTypeForm targetIdentifier ->
            case evaluatedIdentifierDependency targetIdentifier of
              SimpleIdentifierDependency _ ->
                mapDecision
                  EvaluatedDependentIdentifierTypeMember
                  (select source (evaluatedIdentifierUnderlying targetIdentifier))
              DependentIdentifierDependency {} -> select source target
          _ -> select source target

sourceIdentifierParts
  :: InterpretedValue
  -> Maybe (EvaluatedDependentIdentifierType, InterpretedValue)
sourceIdentifierParts value =
  case interpretedForm value of
    DependentIdentifierTypeForm identifier ->
      Just (identifier, evaluatedIdentifierUnderlying identifier)
    IdentifierStringProjectionForm identifier ->
      Just (identifier, evaluatedIdentifierUnderlying identifier)
    CoalizationForm operand -> do
      (identifier, payload) <- sourceIdentifierParts operand
      pure (identifier, coalizeValue payload)
    AssignmentForm specification -> fromSpecification specification
    SpecificationForm specification -> fromSpecification specification
    _ -> Nothing
  where
    fromSpecification specification = do
      identifier <- identifierOf
        (evaluatedSpecificationTarget specification)
      pure
        ( identifier
        , stripSourceIdentifier
            (evaluatedSpecificationSourceValue specification)
        )
    identifierOf target =
      case interpretedForm target of
        DependentIdentifierTypeForm identifier -> Just identifier
        IdentifierStringProjectionForm identifier -> Just identifier
        _ -> Nothing
    stripSourceIdentifier source =
      case interpretedForm source of
        DependentIdentifierTypeForm identifier ->
          evaluatedIdentifierUnderlying identifier
        IdentifierStringProjectionForm identifier ->
          evaluatedIdentifierUnderlying identifier
        AssignmentForm specification ->
          stripSourceIdentifier (evaluatedSpecificationSourceValue specification)
        SpecificationForm specification ->
          stripSourceIdentifier (evaluatedSpecificationSourceValue specification)
        _ -> source

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
        (selectSlots select [source] writtenMembers)
    Just members
      | length members /= length writtenMembers -> DecisionRefuted
      | otherwise ->
          case match members writtenMembers of
            DecisionProved _ -> DecisionProved ()
            _ -> uniqueReorder members
  where
    match members targets =
      selectSlots select members targets
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
  case interpretedForm source of
    ArgumentMapForm members _ -> Just members
    ConcatenatedMapForm _ _ -> Just (concatenationOperands source)
    _ -> sequenceOperands source

privateSimpleIdentifier :: EvaluatedDependentIdentifierType -> Bool
privateSimpleIdentifier identifier =
  case evaluatedIdentifierDependency identifier of
    SimpleIdentifierDependency ('_':_) -> True
    _ -> False

identifierMatchesTarget
  :: EvaluatedDependentIdentifierType
  -> InterpretedValue
  -> Bool
identifierMatchesTarget source = any
  (identifierDependenciesCompatible
    (evaluatedIdentifierDependency source)
    . evaluatedIdentifierDependency)
  . identifierCandidates

-- Simple identifiers reduce this relation to string equality.  Dependent
-- identifiers use their stable family dependency, which is the identifier
-- component of the structural subfederation rule.  Recurse through candidate
-- constructors without crossing into a nested argument-map scope.
identifierCandidates
  :: InterpretedValue
  -> [EvaluatedDependentIdentifierType]
identifierCandidates value =
  case interpretedForm value of
    DependentIdentifierTypeForm identifier -> [identifier]
    IdentifierStringProjectionForm identifier -> [identifier]
    AssignmentForm specification ->
      identifierCandidates (evaluatedSpecificationTarget specification)
    SpecificationForm specification ->
      identifierCandidates (evaluatedSpecificationTarget specification)
    EitherForm alternatives ->
      identifierCandidates (evaluatedEitherLeft alternatives)
        <> identifierCandidates (evaluatedEitherRight alternatives)
    ConcatenatedMapForm left right ->
      identifierCandidates left <> identifierCandidates right
    ArgumentMapForm members _ -> concatMap identifierCandidates members
    _ -> []
