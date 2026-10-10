-- | Deterministic positional matching for argument-map specification.
--
-- Written order wins whenever it is valid. Otherwise a single valid reorder
-- is accepted, while multiple valid reorders are ambiguous. The generic
-- federation selector is injected so this policy remains independent of the
-- recursive composition dispatcher.
module Evaluation.Specification.ArgumentMap
  ( selectArgumentMapMember
  , argumentReservations
  , positionalArgumentSource
  ) where

import BooleanType (DatraBoolean (..))
import Data.List (permutations, sortOn)
import Evaluation.Coalization (coalizeValue)
import Evaluation.Construction (makeAsciiString)
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
  case argumentReservations select source writtenMembers of
    DecisionProved reservations ->
      let selected = selection reservations
      in mapDecision
          (attachPreparedSource reservations)
          selected
    DecisionRefuted -> DecisionRefuted
    DecisionUndecidable -> DecisionUndecidable
  where
    selection reservations =
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
    attachPreparedSource reservations member =
      EvaluatedArgumentMapMember
        (selectedDependentSource
          (positionalArgumentSource reservations source)
          member)
        member
    -- Optional slots already expand into the argument map's alternative
    -- federation. Running the explicit permutation validator as well repeats
    -- the same search and can turn branch count into factorial work.
    isAlternativeMember member =
      case interpretedForm member of
        EitherForm _ -> True
        ConcatenatedMapForm _ _ -> True
        _ -> False

selectedDependentSource
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
selectedDependentSource fallback member =
  case member of
    EvaluatedEitherMember _ selected ->
      selectedDependentSource fallback selected
    EvaluatedDependentIdentifierTypeMember _ selected ->
      selectedDependentSource fallback selected
    EvaluatedDependentSumMember selected -> selected
    _ -> fallback

argumentReservations
  :: FederationSelector
  -> InterpretedValue
  -> [InterpretedValue]
  -> Decision [Bool]
argumentReservations select source writtenMembers =
  namedReservationFlags select sourceMembers targetSlots
  where
    sourceMembers = maybe [source] id (sourceComponents source)
    targetSlots = concatMap argumentTargetSlots writtenMembers

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
      case select source target of
        DecisionProved member -> DecisionProved member
        _ ->
          case sequenceOperands target of
            Just targetMembers
              | length sourceMembers == length targetMembers
              , length reservations == length sourceMembers ->
                  mapDecision EvaluatedSequentialAtlasMapMember
                    (selectSlots select sourceMembers targetMembers)
            Nothing
              | length sourceMembers == 1
              , length reservations == 1 ->
                  singletonSelection
                    (selectSlots select sourceMembers [target])
            _ -> select
              (positionalArgumentSource reservations source)
              target
          where
            sourceMembers = maybe [source] id (sourceComponents source)
            singletonSelection decision = case decision of
              DecisionProved [member] -> DecisionProved member
              DecisionProved _ -> DecisionRefuted
              DecisionRefuted -> DecisionRefuted
              DecisionUndecidable -> DecisionUndecidable

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

argumentTargetSlots :: InterpretedValue -> [InterpretedValue]
argumentTargetSlots target
  | isEmptyMap target = []
  | otherwise =
      case interpretedForm target of
        ConcatenatedMapForm left right ->
          argumentTargetSlots left <> argumentTargetSlots right
        CoalizationForm operand ->
          maybe [target] id (sequenceOperands operand)
        _ -> maybe [target] id (sequenceOperands target)

-- The named pass is ordered and consumptive: the first source identifier
-- that is admitted by a remaining target slot claims that slot. Additional
-- occurrences of the same identifier are left for positional matching.
namedReservationFlags
  :: FederationSelector
  -> [InterpretedValue]
  -> [InterpretedValue]
  -> Decision [Bool]
namedReservationFlags select sources targets =
  go sources (zip [0 :: Int ..] targets)
  where
    go [] _ = DecisionProved []
    go (source:remainingSources) remainingTargets =
      case removeNamedTarget select source remainingTargets of
        DecisionProved (Just (_, laterTargets)) ->
          mapDecision (True :) (go remainingSources laterTargets)
        DecisionProved Nothing ->
          mapDecision (False :) (go remainingSources remainingTargets)
        DecisionRefuted -> DecisionRefuted
        DecisionUndecidable -> DecisionUndecidable

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
      case removeNamedTarget select source remainingTargets of
        DecisionProved (Just ((_, target), laterTargets)) ->
          selectNamed remainingSources laterTargets positionalInputs
            ( ( sourceIndex
              , selectPositionalSlot select True source target
              ) : selected
            )
        DecisionProved Nothing ->
          selectNamed remainingSources remainingTargets
            ((sourceIndex, source) : positionalInputs) selected
        DecisionRefuted ->
          (reverse positionalInputs, remainingTargets,
            (sourceIndex, DecisionRefuted) : selected)
        DecisionUndecidable ->
          (reverse positionalInputs, remainingTargets,
            (sourceIndex, DecisionUndecidable) : selected)

removeNamedTarget
  :: FederationSelector
  -> InterpretedValue
  -> [(Int, InterpretedValue)]
  -> Decision
      (Maybe
        ( (Int, InterpretedValue)
        , [(Int, InterpretedValue)]
        ))
removeNamedTarget select source targets =
  case sourceIdentifierParts source of
    Nothing -> DecisionProved Nothing
    Just (sourceIdentifier, _) -> findTarget sourceIdentifier [] targets
  where
    findTarget _ _ [] = DecisionProved Nothing
    findTarget sourceIdentifier before (target:remaining) =
      case identifierMatchesTarget select sourceIdentifier (snd target) of
        DecisionProved True ->
          DecisionProved (Just (target, reverse before <> remaining))
        DecisionProved False ->
          findTarget sourceIdentifier (target : before) remaining
        DecisionRefuted ->
          findTarget sourceIdentifier (target : before) remaining
        DecisionUndecidable -> DecisionUndecidable

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
        if identifierIsReserved
          then case identifierMatchesTarget select sourceIdentifier target of
            DecisionProved True -> select source target
            DecisionProved False -> DecisionRefuted
            DecisionRefuted -> DecisionRefuted
            DecisionUndecidable -> DecisionUndecidable
          else case interpretedForm target of
            DependentIdentifierTypeForm targetIdentifier
              | privateSimpleIdentifier targetIdentifier -> DecisionRefuted
              | otherwise ->
                  mapDecision
                    (EvaluatedDependentIdentifierTypeMember Nothing)
                    (select sourcePayload
                      (evaluatedIdentifierUnderlying targetIdentifier))
            _ -> select sourcePayload target
      Nothing ->
        case interpretedForm target of
          DependentIdentifierTypeForm targetIdentifier ->
            case evaluatedIdentifierDependency targetIdentifier of
              SimpleIdentifierDependency _ ->
                mapDecision
                  (EvaluatedDependentIdentifierTypeMember Nothing)
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
  :: FederationSelector
  -> EvaluatedDependentIdentifierType
  -> InterpretedValue
  -> Decision Bool
identifierMatchesTarget select source target =
  case map (identifierAdmitsSource select source)
      (identifierCandidates target) of
    [] -> DecisionRefuted
    decisions -> mapDecision (const True) (decideAny decisions)

identifierAdmitsSource
  :: FederationSelector
  -> EvaluatedDependentIdentifierType
  -> EvaluatedDependentIdentifierType
  -> Decision ()
identifierAdmitsSource select source target
  | identifierDependenciesCompatible
      (evaluatedIdentifierDependency source)
      (evaluatedIdentifierDependency target) = DecisionProved ()
  | SimpleIdentifierDependency sourceName <-
      evaluatedIdentifierDependency source
  , Just nameFederation <- evaluatedIdentifierNameFederation target =
      mapDecision
        (const ())
        (select (makeAsciiString sourceName) nameFederation)
  | otherwise = DecisionRefuted

-- Simple identifiers reduce this relation to string equality.  Dependent
-- identifiers use their stable family dependency, which is the identifier
-- component of the structural subfederation rule.  Recurse through candidate
-- constructors without crossing into a nested argument-map scope.
identifierCandidates
  :: InterpretedValue
  -> [EvaluatedDependentIdentifierType]
identifierCandidates value
  | Just dependent <- dependentSumView value =
      identifierCandidates
        (maybe
          (evaluatedDependentSumStaticTarget dependent)
          id
          (evaluatedDependentSumReservationTarget dependent))
  | otherwise =
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
    SequentialMapForm ->
      maybe [] (concatMap identifierCandidates) (sequenceOperands value)
    ConcatenatedMapForm left right ->
      identifierCandidates left <> identifierCandidates right
    CoalizationForm operand -> identifierCandidates operand
    ArgumentMapForm members _ -> concatMap identifierCandidates members
    _ -> []
