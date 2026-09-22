-- | Compile-time decision procedure for the specification operator.
module Evaluation.Specification
  ( specifyValues
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  )
import Control.Monad (foldM)
import Evaluation.Error
  ( AtlasMapFederationOperation
      ( AtlasMapFederationSpecification
      , AtlasMapFederationSubfederation
      )
  , AtlasMapFederationRefutation
      ( AtlasMapFederationSpecificationHasNoMatchingMember
      , AtlasMapFederationSubfederationHasMissingMember
      )
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretingError (..)
  )
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , ordinalLT
  )
import Evaluation.Value
import Evaluation.Federation
  ( decidePrimitiveSubfederation
  , selectNaturalRangeMember
  , selectValuedNaturalRangeMember
  )
import Evaluation.Map (concatenateValues)
import NaturalRange qualified
import Numeric.Natural (Natural)
import SuperEllipsisRange qualified as Range

-- | Singleton federations admit their identical total map directly.
-- NaturalRange and ValuedNaturalRange additionally have target-specific
-- decision procedures: NaturalRange members are range Atlases, while
-- ValuedNaturalRange members are individual EllipsisNatural Atlases.
specifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValues source target =
  case interpretedForm source of
    SpecificationForm specification ->
      widenSpecification source specification target
    _ -> specifyTotalAtlasMap source target

specifyTotalAtlasMap
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyTotalAtlasMap source target = do
  totalSource <-
    case interpretedTotalAtlasMap source of
      Just totalMap -> Right totalMap
      Nothing -> Left (ExpectedTotalAtlasMap (interpretedValueKind source))
  case selectFederationMember source target of
    DecisionProved member ->
      Right
        (specifiedValue
          totalSource
          (interpretedSemantics source)
          target
          member)
    DecisionRefuted -> noMatchingMember
    DecisionUndecidable ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))
  where
    noMatchingMember =
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)

-- | Compose a prior specification with inclusion of its whole target
-- federation into a larger target.  Checking only the previously selected
-- member would be weaker: the intermediate object itself must be an Atlas
-- subfederation of the final object.
widenSpecification
  :: InterpretedValue
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
widenSpecification source specification target =
  case decideValueSubfederation
      (evaluatedSpecificationTarget specification)
      target of
    DecisionProved () ->
      Right
        (specifiedValue
          (evaluatedSpecificationSource specification)
          (originalSpecificationSourceSemantics source)
          target
          (evaluatedSpecificationMember specification))
    DecisionRefuted ->
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSubfederationHasMissingMember)
    DecisionUndecidable ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSubfederation))

specifiedValue
  :: InterpretedTotalAtlasMap
  -> ValueSemantics
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
specifiedValue totalSource sourceCanonical target member =
  makeInterpretedValue
    (SpecificationForm
      EvaluatedSpecification
        { evaluatedSpecificationSource = totalSource
        , evaluatedSpecificationTarget = target
        , evaluatedSpecificationMember = member
        })
    NoInsertion
    (interpretedTotalAtlasMapUnderlying totalSource)
    (interpretedAtlasMapFederation target)
    NonTotalInterpretedMap
    (SpecificationSemantics sourceCanonical (interpretedSemantics target))

data Decision proof
  = DecisionProved proof
  | DecisionRefuted
  | DecisionUndecidable

-- | Select a total source map from a target federation. Composite federations
-- follow their retained sequence, expansion, or concatenation construction,
-- delegating leaves to the singleton and primitive procedures used at the top
-- level.
selectFederationMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectFederationMember source target
  | not (interpretedValueHasTotalMap source) = DecisionRefuted
  | otherwise =
      case interpretedAtlasMapFederation target of
        SingletonAtlasMapFederation _
          | interpretedValueHasTotalMap target
              && interpretedCanonicalResult source
                == interpretedCanonicalResult target ->
              DecisionProved
                (EvaluatedSingletonAtlasMapMember
                  (interpretedCanonicalResult source))
          | otherwise -> DecisionRefuted
        PrimitiveAtlasMapFederation
            (NaturalRangeAtlasMapFederation
              (EvaluatedNaturalRange targetRange)) ->
          maybe
            DecisionRefuted
            (DecisionProved . EvaluatedNaturalRangeMember)
            (sourceNaturalSubrange source
              >>= selectNaturalRangeMember targetRange)
        PrimitiveAtlasMapFederation
            (ValuedNaturalRangeAtlasMapFederation
              (EvaluatedValuedNaturalRange targetRange)) ->
          maybe
            DecisionRefuted
            (DecisionProved . EvaluatedValuedNaturalRangeMember)
            (sourceEllipsisNatural source
              >>= selectValuedNaturalRangeMember targetRange)
        SequentialAtlasMapFederation _ ->
          selectSequentialMember source target
        ConcatenatedAtlasMapFederation _ _ ->
          selectConcatenatedMember source target
        ExpansionAtlasMapFederation _ _ ->
          selectExpansionMember source target

selectSequentialMember
  :: InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember
selectSequentialMember source target =
  case (sequenceOperands source, sequenceOperands target) of
    (Just sourceMembers, Just targetMembers)
      | length sourceMembers == length targetMembers ->
          mapDecision
            EvaluatedSequentialAtlasMapMember
            (decideAll
              (zipWith selectFederationMember sourceMembers targetMembers))
    _ -> DecisionRefuted

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

sequenceOperands :: InterpretedValue -> Maybe [InterpretedValue]
sequenceOperands value =
  case interpretedForm value of
    SequentialMapForm -> finiteMapValues value
    _ -> Nothing

expansionOperands
  :: InterpretedValue
  -> Maybe (InterpretedValue, InterpretedValue)
expansionOperands value =
  case interpretedForm value of
    ExpansionMapForm left right -> Just (left, right)
    _ -> Nothing

finiteMapValues :: InterpretedValue -> Maybe [InterpretedValue]
finiteMapValues value = do
  cardinality <-
    naturalAtOrdinal
      (interpretedMapFinalOrderType (interpretedMap value))
  traverse
    (interpretedMapValueAt (interpretedMap value) . finiteOrdinal)
    (finitePositions cardinality)
  where
    finitePositions 0 = []
    finitePositions cardinality = [0 .. cardinality - 1]

concatenationOperands :: InterpretedValue -> [InterpretedValue]
concatenationOperands value =
  case interpretedForm value of
    ConcatenatedMapForm left right ->
      concatenationOperands left <> concatenationOperands right
    _ -> [value]

concatenateGroup :: [InterpretedValue] -> Maybe InterpretedValue
concatenateGroup [] = Nothing
concatenateGroup (first : rest) =
  either (const Nothing) Just (foldM concatenateValues first rest)

decideAll :: [Decision proof] -> Decision [proof]
decideAll decisions
  | any isRefuted decisions = DecisionRefuted
  | any isUndecidable decisions = DecisionUndecidable
  | otherwise = DecisionProved [proof | DecisionProved proof <- decisions]

decideAny :: [Decision proof] -> Decision proof
decideAny decisions =
  case [proof | DecisionProved proof <- decisions] of
    proof : _ -> DecisionProved proof
    []
      | any isUndecidable decisions -> DecisionUndecidable
      | otherwise -> DecisionRefuted

mapDecision :: (left -> right) -> Decision left -> Decision right
mapDecision transform decision =
  case decision of
    DecisionProved proof -> DecisionProved (transform proof)
    DecisionRefuted -> DecisionRefuted
    DecisionUndecidable -> DecisionUndecidable

prependDecision
  :: Decision value
  -> Decision [value]
  -> Decision [value]
prependDecision (DecisionProved value) (DecisionProved values) =
  DecisionProved (value : values)
prependDecision DecisionRefuted _ = DecisionRefuted
prependDecision _ DecisionRefuted = DecisionRefuted
prependDecision _ _ = DecisionUndecidable

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

isRefuted :: Decision proof -> Bool
isRefuted DecisionRefuted = True
isRefuted _ = False

isUndecidable :: Decision proof -> Bool
isUndecidable DecisionUndecidable = True
isUndecidable _ = False

-- | Decide inclusion of evaluated federation constructions. A singleton
-- source reduces to ordinary member selection. Primitive families use their
-- established inclusion procedure, while composite families are checked
-- componentwise after erasing only concatenation associativity.
decideValueSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideValueSubfederation source target
  | interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | otherwise =
      case ( interpretedAtlasMapFederation source
           , interpretedAtlasMapFederation target
           ) of
        ( PrimitiveAtlasMapFederation sourcePrimitive
          , PrimitiveAtlasMapFederation targetPrimitive
          ) ->
            primitiveSubfederationDecision sourcePrimitive targetPrimitive
        (SequentialAtlasMapFederation _, SequentialAtlasMapFederation _) ->
          decidePointwiseSubfederation
            (sequenceOperands source)
            (sequenceOperands target)
        ( ExpansionAtlasMapFederation _ _
          , ExpansionAtlasMapFederation _ _
          ) ->
            decideExpansionSubfederation source target
        ( ConcatenatedAtlasMapFederation _ _
          , ConcatenatedAtlasMapFederation _ _
          ) ->
            decidePointwiseSubfederation
              (Just (concatenationOperands source))
              (Just (concatenationOperands target))
        _ -> DecisionUndecidable

decideExpansionSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideExpansionSubfederation source target =
  case (expansionOperands source, expansionOperands target) of
    (Just (sourceLeft, sourceRight), Just (targetLeft, targetRight)) ->
      mapDecision
        (const ())
        (decideAll
          [ decideValueSubfederation sourceLeft targetLeft
          , decideValueSubfederation sourceRight targetRight
          ])
    _ -> DecisionRefuted

primitiveSubfederationDecision
  :: InterpretedAtlasMapFederationPrimitive
  -> InterpretedAtlasMapFederationPrimitive
  -> Decision ()
primitiveSubfederationDecision source target =
  case decidePrimitiveSubfederation source target of
    AtlasMapFederationProved () -> DecisionProved ()
    AtlasMapFederationRefuted _ -> DecisionRefuted
    AtlasMapFederationUndecidable _ -> DecisionUndecidable

decidePointwiseSubfederation
  :: Maybe [InterpretedValue]
  -> Maybe [InterpretedValue]
  -> Decision ()
decidePointwiseSubfederation
    (Just sourceMembers)
    (Just targetMembers)
  | length sourceMembers == length targetMembers =
      mapDecision
        (const ())
        (decideAll
          (zipWith decideValueSubfederation sourceMembers targetMembers))
decidePointwiseSubfederation _ _ = DecisionRefuted

originalSpecificationSourceSemantics :: InterpretedValue -> ValueSemantics
originalSpecificationSourceSemantics value =
  case interpretedSemantics value of
    SpecificationSemantics source _ -> source
    semantics -> semantics

sourceEllipsisNatural :: InterpretedValue -> Maybe Natural
sourceEllipsisNatural value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in if level == 1 then naturalAtOrdinal ordinalValue else Nothing
    SequentialMapForm -> do
      [member] <- sequenceOperands value
      sourceEllipsisNatural member
    _ -> Nothing

sourceNaturalSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
sourceNaturalSubrange value =
  case interpretedForm value of
    RangeForm valueRange -> rangeSubrange valueRange
    SequentialMapForm
      | interpretedMapPageCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapPageCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    ConcatenatedMapForm _ _
      | interpretedMapPageCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapPageCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    ExpansionMapForm _ _
      | interpretedMapPageCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapPageCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    MapForm
      | interpretedMapPageCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapPageCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    _ -> Nothing

mapSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
mapSubrange value =
  case interpretedSemantics value of
    MapSemantics _ [RangeSemantics description] ->
      describedRangeSubrange 1 description
    MapSemantics _ [ExplicitSemantics level ordinalValue] -> do
      natural <- naturalAtOrdinal ordinalValue
      if level == 1
        then Just (NaturalRange.FiniteNaturalSubrange natural natural)
        else Nothing
    _ -> do
      cardinality <-
        naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap value))
      values <- traverse valueAt (finitePositions cardinality)
      finiteSequenceSubrange values
  where
    valueAt position = do
      member <-
        interpretedMapValueAt
          (interpretedMap value)
          (finiteOrdinal position)
      (level, ordinalValue) <- interpretedExplicitOrdinal member
      if level == 1 then naturalAtOrdinal ordinalValue else Nothing

    finitePositions 0 = []
    finitePositions cardinality = [0 .. cardinality - 1]

rangeSubrange
  :: EvaluatedRange
  -> Maybe NaturalRange.NaturalSubrangeDescription
rangeSubrange valueRange =
  describedRangeSubrange
    (evaluatedRangeLevel valueRange)
    (rangeDescription valueRange)

describedRangeSubrange
  :: Natural
  -> Range.SuperEllipsisRangeDescription
  -> Maybe NaturalRange.NaturalSubrangeDescription
describedRangeSubrange level description
  | level /= 1 = Nothing
  | otherwise = do
      start <- naturalAtOrdinal (Range.describedRangeStart description)
      case Range.describedRangeTarget description of
        Range.PlusSign ->
          Just (NaturalRange.UpwardsNaturalSubrange start)
        Range.MinusSign ->
          Just (NaturalRange.FiniteNaturalSubrange start 0)
        Range.GivenTarget boundary -> do
          finalBoundary <- naturalAtOrdinal boundary
          if boundary == Range.describedRangeStart description
            then Just NaturalRange.EmptyNaturalSubrange
            else if ordinalLT (Range.describedRangeStart description) boundary
              then
                Just
                  (NaturalRange.FiniteNaturalSubrange
                    start (finalBoundary - 1))
              else
                Just
                  (NaturalRange.FiniteNaturalSubrange
                    start (finalBoundary + 1))

finiteSequenceSubrange
  :: [Natural]
  -> Maybe NaturalRange.NaturalSubrangeDescription
finiteSequenceSubrange [] = Just NaturalRange.EmptyNaturalSubrange
finiteSequenceSubrange [value] =
  Just (NaturalRange.FiniteNaturalSubrange value value)
finiteSequenceSubrange values@(first : second : _)
  | second == first + 1 && ascending values =
      Just (NaturalRange.FiniteNaturalSubrange first (last values))
  | first == second + 1 && descending values =
      Just (NaturalRange.FiniteNaturalSubrange first (last values))
  | otherwise = Nothing
  where
    ascending (left : right : rest) =
      right == left + 1 && ascending (right : rest)
    ascending _ = True

    descending (left : right : rest) =
      left == right + 1 && descending (right : rest)
    descending _ = True
