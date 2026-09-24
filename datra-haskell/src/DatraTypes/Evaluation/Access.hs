-- | Checked access through an evaluated insertion capability.
module Evaluation.Access
  ( namedAccessValue
  , accessValues
  ) where

import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omegaPower
  , ordinalLT
  )
import Data.Bifunctor qualified as Bifunctor
import Evaluation.Error
  ( InterpretingError (..)
  )
import Evaluation.Access.Composition
  ( FederationAccess (..)
  , accessMapFor
  , decideFederationAccess
  )
import Evaluation.Access.Federation
  ( federationIsCoalition
  )
import Evaluation.Access.Specification (accessSpecification)
import Evaluation.Access.Identifier (accessDependentIdentifierType)
import Evaluation.Map (makeAtlasMap)
import Evaluation.Construction (makeAsciiString, makeFormulation)
import Evaluation.Access.RangeSelection
  ( AccessSource (..)
  , DescribedRange (..)
  , accessSelection
  , accessSource
  , describedRangeSemantics
  , evaluatedDescribedRange
  , pureOmegaPowerLevel
  , rangeAccessDescriptions
  )
import Evaluation.Range qualified as RangeEvaluation
import Evaluation.Value
import Evaluation.Arguments (argumentAlternatives, makeDistinctUnion)
import Evaluation.Specification (specifyValues)
import NaturalRange qualified
import MapOperators.AccessOperator
  ( validateAccessSelection )
import Numeric.Natural (Natural)
import SuperEllipsisInsertion
  ( someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  , someSuperEllipsisInsertionRank
  )
import SuperEllipsisRange qualified as Range

accessValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessValues mapValue insertionValue =
  case interpretedForm mapValue of
    ArgumentMapForm _ underlying ->
      traverse (`accessValues` insertionValue) (argumentAlternatives underlying)
        >>= makeDistinctUnion
    FederationSpecificationForm _ _ branches -> do
      selected <- traverse (`accessValues` insertionValue) branches
      source <- makeDistinctUnion (map specificationSource selected)
      target <- makeDistinctUnion (map specificationTarget selected)
      specifyValues source target
    SpecificationForm specification ->
      accessSpecification accessValues specification insertionValue
    AssignmentForm specification ->
      accessSpecification accessValues specification insertionValue
    DependentIdentifierTypeForm identifier ->
      accessDependentIdentifierType mapValue identifier insertionValue
    _ -> accessFederationValues mapValue insertionValue

specificationSource :: InterpretedValue -> InterpretedValue
specificationSource value =
  case interpretedForm value of
    SpecificationForm specification -> evaluatedSpecificationSourceValue specification
    AssignmentForm specification -> evaluatedSpecificationSourceValue specification
    _ -> value

specificationTarget :: InterpretedValue -> InterpretedValue
specificationTarget value =
  case interpretedForm value of
    SpecificationForm specification -> evaluatedSpecificationTarget specification
    AssignmentForm specification -> evaluatedSpecificationTarget specification
    _ -> value

accessFederationValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessFederationValues mapValue insertionValue =
  case decideFederationAccess mapValue insertionValue of
    Left rejection -> Left rejection
    Right (NaturalRangeFederationAccess sourceRange selectionRange) ->
      accessNaturalRanges mapValue sourceRange selectionRange
    Right (NaturalRangeSelectionAccess naturalRange) ->
      accessNaturalRange mapValue naturalRange
    Right EmptyFederationAccess ->
      finishAccess mapValue emptyInterpretedMap
    Right (SingletonFederationAccess insertion) ->
      accessSingleton mapValue insertionValue insertion

accessSingleton
  :: InterpretedValue
  -> InterpretedValue
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError InterpretedValue
accessSingleton mapValue insertionValue insertion = do
  selected <- accessMap (accessMapFor mapValue) insertion
  let source = accessSource mapValue
  case accessSelection insertionValue of
    Just selectionRanges
      | not (valueIsCoalition mapValue)
          && (sourceIsRangeLike source
          || naturalAtOrdinal
              (someSuperEllipsisInsertionOrderType insertion) == Nothing) ->
        finishStaticAccess mapValue selected source selectionRanges
    _ -> finishAccess mapValue selected

accessNaturalRanges
  :: InterpretedValue
  -> EvaluatedNaturalRange
  -> EvaluatedNaturalRange
  -> Either InterpretingError InterpretedValue
accessNaturalRanges mapValue _ selectionRange = do
  selected <- accessNaturalRange mapValue selectionRange
  naturalRangeAccessResult selected

naturalRangeAccessResult
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
naturalRangeAccessResult selected =
  case interpretedSemantics selected of
    MapSemantics 0 _ -> Right selected
    ExplicitSemantics _ value ->
      case naturalAtOrdinal value of
        Just natural -> RangeEvaluation.naturalRangeValue natural natural
        Nothing -> Right selected
    RangeSemantics description ->
      case naturalAtOrdinal (Range.describedRangeStart description) of
        Nothing -> Right selected
        Just start ->
          case Range.describedRangeTarget description of
            Range.PlusSign ->
              RangeEvaluation.naturalRangeUpwardsValue start
            Range.MinusSign ->
              RangeEvaluation.naturalRangeValue start 0
            Range.GivenTarget boundary ->
              case naturalAtOrdinal boundary of
                Nothing -> Right selected
                Just targetBoundary
                  | ordinalLT
                      (Range.describedRangeStart description)
                      boundary ->
                      RangeEvaluation.naturalRangeValue
                        start (targetBoundary - 1)
                  | otherwise ->
                      RangeEvaluation.naturalRangeValue
                        start (targetBoundary + 1)
    _ -> Right selected

accessNaturalRange
  :: InterpretedValue
  -> EvaluatedNaturalRange
  -> Either InterpretingError InterpretedValue
accessNaturalRange mapValue (EvaluatedNaturalRange valueRange) =
  case NaturalRange.naturalSubrangeEllipsisRange selectedRange $ \range ->
      accessWithRange mapValue (EvaluatedRange 1 range) of
    Just result -> result
    Nothing -> finishAccess mapValue emptyInterpretedMap
  where
    sourceOrderType =
      interpretedMapFinalOrderType (accessMapFor mapValue)
    selectedRange =
      case naturalAtOrdinal sourceOrderType of
        Just finiteLimit ->
          NaturalRange.naturalRangeLargestSubrangeBelow
            valueRange finiteLimit
        Nothing -> NaturalRange.naturalRangeFullSubrange valueRange

accessWithRange
  :: InterpretedValue
  -> EvaluatedRange
  -> Either InterpretingError InterpretedValue
accessWithRange mapValue selectionRange = do
  selected <-
    accessMap
      (accessMapFor mapValue)
      (rangeInsertion selectionRange)
  let source = accessSource mapValue
  if not (valueIsCoalition mapValue)
      && (sourceIsRangeLike source
        || naturalAtOrdinal
            (interpretedMapFinalOrderType selected) == Nothing)
    then
      finishStaticAccess
        mapValue
        selected
        source
        [evaluatedDescribedRange selectionRange]
    else finishAccess mapValue selected

finishStaticAccess
  :: InterpretedValue
  -> InterpretedMap
  -> AccessSource
  -> [DescribedRange]
  -> Either InterpretingError InterpretedValue
finishStaticAccess mapValue selected source selectionRanges =
  case sourceFormulationLevel source
      >> pureOmegaPowerLevel (interpretedMapFinalOrderType selected) of
    Just level ->
      Right
        (formulationAccessResult
          (hasTotalAtlasMap mapValue) selected level)
    Nothing -> do
      result <-
        rangeAccessResult
          (hasTotalAtlasMap mapValue)
          selected
          (rangeAccessDescriptions
            (sourceDescribedRanges source)
            selectionRanges)
      maybe (finishAccess mapValue selected) Right result

formulationAccessResult
  :: Bool
  -> InterpretedMap
  -> Natural
  -> InterpretedValue
formulationAccessResult sourceIsTotal selected level =
  makeSingletonInterpretedValue
    (interpretedDatraType template)
    (interpretedForm template)
    (interpretedInsertionCapability template)
    resultMap
    (if sourceIsTotal then TotalInterpretedMap else NonTotalInterpretedMap)
    semantics
  where
    template = makeFormulation level
    semantics = FormulationSemantics level
    resultMap = selected { interpretedMapComponents = [semantics] }

finishAccess
  :: InterpretedValue
  -> InterpretedMap
  -> Either InterpretingError InterpretedValue
finishAccess mapValue selected =
  let semantics =
        MapSemantics
          (interpretedMapPageCardinality selected)
          (interpretedMapComponents selected)
      ordinaryResult =
        case naturalAtOrdinal (interpretedMapFinalOrderType selected) of
          Just cardinality ->
            case selectedValueList cardinality of
              Just values ->
                makeAtlasMap
                  (interpretedMapPageCardinality selected)
                  values
              Nothing -> fallbackResult
          Nothing -> fallbackResult
      fallbackResult =
        makeSingletonInterpretedValue
          structuralDatraType
          MapForm
          NoInsertion
          selected
          (if hasTotalAtlasMap mapValue
            then TotalInterpretedMap
            else NonTotalInterpretedMap)
          semantics
  in pure
    (case interpretedForm mapValue of
      AsciiStringForm _ ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap selected)
      _ -> ordinaryResult)
  where
    selectedValueList 0 = Just []
    selectedValueList cardinality =
      traverse
        (interpretedMapValueAt selected . finiteOrdinal)
        [0 .. cardinality - 1]

valueIsCoalition :: InterpretedValue -> Bool
valueIsCoalition = federationIsCoalition . interpretedAtlasMapFederation

rangeAccessResult
  :: Bool
  -> InterpretedMap
  -> [DescribedRange]
  -> Either InterpretingError (Maybe InterpretedValue)
rangeAccessResult _ _ [] = Right Nothing
rangeAccessResult sourceIsTotal selected describedRanges = do
  ranges <- traverse makeRange describedRanges
  let insertionCapability =
        RangeEvaluation.concatenateRangeCapability ranges
      semanticComponents = map describedRangeSemantics describedRanges
      (rangeForm, resultCapability, semantics) =
        case insertionCapability of
          RejectedInsertion _ ->
            ( MapForm
            , NoInsertion
            , MapSemantics
                (interpretedMapPageCardinality selected)
                semanticComponents
            )
          _ ->
            ( case ranges of
                [valueRange] -> RangeForm valueRange
                _ -> RangeConcatenationForm ranges Nothing
            , insertionCapability
            , case semanticComponents of
                [component] -> component
                _ -> RangeConcatenationSemantics descriptions
            )
  pure . Just $
    makeSingletonInterpretedValue
      structuralDatraType
      rangeForm
      resultCapability
      (selected { interpretedMapComponents = [semantics] })
      (if sourceIsTotal then TotalInterpretedMap else NonTotalInterpretedMap)
      semantics
  where
    descriptions = map describedRangeDescription describedRanges
    makeRange described =
      RangeEvaluation.makeEvaluatedRangeAt
        (describedRangeLevel described)
        (Range.describedRangeStart (describedRangeDescription described))
        (Range.describedRangeTarget (describedRangeDescription described))

hasTotalAtlasMap :: InterpretedValue -> Bool
hasTotalAtlasMap = interpretedValueHasTotalMap

accessMap
  :: InterpretedMap
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError InterpretedMap
accessMap sourceMap insertion
  | sourceOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | insertionOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | otherwise = do
      Bifunctor.first AccessRejected
        (validateAccessSelection
          rankOrderType
          insertionOrderType
          sourceOrderType
          (someSuperEllipsisInsertionPositionAt insertion))
      let selectedValues =
            OrdinalOrderedValues insertionOrderType $ \position -> do
              selectedPosition <-
                someSuperEllipsisInsertionPositionAt insertion position
              ordinalOrderedValueAt sourceValues selectedPosition
          components = selectedComponents selectedValues insertionOrderType
      Right (InterpretedMap 2 selectedValues components)
  where
    sourceValues = interpretedMapFinalValues sourceMap
    sourceOrderType = ordinalOrderedValuesOrderType sourceValues
    insertionOrderType = someSuperEllipsisInsertionOrderType insertion
    rankOrderType = omegaPower (someSuperEllipsisInsertionRank insertion)

    selectedComponents selectedValues orderType =
      case naturalAtOrdinal orderType of
        -- Infinite selections are reconstructed symbolically by accessValues.
        Nothing -> []
        Just cardinality ->
          concatMap
            (maybe []
              (interpretedMapComponents . interpretedMap)
              . ordinalOrderedValueAt selectedValues
              . finiteOrdinal)
            [0 .. cardinality - 1]

-- | Select a named page without discarding its identifier or specification.
-- Inspect argument-map slots directly: permutation expansion is unnecessary
-- when selection is by name, and optional names retain their named branch.
namedAccessValue :: InterpretedValue -> String -> Either InterpretingError InterpretedValue
namedAccessValue source name = do
  selected <- candidates source
  case selected of
    [] -> Left (NamedAccessError ("no field named " <> name))
    [value] -> Right value
    _ -> Left (NamedAccessError ("ambiguous field named " <> name))
  where
    candidates value
      | matchesName (interpretedCanonicalResult value) = Right [value]
      | otherwise = case interpretedForm value of
          DependentIdentifierTypeForm _ -> Right []
          AssignmentForm _ -> Right []
          ArgumentMapForm members _ -> concat <$> traverse candidates members
          EitherForm alternatives -> do
            values <- concat <$> traverse candidates
              [evaluatedEitherLeft alternatives, evaluatedEitherRight alternatives]
            case values of
              [] -> Right []
              _ -> (:[]) <$> makeDistinctUnion values
          FederationSpecificationForm _ _ branches -> do
            values <- traverse (`namedAccessValue` name) branches
            (:[]) <$> makeDistinctUnion values
          SpecificationForm specification -> do
            let original = evaluatedSpecificationSourceValue specification
                target = evaluatedSpecificationTarget specification
            originalField <- namedAccessValue original name
            targetFields <- candidates target
            case targetFields of
              [] -> pure [originalField]
              [targetField] -> (:[]) <$> specifyValues originalField targetField
              _ -> Left (NamedAccessError ("ambiguous field named " <> name))
          ConcatenatedMapForm left right -> (<>) <$> candidates left <*> candidates right
          SequentialMapForm -> pages value
          MapForm -> pages value
          _ -> Right []
    pages value = case naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap value)) of
      Just count -> concat <$> traverse (\index -> case interpretedMapValueAt (interpretedMap value) (finiteOrdinal index) of
          Nothing -> Left (NamedAccessError "field map is not inspectable")
          Just field -> candidates field) (if count == 0 then [] else [0 .. count - 1])
      Nothing -> Left (NamedAccessError "named access requires a finite map")
    matchesName canonical = case canonical of
      CanonicalSimpleIdentifierType actual _ -> actual == name
      CanonicalAssignment actual _ _ -> actual == name
      CanonicalSpecification original _ -> matchesName original
      _ -> False
