-- | Checked access through an evaluated insertion capability.
module Evaluation.Access
  ( accessValues
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omegaPower
  , ordinalLT
  , splitFiniteTail
  , subtractOrdinal
  )
import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.Diagnostics.Interpreter (InterpretingError (..))
import Evaluation.Construction (makeAsciiString)
import Evaluation.Range qualified as RangeEvaluation
import Evaluation.Value
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
  case interpretedForm insertionValue of
    NaturalRangeForm naturalRange ->
      accessNaturalRange mapValue naturalRange
    _ -> do
      insertion <- requireInsertion insertionValue
      selected <- accessMap (interpretedMap mapValue) insertion
      case (valueRanges mapValue, valueRanges insertionValue) of
        (Just sourceRanges, Just selectionRanges) -> do
          result <-
            rangeAccessResult selected
              (rangeAccessDescriptions sourceRanges selectionRanges)
          maybe (finishAccess mapValue selected) Right result
        _ -> finishAccess mapValue selected

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
      interpretedMapFinalOrderType (interpretedMap mapValue)
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
      (interpretedMap mapValue)
      (rangeInsertion selectionRange)
  case valueRanges mapValue of
    Just sourceRanges -> do
      result <-
        rangeAccessResult selected
          (rangeAccessDescriptions sourceRanges [selectionRange])
      maybe (finishAccess mapValue selected) Right result
    Nothing -> finishAccess mapValue selected

finishAccess
  :: InterpretedValue
  -> InterpretedMap
  -> Either InterpretingError InterpretedValue
finishAccess mapValue selected =
  let ordinaryResult =
        InterpretedValue
          MapForm
          NoInsertion
          selected
          (CanonicalMap
            (interpretedMapCardinality selected)
            (interpretedMapComponents selected))
  in pure
    (case interpretedForm mapValue of
      AsciiStringForm _ ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap selected)
      _ -> ordinaryResult)

rangeAccessResult
  :: InterpretedMap
  -> [DescribedRange]
  -> Either InterpretingError (Maybe InterpretedValue)
rangeAccessResult _ [] = Right Nothing
rangeAccessResult selected describedRanges = do
  ranges <- traverse makeRange describedRanges
  let rangeForm =
        case ranges of
          [valueRange] -> RangeForm valueRange
          _ -> RangeConcatenationForm ranges
  pure . Just $
    InterpretedValue
      { interpretedForm = rangeForm
      , interpretedInsertionCapability =
          RangeEvaluation.concatenateRangeCapability ranges
      , interpretedMap =
          selected { interpretedMapComponents = [canonical] }
      , interpretedCanonicalResult = canonical
      }
  where
    descriptions = map describedRangeDescription describedRanges
    canonical =
      case descriptions of
        [description] -> CanonicalRange description
        _ -> CanonicalRangeConcatenation descriptions
    makeRange described =
      RangeEvaluation.makeEvaluatedRangeAt
        (describedRangeLevel described)
        (Range.describedRangeStart (describedRangeDescription described))
        (Range.describedRangeTarget (describedRangeDescription described))

data DescribedRange = DescribedRange
  { describedRangeLevel :: Natural
  , describedRangeDescription :: Range.SuperEllipsisRangeDescription
  }

data SegmentDirection = SegmentAscending | SegmentDescending
  deriving (Eq)

data OrdinalRangeSegment = OrdinalRangeSegment
  { segmentLevel :: Natural
  , segmentStart :: Ordinal
  , segmentLowerBound :: Ordinal
  , segmentUpperBound :: Ordinal
  , segmentOrderType :: Ordinal
  , segmentRankLimit :: Ordinal
  , segmentIsOpen :: Bool
  , segmentDirection :: SegmentDirection
  }

data LocatedOrdinalRangeSegment = LocatedOrdinalRangeSegment
  { locatedSegmentOffset :: Ordinal
  , locatedSegment :: OrdinalRangeSegment
  }

-- | Compose range descriptions symbolically.  Every range segment is affine
-- with step one or minus one, so intersections with selection segments remain
-- ranges and no element-by-element expansion is needed.
rangeAccessDescriptions
  :: [EvaluatedRange]
  -> [EvaluatedRange]
  -> [DescribedRange]
rangeAccessDescriptions sourceRanges selectionRanges =
  let locatedSources = locateSourceSegments sourceSegments
      selectedDescriptions =
        concatMap (sliceOrdinalSegment locatedSources) selectionSegments
  in mergeAdjacentDescriptions selectedDescriptions
  where
    sourceSegments = map ordinalSegment sourceRanges
    selectionSegments = map ordinalSegment selectionRanges

ordinalSegment
  :: EvaluatedRange
  -> OrdinalRangeSegment
ordinalSegment evaluatedRange =
  OrdinalRangeSegment
    { segmentLevel = evaluatedRangeLevel evaluatedRange
    , segmentStart = start
    , segmentLowerBound = lowerBound
    , segmentUpperBound = upperBound
    , segmentOrderType =
        someSuperEllipsisInsertionOrderType
          (rangeInsertion evaluatedRange)
    , segmentRankLimit = Range.describedRangeRankLimit description
    , segmentIsOpen = target == Range.PlusSign
    , segmentDirection = direction
    }
  where
    description = rangeDescription evaluatedRange
    start = Range.describedRangeStart description
    target = Range.describedRangeTarget description
    (lowerBound, upperBound, direction) =
      case target of
        Range.GivenTarget boundary
          | ordinalLT boundary start ->
              (successorOrdinal boundary, successorOrdinal start, SegmentDescending)
          | otherwise -> (start, boundary, SegmentAscending)
        Range.MinusSign ->
          let (base, _) = splitFiniteTail start
          in (base, successorOrdinal start, SegmentDescending)
        Range.PlusSign ->
          (start, Range.describedRangeRankLimit description, SegmentAscending)

locateSourceSegments
  :: [OrdinalRangeSegment]
  -> [LocatedOrdinalRangeSegment]
locateSourceSegments = go (finiteOrdinal 0)
  where
    go _ [] = []
    go offset (segment : rest) =
      let orderType = segmentOrderType segment
      in if orderType == finiteOrdinal 0
          then go offset rest
          else LocatedOrdinalRangeSegment offset segment
            : go (addOrdinals offset orderType) rest

sliceOrdinalSegment
  :: [LocatedOrdinalRangeSegment]
  -> OrdinalRangeSegment
  -> [DescribedRange]
sliceOrdinalSegment sources selection
  | segmentOrderType selection == finiteOrdinal 0 = []
  | otherwise = foldMap slice orderedSources
  where
    selectionIsAscending =
      segmentDirection selection == SegmentAscending
    orderedSources
      | selectionIsAscending = sources
      | otherwise = reverse sources
    selectionBounds =
      (segmentLowerBound selection, segmentUpperBound selection)

    slice source =
      case intersectBounds
        selectionBounds
        (sourcePositionBounds source) of
          Nothing -> []
          Just (lower, upper) ->
            [descriptionForSlice source selectionIsAscending lower upper]

sourcePositionBounds
  :: LocatedOrdinalRangeSegment
  -> (Ordinal, Ordinal)
sourcePositionBounds source =
  ( locatedSegmentOffset source
  , addOrdinals
      (locatedSegmentOffset source)
      (segmentOrderType (locatedSegment source))
  )

intersectBounds
  :: (Ordinal, Ordinal)
  -> (Ordinal, Ordinal)
  -> Maybe (Ordinal, Ordinal)
intersectBounds (leftLower, leftUpper) (rightLower, rightUpper)
  | not (ordinalLT lower upper) = Nothing
  | otherwise = Just (lower, upper)
  where
    lower = max leftLower rightLower
    upper = min leftUpper rightUpper

descriptionForSlice
  :: LocatedOrdinalRangeSegment
  -> Bool
  -> Ordinal
  -> Ordinal
  -> DescribedRange
descriptionForSlice source selectionAscending lower upper =
  DescribedRange
    (segmentLevel segment)
    (Range.SuperEllipsisRangeDescription
      (segmentRankLimit segment)
      firstValue
      target)
  where
    segment = locatedSegment source
    firstPosition
      | selectionAscending = lower
      | otherwise = ordinalPredecessor upper
    firstValue = sourceValueAt source firstPosition
    target
      | outputAscending && selectionAscending =
          let boundary = sourceValueAt source upper
          in if segmentIsOpen segment
                && boundary == segmentRankLimit segment
              then Range.PlusSign
              else Range.GivenTarget boundary
      | outputAscending =
          Range.GivenTarget (successorOrdinal finalValue)
      | finiteTail == 0 = Range.MinusSign
      | otherwise =
          Range.GivenTarget
            (addOrdinals finiteBase (finiteOrdinal (finiteTail - 1)))
    outputAscending =
      selectionAscending
        == (segmentDirection segment == SegmentAscending)
    finalPosition
      | selectionAscending = ordinalPredecessor upper
      | otherwise = lower
    finalValue = sourceValueAt source finalPosition
    (finiteBase, finiteTail) = splitFiniteTail finalValue

sourceValueAt :: LocatedOrdinalRangeSegment -> Ordinal -> Ordinal
sourceValueAt source position =
  case segmentDirection segment of
    SegmentAscending -> addOrdinals (segmentStart segment) relativePosition
    SegmentDescending ->
      case naturalAtOrdinal relativePosition of
        Just finiteOffset -> subtractFiniteOrdinal (segmentStart segment) finiteOffset
        Nothing -> segmentStart segment
  where
    segment = locatedSegment source
    relativePosition =
      case subtractOrdinal (locatedSegmentOffset source) position of
        Just value -> value
        Nothing -> finiteOrdinal 0

subtractFiniteOrdinal :: Ordinal -> Natural -> Ordinal
subtractFiniteOrdinal value amount =
  let (base, finiteTail) = splitFiniteTail value
  in addOrdinals base (finiteOrdinal (finiteTail - amount))

ordinalPredecessor :: Ordinal -> Ordinal
ordinalPredecessor value =
  let (base, finiteTail) = splitFiniteTail value
  in if finiteTail == 0
      then value
      else addOrdinals base (finiteOrdinal (finiteTail - 1))

successorOrdinal :: Ordinal -> Ordinal
successorOrdinal value = addOrdinals value (finiteOrdinal 1)

mergeAdjacentDescriptions
  :: [DescribedRange]
  -> [DescribedRange]
mergeAdjacentDescriptions = foldl appendDescription []
  where
    appendDescription [] description = [description]
    appendDescription descriptions description =
      case reverse descriptions of
        [] -> [description]
        previous : reversedPrefix ->
          case Range.analyzeSuperEllipsisRangeDescriptions
            (describedRangeDescription previous)
            (describedRangeDescription description) of
              Range.RangeConcatCanonical merged ->
                let level
                      | Range.describedRangeRankLimit merged
                          == Range.describedRangeRankLimit
                            (describedRangeDescription previous) =
                          describedRangeLevel previous
                      | otherwise = describedRangeLevel description
                in reverse reversedPrefix <> [DescribedRange level merged]
              _ -> descriptions <> [description]

requireInsertion
  :: InterpretedValue
  -> Either InterpretingError SomeSuperEllipsisInsertion
requireInsertion value =
  case interpretedInsertionCapability value of
    NoInsertion ->
      Left (ExpectedInsertionOperand (interpretedValueKind value))
    RejectedInsertion rejection ->
      Left (RangeConcatenationRejected rejection)
    ValidInsertion insertion -> Right insertion

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
        Nothing -> [CanonicalSuperEllipsisInsertion]
        Just cardinality ->
          concatMap
            (maybe []
              (interpretedMapComponents . interpretedMap)
              . ordinalOrderedValueAt selectedValues
              . finiteOrdinal)
            [0 .. cardinality - 1]
