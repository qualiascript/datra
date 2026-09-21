-- | Checked access through an evaluated insertion capability.
module Evaluation.Access
  ( accessValues
  ) where

import AtlasMapFederation
  ( AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , ordinalCoefficients
  , omegaPower
  , ordinalLT
  , splitFiniteTail
  , subtractOrdinal
  )
import Data.Bifunctor qualified as Bifunctor
import Data.Char (ord)
import DatraLanguage.Diagnostics.Interpreter
  ( AtlasMapFederationOperation (AtlasMapFederationAccess)
  , AtlasMapFederationRefutation
      (AtlasMapFederationAccessHasEmptyCounterexample)
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretingError (..)
  )
import Evaluation.Construction (makeAsciiString, makeFormulation)
import Evaluation.Range qualified as RangeEvaluation
import Evaluation.Value
import NaturalRange qualified
import MapOperators.AccessOperator
  ( validateAccessSelection )
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand (someSuperEllipsisLevel)
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
  case (naturalRangeFederation mapValue,
        naturalRangeFederation insertionValue) of
    (Just sourceRange, Just selectionRange) ->
      accessNaturalRanges mapValue sourceRange selectionRange
    (Nothing, Just naturalRange)
      | atlasMapFederationExpressionIsSingleton
          (interpretedAtlasMapFederation mapValue) ->
          accessNaturalRange mapValue naturalRange
      | otherwise -> undecidableFederationAccess
    (_, Nothing) -> do
      insertion <- requireInsertion insertionValue
      if someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0
        then finishAccess mapValue emptyInterpretedMap
        else case naturalRangeFederation mapValue of
          Just _ ->
            Left
              (AtlasMapFederationOperationRefuted
                AtlasMapFederationAccessHasEmptyCounterexample)
          Nothing
            | atlasMapFederationExpressionIsSingleton
                (interpretedAtlasMapFederation mapValue) ->
                accessSingleton mapValue insertionValue insertion
            | otherwise -> undecidableFederationAccess

naturalRangeFederation
  :: InterpretedValue
  -> Maybe EvaluatedNaturalRange
naturalRangeFederation value =
  case interpretedAtlasMapFederation value of
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation naturalRange) ->
      Just naturalRange
    _ -> Nothing

undecidableFederationAccess
  :: Either InterpretingError InterpretedValue
undecidableFederationAccess =
  Left
    (AtlasMapFederationOperationUndecidable
      (NoAtlasMapFederationDecisionProcedure AtlasMapFederationAccess))

accessSingleton
  :: InterpretedValue
  -> InterpretedValue
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError InterpretedValue
accessSingleton mapValue insertionValue insertion = do
  selected <- accessMap (interpretedMap mapValue) insertion
  let source = accessSource mapValue
  case accessSelection insertionValue of
    Just selectionRanges
      | sourceIsRangeLike source
          || naturalAtOrdinal
              (someSuperEllipsisInsertionOrderType insertion) == Nothing ->
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
  case interpretedCanonicalResult selected of
    CanonicalMap 0 _ -> Right selected
    CanonicalExplicit _ value ->
      case naturalAtOrdinal value of
        Just natural -> RangeEvaluation.naturalRangeValue natural natural
        Nothing -> Right selected
    CanonicalRange description ->
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
  let source = accessSource mapValue
  if sourceIsRangeLike source
      || naturalAtOrdinal
          (interpretedMapFinalOrderType selected) == Nothing
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
  template
    { interpretedMap =
        selected { interpretedMapComponents = [canonical] }
    , interpretedAtlasMapFederation =
        SingletonAtlasMapFederation
          (selected { interpretedMapComponents = [canonical] })
    , interpretedTotalAtlasMap =
        if sourceIsTotal
          then
            Just
              (InterpretedTotalAtlasMap
                (selected { interpretedMapComponents = [canonical] }))
          else Nothing
    }
  where
    template = makeFormulation level
    canonical = CanonicalFormulation level

finishAccess
  :: InterpretedValue
  -> InterpretedMap
  -> Either InterpretingError InterpretedValue
finishAccess mapValue selected =
  let canonical =
        CanonicalMap
          (interpretedMapCardinality selected)
          (interpretedMapComponents selected)
      ordinaryResult =
        InterpretedValue
          { interpretedForm = MapForm
          , interpretedInsertionCapability = NoInsertion
          , interpretedMap = selected
          , interpretedAtlasMapFederation =
              SingletonAtlasMapFederation selected
          , interpretedTotalAtlasMap =
              if hasTotalAtlasMap mapValue
                then Just (InterpretedTotalAtlasMap selected)
                else Nothing
          , interpretedCanonicalResult = canonical
          }
  in pure
    (case interpretedForm mapValue of
      AsciiStringForm _ ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap selected)
      _ -> ordinaryResult)

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
      canonicalComponents = map describedRangeCanonical describedRanges
      (rangeForm, resultCapability, canonical) =
        case insertionCapability of
          RejectedInsertion _ ->
            ( MapForm
            , NoInsertion
            , CanonicalMap
                (interpretedMapCardinality selected)
                canonicalComponents
            )
          _ ->
            ( case ranges of
                [valueRange] -> RangeForm valueRange
                _ -> RangeConcatenationForm ranges
            , insertionCapability
            , case canonicalComponents of
                [component] -> component
                _ -> CanonicalRangeConcatenation descriptions
            )
  pure . Just $
    InterpretedValue
      { interpretedForm = rangeForm
      , interpretedInsertionCapability = resultCapability
      , interpretedMap =
          selected { interpretedMapComponents = [canonical] }
      , interpretedAtlasMapFederation =
          SingletonAtlasMapFederation
            (selected { interpretedMapComponents = [canonical] })
      , interpretedTotalAtlasMap =
          if sourceIsTotal
            then
              Just
                (InterpretedTotalAtlasMap
                  (selected { interpretedMapComponents = [canonical] }))
            else Nothing
      , interpretedCanonicalResult = canonical
      }
  where
    descriptions = map describedRangeDescription describedRanges
    makeRange described =
      RangeEvaluation.makeEvaluatedRangeAt
        (describedRangeLevel described)
        (Range.describedRangeStart (describedRangeDescription described))
        (Range.describedRangeTarget (describedRangeDescription described))

hasTotalAtlasMap :: InterpretedValue -> Bool
hasTotalAtlasMap = maybe False (const True) . interpretedTotalAtlasMap

describedRangeCanonical :: DescribedRange -> CanonicalResult
describedRangeCanonical described
  | rangeOrderType description == finiteOrdinal 1 =
      CanonicalExplicit
        (describedRangeLevel described)
        (Range.describedRangeStart description)
  | otherwise = CanonicalRange description
  where
    description = describedRangeDescription described

data DescribedRange = DescribedRange
  { describedRangeLevel :: Natural
  , describedRangeDescription :: Range.SuperEllipsisRangeDescription
  }

data AccessSource = AccessSource
  { sourceDescribedRanges :: [DescribedRange]
  , sourceIsRangeLike :: Bool
  , sourceFormulationLevel :: Maybe Natural
  }

accessSource :: InterpretedValue -> AccessSource
accessSource value =
  case interpretedForm value of
    RangeForm valueRange ->
      rangeSource [evaluatedDescribedRange valueRange]
    NaturalRangeForm valueRange ->
      rangeSource
        [evaluatedDescribedRange
          (naturalRangeAsEvaluatedRange valueRange)]
    RangeConcatenationForm ranges ->
      rangeSource (map evaluatedDescribedRange ranges)
    FormulationForm formulation ->
      let level = someSuperEllipsisLevel formulation
      in AccessSource
          { sourceDescribedRanges = [formulationDescribedRange level]
          , sourceIsRangeLike = True
          , sourceFormulationLevel = Just level
          }
    MapForm ->
      combineAccessSources
        (map canonicalAccessSource
          (interpretedMapComponents (interpretedMap value)))
    AsciiStringForm characters ->
      AccessSource
        { sourceDescribedRanges =
            map
              (singletonDescribedRange 1 . finiteOrdinal . fromIntegral . ord)
              characters
        , sourceIsRangeLike = False
        , sourceFormulationLevel = Nothing
        }
    SpecificationForm _ ->
      AccessSource
        { sourceDescribedRanges = []
        , sourceIsRangeLike = False
        , sourceFormulationLevel = Nothing
        }
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in AccessSource
          { sourceDescribedRanges =
              [singletonDescribedRange level ordinalValue]
          , sourceIsRangeLike = False
          , sourceFormulationLevel = Nothing
          }
  where
    rangeSource ranges =
      AccessSource
        { sourceDescribedRanges = ranges
        , sourceIsRangeLike = True
        , sourceFormulationLevel = Nothing
        }

accessSelection :: InterpretedValue -> Maybe [DescribedRange]
accessSelection value =
  case interpretedForm value of
    FormulationForm formulation ->
      Just [formulationDescribedRange (someSuperEllipsisLevel formulation)]
    _ -> map evaluatedDescribedRange <$> valueRanges value

canonicalAccessSource :: CanonicalResult -> AccessSource
canonicalAccessSource canonical =
  case canonical of
    CanonicalExplicit level value ->
      ordinarySource [singletonDescribedRange level value]
    CanonicalFormulation level ->
      AccessSource
        { sourceDescribedRanges = [formulationDescribedRange level]
        , sourceIsRangeLike = True
        , sourceFormulationLevel = Just level
        }
    CanonicalRange description ->
      rangeSource [describedRangeFromDescription description]
    CanonicalNaturalRange start target ->
      rangeSource [naturalDescribedRange start target]
    CanonicalRangeConcatenation descriptions ->
      rangeSource (map describedRangeFromDescription descriptions)
    CanonicalConcatenation members ->
      combineAccessSources (map canonicalAccessSource members)
    CanonicalAsciiString characters ->
      ordinarySource
        (map
          (singletonDescribedRange 1 . finiteOrdinal . fromIntegral . ord)
          characters)
    CanonicalMap _ components ->
      combineAccessSources (map canonicalAccessSource components)
    CanonicalSpecification _ _ -> ordinarySource []
  where
    ordinarySource ranges =
      AccessSource ranges False Nothing
    rangeSource ranges =
      AccessSource ranges True Nothing

combineAccessSources :: [AccessSource] -> AccessSource
combineAccessSources sources =
  AccessSource
    { sourceDescribedRanges = concatMap sourceDescribedRanges sources
    , sourceIsRangeLike = all sourceIsRangeLike sources
    , sourceFormulationLevel =
        case sources of
          [source] -> sourceFormulationLevel source
          _ -> Nothing
    }

evaluatedDescribedRange :: EvaluatedRange -> DescribedRange
evaluatedDescribedRange valueRange =
  DescribedRange
    (evaluatedRangeLevel valueRange)
    (rangeDescription valueRange)

describedRangeFromDescription
  :: Range.SuperEllipsisRangeDescription
  -> DescribedRange
describedRangeFromDescription description =
  DescribedRange
    (maybe 1 id
      (pureOmegaPowerLevel (Range.describedRangeRankLimit description)))
    description

formulationDescribedRange :: Natural -> DescribedRange
formulationDescribedRange level =
  DescribedRange
    level
    (Range.SuperEllipsisRangeDescription
      rankLimit
      (finiteOrdinal 0)
      (Range.GivenTarget rankLimit))
  where
    rankLimit = omegaPower level

singletonDescribedRange :: Natural -> Ordinal -> DescribedRange
singletonDescribedRange level value =
  DescribedRange
    level
    (Range.SuperEllipsisRangeDescription
      (omegaPower level)
      value
      (Range.GivenTarget (successorOrdinal value)))

naturalDescribedRange
  :: Natural
  -> NaturalRange.NaturalRangeTarget
  -> DescribedRange
naturalDescribedRange start target =
  DescribedRange
    1
    (Range.SuperEllipsisRangeDescription
      (omegaPower 1)
      (finiteOrdinal start)
      (case target of
        NaturalRange.UpwardsTarget -> Range.PlusSign
        NaturalRange.FiniteNaturalTarget final
          | start <= final -> Range.GivenTarget (finiteOrdinal (final + 1))
          | final == 0 -> Range.MinusSign
          | otherwise -> Range.GivenTarget (finiteOrdinal (final - 1))))

pureOmegaPowerLevel :: Ordinal -> Maybe Natural
pureOmegaPowerLevel value =
  case ordinalCoefficients value of
    1 : remaining
      | not (null remaining) && all (== 0) remaining ->
          Just (fromIntegral (length remaining))
    _ -> Nothing

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
  :: [DescribedRange]
  -> [DescribedRange]
  -> [DescribedRange]
rangeAccessDescriptions sourceRanges selectionRanges =
  let locatedSources = locateSourceSegments sourceSegments
      selectedDescriptions =
        concatMap (sliceOrdinalSegment locatedSources) selectionSegments
  in mergeAdjacentDescriptions selectedDescriptions
  where
    sourceSegments = map ordinalSegment sourceRanges
    selectionSegments = map ordinalSegment selectionRanges

ordinalSegment :: DescribedRange -> OrdinalRangeSegment
ordinalSegment describedRange =
  OrdinalRangeSegment
    { segmentLevel = describedRangeLevel describedRange
    , segmentStart = start
    , segmentLowerBound = lowerBound
    , segmentUpperBound = upperBound
    , segmentOrderType = rangeOrderType description
    , segmentRankLimit = Range.describedRangeRankLimit description
    , segmentIsOpen = target == Range.PlusSign
    , segmentDirection = direction
    }
  where
    description = describedRangeDescription describedRange
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

rangeOrderType :: Range.SuperEllipsisRangeDescription -> Ordinal
rangeOrderType description =
  maybe (finiteOrdinal 0) id (subtractOrdinal lowerBound upperBound)
  where
    start = Range.describedRangeStart description
    (lowerBound, upperBound) =
      case Range.describedRangeTarget description of
        Range.GivenTarget boundary
          | ordinalLT boundary start ->
              (successorOrdinal boundary, successorOrdinal start)
          | otherwise -> (start, boundary)
        Range.MinusSign ->
          let (base, _) = splitFiniteTail start
          in (base, successorOrdinal start)
        Range.PlusSign ->
          (start, Range.describedRangeRankLimit description)

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
        -- Infinite selections are reconstructed symbolically by accessValues.
        Nothing -> []
        Just cardinality ->
          concatMap
            (maybe []
              (interpretedMapComponents . interpretedMap)
              . ordinalOrderedValueAt selectedValues
              . finiteOrdinal)
            [0 .. cardinality - 1]
