-- | Semantic range views and symbolic range slicing for map access.
module Evaluation.Access.RangeSelection
  ( DescribedRange (..)
  , AccessSource (..)
  , accessSource
  , accessSelection
  , describedRangeSemantics
  , evaluatedDescribedRange
  , pureOmegaPowerLevel
  , rangeAccessDescriptions
  ) where

import Data.Char (ord)
import Data.Maybe (fromMaybe)
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
import Evaluation.Value
import NaturalRange qualified
import NaturalRange.Interval qualified as NaturalInterval
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand (someSuperEllipsisLevel)
import SuperEllipsisRange qualified as Range
import SuperEllipsisRange.Description qualified as RangeDescription

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
    ValuedNaturalRangeForm _ ->
      case interpretedRangeDescription value of
        Just description ->
          rangeSource [describedRangeFromDescription description]
        Nothing -> rangeSource []
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
        (map semanticAccessSource
          (interpretedMapComponents (interpretedMap value)))
    AsciiStringForm characters ->
      ordinarySource
        (map
          (singletonDescribedRange 1 . finiteOrdinal . fromIntegral . ord)
          characters)
    SpecificationForm _ -> ordinarySource []
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in ordinarySource [singletonDescribedRange level ordinalValue]
  where
    ordinarySource ranges = AccessSource ranges False Nothing
    rangeSource ranges = AccessSource ranges True Nothing

accessSelection :: InterpretedValue -> Maybe [DescribedRange]
accessSelection value =
  case interpretedForm value of
    FormulationForm formulation ->
      Just [formulationDescribedRange (someSuperEllipsisLevel formulation)]
    _ -> map evaluatedDescribedRange <$> valueRanges value

describedRangeSemantics :: DescribedRange -> ValueSemantics
describedRangeSemantics described
  | RangeDescription.rangeDescriptionOrderType description == finiteOrdinal 1 =
      ExplicitSemantics
        (describedRangeLevel described)
        (Range.describedRangeStart description)
  | otherwise = RangeSemantics description
  where
    description = describedRangeDescription described

semanticAccessSource :: ValueSemantics -> AccessSource
semanticAccessSource semantics =
  case semantics of
    ExplicitSemantics level value ->
      ordinarySource [singletonDescribedRange level value]
    FormulationSemantics level ->
      AccessSource
        { sourceDescribedRanges = [formulationDescribedRange level]
        , sourceIsRangeLike = True
        , sourceFormulationLevel = Just level
        }
    RangeSemantics description ->
      rangeSource [describedRangeFromDescription description]
    NaturalRangeSemantics start target ->
      rangeSource [naturalDescribedRange start target]
    ValuedNaturalRangeSemantics start target ->
      rangeSource [naturalDescribedRange start target]
    NaturalTypeSemantics ->
      rangeSource [naturalDescribedRange 0 NaturalRange.UpwardsTarget]
    RangeConcatenationSemantics descriptions ->
      rangeSource (map describedRangeFromDescription descriptions)
    ConcatenationSemantics members ->
      combineAccessSources (map semanticAccessSource members)
    AsciiStringSemantics characters ->
      ordinarySource
        (map
          (singletonDescribedRange 1 . finiteOrdinal . fromIntegral . ord)
          characters)
    MapSemantics _ components ->
      combineAccessSources (map semanticAccessSource components)
    SpecificationSemantics _ _ -> ordinarySource []
  where
    ordinarySource ranges = AccessSource ranges False Nothing
    rangeSource ranges = AccessSource ranges True Nothing

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
    (fromMaybe 1
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
      (Range.GivenTarget (RangeDescription.successorOrdinal value)))

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
      (NaturalInterval.naturalRangeTargetAsSuperEllipsisRangeTarget start target))

pureOmegaPowerLevel :: Ordinal -> Maybe Natural
pureOmegaPowerLevel value =
  case ordinalCoefficients value of
    1 : remaining
      | not (null remaining) && all (== 0) remaining ->
          Just (fromIntegral (length remaining))
    _ -> Nothing

data OrdinalRangeSegment = OrdinalRangeSegment
  { segmentLevel :: Natural
  , segmentStart :: Ordinal
  , segmentLowerBound :: Ordinal
  , segmentUpperBound :: Ordinal
  , segmentOrderType :: Ordinal
  , segmentRankLimit :: Ordinal
  , segmentIsOpen :: Bool
  , segmentDirection :: RangeDescription.RangeDirection
  }

data LocatedOrdinalRangeSegment = LocatedOrdinalRangeSegment
  { locatedSegmentOffset :: Ordinal
  , locatedSegment :: OrdinalRangeSegment
  }

-- | Compose range descriptions symbolically. Every range segment is affine
-- with step one or minus one, so no element-by-element expansion is needed.
rangeAccessDescriptions
  :: [DescribedRange]
  -> [DescribedRange]
  -> [DescribedRange]
rangeAccessDescriptions sourceRanges selectionRanges =
  mergeAdjacentDescriptions
    (concatMap (sliceOrdinalSegment locatedSources) selectionSegments)
  where
    locatedSources = locateSourceSegments (map ordinalSegment sourceRanges)
    selectionSegments = map ordinalSegment selectionRanges

ordinalSegment :: DescribedRange -> OrdinalRangeSegment
ordinalSegment describedRange =
  OrdinalRangeSegment
    { segmentLevel = describedRangeLevel describedRange
    , segmentStart = Range.describedRangeStart description
    , segmentLowerBound = lowerBound
    , segmentUpperBound = upperBound
    , segmentOrderType = RangeDescription.rangeDescriptionOrderType description
    , segmentRankLimit = Range.describedRangeRankLimit description
    , segmentIsOpen = Range.describedRangeTarget description == Range.PlusSign
    , segmentDirection = direction
    }
  where
    description = describedRangeDescription describedRange
    start = Range.describedRangeStart description
    (lowerBound, upperBound) =
      fromMaybe (start, start)
        (RangeDescription.rangeDescriptionImageBounds description)
    direction =
      fromMaybe RangeDescription.AscendingRange
        (RangeDescription.rangeDescriptionDirection description)

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
      segmentDirection selection == RangeDescription.AscendingRange
    orderedSources
      | selectionIsAscending = sources
      | otherwise = reverse sources
    selectionBounds =
      (segmentLowerBound selection, segmentUpperBound selection)

    slice source =
      case intersectBounds selectionBounds (sourcePositionBounds source) of
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
      | otherwise = RangeDescription.ordinalPredecessor upper
    firstValue = sourceValueAt source firstPosition
    target
      | outputAscending && selectionAscending =
          let boundary = sourceValueAt source upper
          in if segmentIsOpen segment
                && boundary == segmentRankLimit segment
              then Range.PlusSign
              else Range.GivenTarget boundary
      | outputAscending =
          Range.GivenTarget (RangeDescription.successorOrdinal finalValue)
      | finiteTail == 0 = Range.MinusSign
      | otherwise =
          Range.GivenTarget
            (addOrdinals finiteBase (finiteOrdinal (finiteTail - 1)))
    outputAscending =
      selectionAscending
        == (segmentDirection segment == RangeDescription.AscendingRange)
    finalPosition
      | selectionAscending = RangeDescription.ordinalPredecessor upper
      | otherwise = lower
    finalValue = sourceValueAt source finalPosition
    (finiteBase, finiteTail) = splitFiniteTail finalValue

sourceValueAt :: LocatedOrdinalRangeSegment -> Ordinal -> Ordinal
sourceValueAt source position =
  case segmentDirection segment of
    RangeDescription.AscendingRange ->
      addOrdinals (segmentStart segment) relativePosition
    RangeDescription.DescendingRange ->
      case naturalAtOrdinal relativePosition of
        Just finiteOffset ->
          RangeDescription.subtractFiniteOrdinal
            (segmentStart segment) finiteOffset
        Nothing -> segmentStart segment
  where
    segment = locatedSegment source
    relativePosition =
      fromMaybe (finiteOrdinal 0)
        (subtractOrdinal (locatedSegmentOffset source) position)

mergeAdjacentDescriptions :: [DescribedRange] -> [DescribedRange]
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
