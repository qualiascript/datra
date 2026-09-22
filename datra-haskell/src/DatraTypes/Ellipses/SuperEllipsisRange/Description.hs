-- | Scope-free geometry for super-ellipsis ranges.
--
-- Both proof-bearing ranges and the erased evaluator use this module. Keeping
-- the half-open interval arithmetic here prevents access, concatenation, and
-- diagnostics from developing subtly different range conventions.
module SuperEllipsisRange.Description
  ( SuperEllipsisRangeTarget (..)
  , SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeConcatAnalysis (..)
  , SuperEllipsisRangeConcatError (..)
  , RangeDirection (..)
  , rangeDescriptionDirection
  , rangeDescriptionImageBounds
  , rangeDescriptionOrderType
  , rangeDescriptionIsEmpty
  , rangeDescriptionOverlapBounds
  , analyzeSuperEllipsisRangeDescriptions
  , validateSuperEllipsisRangeDescriptions
  , sameFiniteBase
  , finiteTailDifference
  , successorOrdinal
  , ordinalPredecessor
  , subtractFiniteOrdinal
  ) where

import Data.Maybe (fromMaybe)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , ordinalLT
  , splitFiniteTail
  , subtractOrdinal
  )
import Numeric.Natural (Natural)

data SuperEllipsisRangeTarget
  = GivenTarget Ordinal
  | MinusSign
  | PlusSign
  deriving (Eq, Show)

data SuperEllipsisRangeDescription = SuperEllipsisRangeDescription
  { describedRangeRankLimit :: Ordinal
  , describedRangeStart :: Ordinal
  , describedRangeTarget :: SuperEllipsisRangeTarget
  }
  deriving (Eq, Show)

data SuperEllipsisRangeConcatAnalysis
  = RangeConcatCanonical SuperEllipsisRangeDescription
  | RangeConcatDisjoint
      SuperEllipsisRangeDescription
      SuperEllipsisRangeDescription
  | RangeConcatOverlapping
      SuperEllipsisRangeDescription
      SuperEllipsisRangeDescription
      Ordinal
      Ordinal
  deriving (Eq, Show)

data SuperEllipsisRangeConcatError
  = SuperEllipsisRangesOverlap
      SuperEllipsisRangeDescription
      SuperEllipsisRangeDescription
      Ordinal
      Ordinal
  deriving (Eq, Show)

data RangeDirection = AscendingRange | DescendingRange
  deriving (Eq, Show)

rangeDescriptionDirection
  :: SuperEllipsisRangeDescription
  -> Maybe RangeDirection
rangeDescriptionDirection description =
  case describedRangeTarget description of
    GivenTarget target
      | ordinalLT start target -> Just AscendingRange
      | ordinalLT target start -> Just DescendingRange
      | otherwise -> Nothing
    PlusSign -> Just AscendingRange
    MinusSign -> Just DescendingRange
  where
    start = describedRangeStart description

-- | Half-open bounds of the values visited by a range, independent of its
-- traversal direction.
rangeDescriptionImageBounds
  :: SuperEllipsisRangeDescription
  -> Maybe (Ordinal, Ordinal)
rangeDescriptionImageBounds description =
  case describedRangeTarget description of
    GivenTarget target
      | ordinalLT start target -> Just (start, target)
      | ordinalLT target start ->
          Just (successorOrdinal target, successorOrdinal start)
      | otherwise -> Nothing
    MinusSign ->
      let (base, _) = splitFiniteTail start
      in Just (base, successorOrdinal start)
    PlusSign -> Just (start, describedRangeRankLimit description)
  where
    start = describedRangeStart description

rangeDescriptionOrderType :: SuperEllipsisRangeDescription -> Ordinal
rangeDescriptionOrderType description =
  case rangeDescriptionImageBounds description of
    Nothing -> finiteOrdinal 0
    Just (lower, upper) ->
      fromMaybe (finiteOrdinal 0) (subtractOrdinal lower upper)

rangeDescriptionIsEmpty :: SuperEllipsisRangeDescription -> Bool
rangeDescriptionIsEmpty description =
  case describedRangeTarget description of
    GivenTarget target -> target == describedRangeStart description
    _ -> False

rangeDescriptionOverlapBounds
  :: SuperEllipsisRangeDescription
  -> SuperEllipsisRangeDescription
  -> Maybe (Ordinal, Ordinal)
rangeDescriptionOverlapBounds first second =
  case (rangeDescriptionImageBounds first,
        rangeDescriptionImageBounds second) of
    (Just (firstLower, firstUpper), Just (secondLower, secondUpper))
      | ordinalLT overlapLower overlapUpper ->
          Just (overlapLower, overlapUpper)
      where
        overlapLower = max firstLower secondLower
        overlapUpper = min firstUpper secondUpper
    _ -> Nothing

analyzeSuperEllipsisRangeDescriptions
  :: SuperEllipsisRangeDescription
  -> SuperEllipsisRangeDescription
  -> SuperEllipsisRangeConcatAnalysis
analyzeSuperEllipsisRangeDescriptions firstDescription secondDescription
  | rangeDescriptionIsEmpty firstDescription =
      RangeConcatCanonical secondDescription
  | rangeDescriptionIsEmpty secondDescription =
      RangeConcatCanonical firstDescription
  | Just (lower, upper) <- rangeDescriptionOverlapBounds
      firstDescription secondDescription =
      RangeConcatOverlapping
        firstDescription secondDescription lower upper
  | descriptionsAreContiguous firstDescription secondDescription =
      RangeConcatCanonical
        SuperEllipsisRangeDescription
          { describedRangeRankLimit =
              max
                (describedRangeRankLimit firstDescription)
                (describedRangeRankLimit secondDescription)
          , describedRangeStart = describedRangeStart firstDescription
          , describedRangeTarget = describedRangeTarget secondDescription
          }
  | otherwise = RangeConcatDisjoint firstDescription secondDescription

validateSuperEllipsisRangeDescriptions
  :: [SuperEllipsisRangeDescription]
  -> Either SuperEllipsisRangeConcatError ()
validateSuperEllipsisRangeDescriptions [] = Right ()
validateSuperEllipsisRangeDescriptions (first : rest) = do
  mapM_ (ensureDisjoint first) rest
  validateSuperEllipsisRangeDescriptions rest
  where
    ensureDisjoint left right =
      case analyzeSuperEllipsisRangeDescriptions left right of
        RangeConcatOverlapping
            firstDescription secondDescription lower upper ->
          Left
            (SuperEllipsisRangesOverlap
              firstDescription secondDescription lower upper)
        _ -> Right ()

descriptionsAreContiguous
  :: SuperEllipsisRangeDescription
  -> SuperEllipsisRangeDescription
  -> Bool
descriptionsAreContiguous first second =
  case describedRangeTarget first of
    GivenTarget boundary ->
      boundary == describedRangeStart second
        && rangeDescriptionDirection first == rangeDescriptionDirection second
    _ -> False

sameFiniteBase :: Ordinal -> Ordinal -> Bool
sameFiniteBase left right =
  let (leftBase, _) = splitFiniteTail left
      (rightBase, _) = splitFiniteTail right
  in leftBase == rightBase

finiteTailDifference :: Ordinal -> Ordinal -> Maybe Ordinal
finiteTailDifference left right =
  let (leftBase, leftTail) = splitFiniteTail left
      (rightBase, rightTail) = splitFiniteTail right
  in if leftBase == rightBase && rightTail <= leftTail
      then Just (finiteOrdinal (leftTail - rightTail))
      else Nothing

successorOrdinal :: Ordinal -> Ordinal
successorOrdinal value = addOrdinals value (finiteOrdinal 1)

ordinalPredecessor :: Ordinal -> Ordinal
ordinalPredecessor value =
  let (base, finiteTail) = splitFiniteTail value
  in if finiteTail == 0
      then value
      else addOrdinals base (finiteOrdinal (finiteTail - 1))

subtractFiniteOrdinal :: Ordinal -> Natural -> Ordinal
subtractFiniteOrdinal value amount =
  let (base, finiteTail) = splitFiniteTail value
  in addOrdinals base (finiteOrdinal (finiteTail - amount))
