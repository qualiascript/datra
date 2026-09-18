-- | English presentation text for typed Datra diagnostics.
--
-- This display-stage module translates strongly typed domain errors into
-- prose. Domain modules do not depend on it.
module Diagnostics.English
  ( localizeAccessError
  , localizeSuperEllipsisRangeError
  , localizeSuperEllipsisRangeConcatError
  ) where

import Data.List (intercalate)
import DatraOrdinal (Ordinal, ordinalCoefficients)
import Diagnostics (LocalizedMessage (LocalizedMessage))
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeError
      ( SuperEllipsisRangeInvalidDescendingBounds
      , SuperEllipsisRangeStartOutsideRank
      , SuperEllipsisRangeTargetOutsideRank
      )
  )

localizeAccessError :: AccessError -> LocalizedMessage
localizeAccessError reason =
  case reason of
    AccessInsertionRankExceedsMap insertionRank mapOrderType ->
      LocalizedMessage
        "the access insertion has a larger rank than the map"
        [ "insertion rank limit: " <> englishOrdinal insertionRank
        , "map final-page order type: " <> englishOrdinal mapOrderType
        ]
    AccessPositionOutOfBounds position mapOrderType ->
      LocalizedMessage
        "the access insertion selects a position outside the map"
        [ "selected position: " <> englishOrdinal position
        , "map final-page order type: " <> englishOrdinal mapOrderType
        ]
localizeSuperEllipsisRangeError
  :: SuperEllipsisRangeError
  -> LocalizedMessage
localizeSuperEllipsisRangeError reason =
  case reason of
    SuperEllipsisRangeStartOutsideRank start rankLimit ->
      LocalizedMessage
        ( "range start " <> englishOrdinal start
            <> " is not below the rank limit " <> englishOrdinal rankLimit
        )
        []
    SuperEllipsisRangeTargetOutsideRank target rankLimit ->
      LocalizedMessage
        ( "range target " <> englishOrdinal target
            <> " is above the rank limit " <> englishOrdinal rankLimit
        )
        []
    SuperEllipsisRangeInvalidDescendingBounds start target ->
      LocalizedMessage
        ( "descending range from " <> englishOrdinal start
            <> " to " <> englishOrdinal target
            <> " crosses an ordinal limit"
        )
        []

localizeSuperEllipsisRangeConcatError
  :: SuperEllipsisRangeConcatError
  -> LocalizedMessage
localizeSuperEllipsisRangeConcatError
    (SuperEllipsisRangesOverlap first second lower upper) =
  LocalizedMessage
    "cannot use overlapping ranges to access a map"
    [ "first range: " <> show first
    , "second range: " <> show second
    , "overlap: " <> englishOrdinal lower
        <> " through " <> englishOrdinal upper
    ]

englishOrdinal :: Ordinal -> String
englishOrdinal value =
  case ordinalCoefficients value of
    [] -> "0"
    coefficients ->
      intercalate " + "
        [ renderTerm power coefficient
        | (power, coefficient) <- zip [degree, degree - 1 .. 0] coefficients
        , coefficient /= 0
        ]
      where
        degree = length coefficients - 1
        renderTerm 0 coefficient = show coefficient
        renderTerm 1 1 = "(...)"
        renderTerm 1 coefficient = "(...) * " <> show coefficient
        renderTerm power 1 = "(...)^" <> show power
        renderTerm power coefficient =
          "(...)^" <> show power <> " * " <> show coefficient
