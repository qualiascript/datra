{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Rank-inferred construction of ranges from numerical operands.
module NumericalOperators.Range
  ( boundedSuperEllipsisRange
  , openPlusSuperEllipsisRange
  , openMinusSuperEllipsisRange
  ) where

import NumericalOperators.NumericalOperand
  ( KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalOperandLevel
  , NumericalOperandTarget
  , RangeNumericalLevel
  , RangeNumericalTarget
  , knownSuperEllipsisRank
  , numericalOperandOrdinal
  )
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign)
  , superEllipsisRange
  )

-- | Construct a lower-inclusive, upper-exclusive range at the least rank
-- containing its lower value and upper boundary. A formulation on the right
-- denotes the boundary of its own rank rather than a value in the next rank.
boundedSuperEllipsisRange
  :: forall left right result.
     ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (RangeNumericalLevel left right)
     )
  => left
  -> right
  -> (forall scope.
        SuperEllipsisRange (RangeNumericalTarget left right) scope
        -> result)
  -> Maybe result
boundedSuperEllipsisRange left right useRange =
  superEllipsisRange
    (knownSuperEllipsisRank @(RangeNumericalLevel left right))
    (numericalOperandOrdinal left)
    (GivenTarget (numericalOperandOrdinal right))
    useRange

-- | Construct a range from an explicit origin through the rest of its rank.
openPlusSuperEllipsisRange
  :: forall origin result.
     ( NumericalOperand origin
     , KnownSuperEllipsisLevel (NumericalOperandLevel origin)
     )
  => origin
  -> (forall scope.
        SuperEllipsisRange (NumericalOperandTarget origin) scope
        -> result)
  -> Maybe result
openPlusSuperEllipsisRange origin useRange =
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    (numericalOperandOrdinal origin)
    PlusSign
    useRange

-- | Construct the longest descending range that only removes a finite tail.
openMinusSuperEllipsisRange
  :: forall origin result.
     ( NumericalOperand origin
     , KnownSuperEllipsisLevel (NumericalOperandLevel origin)
     )
  => origin
  -> (forall scope.
        SuperEllipsisRange (NumericalOperandTarget origin) scope
        -> result)
  -> Maybe result
openMinusSuperEllipsisRange origin useRange =
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    (numericalOperandOrdinal origin)
    MinusSign
    useRange
