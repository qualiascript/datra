{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

-- | Symbolic syntax for Ellipsis and super-ellipsis ranges.
module Ellipsis.Syntax
  ( (...)
  , (<..>)
  , (..+)
  , (..-)
  ) where

import Dot (dot)
import Ellipsis (Ellipsis)
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
import StableConfederalData (StableConfederalData)
import SuperEllipsis (superEllipsis)
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeTarget (MinusSign, PlusSign, GivenTarget)
  , superEllipsisRange
  )

infix 5 <..>
infixl 5 ..+, ..-

-- | The rank-one Ellipsis formulation.
(...) :: StableConfederalData Ellipsis
(...) = superEllipsis dot

-- | Construct a lower-inclusive, upper-exclusive range at the least rank
-- containing its lower value and upper boundary. A formulation on the right
-- denotes the boundary of its own rank rather than a value in the next rank.
(<..>)
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
left <..> right = \useRange -> do
  superEllipsisRange
    (knownSuperEllipsisRank @(RangeNumericalLevel left right))
    (numericalOperandOrdinal left)
    (GivenTarget (numericalOperandOrdinal right))
    useRange

-- | Construct a range from an explicit origin through the rest of its rank.
(..+)
  :: forall origin result.
     ( NumericalOperand origin
     , KnownSuperEllipsisLevel (NumericalOperandLevel origin)
     )
  => origin
  -> (forall scope.
        SuperEllipsisRange (NumericalOperandTarget origin) scope
        -> result)
  -> Maybe result
(..+) origin useRange = do
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    (numericalOperandOrdinal origin)
    PlusSign
    useRange

-- | Construct the longest descending range that only removes a finite tail.
(..-)
  :: forall origin result.
     ( NumericalOperand origin
     , KnownSuperEllipsisLevel (NumericalOperandLevel origin)
     )
  => origin
  -> (forall scope.
        SuperEllipsisRange (NumericalOperandTarget origin) scope
        -> result)
  -> Maybe result
(..-) origin useRange = do
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    (numericalOperandOrdinal origin)
    MinusSign
    useRange
