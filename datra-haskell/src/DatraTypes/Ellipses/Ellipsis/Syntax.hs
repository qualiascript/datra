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
  ( BinaryNumericalLevel
  , BinaryNumericalTarget
  , KnownSuperEllipsisLevel
  , NumericalOperand
  , NumericalOperandLevel
  , NumericalOperandTarget
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
-- containing both explicit endpoint values.
(<..>)
  :: forall left right result.
     ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (BinaryNumericalLevel left right)
     )
  => left
  -> right
  -> (forall scope.
        SuperEllipsisRange (BinaryNumericalTarget left right) scope
        -> result)
  -> Maybe result
left <..> right = \useRange -> do
  start <- numericalOperandOrdinal left
  target <- numericalOperandOrdinal right
  superEllipsisRange
    (knownSuperEllipsisRank @(BinaryNumericalLevel left right))
    start
    (GivenTarget target)
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
  start <- numericalOperandOrdinal origin
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    start
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
  start <- numericalOperandOrdinal origin
  superEllipsisRange
    (knownSuperEllipsisRank @(NumericalOperandLevel origin))
    start
    MinusSign
    useRange
