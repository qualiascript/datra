{-# LANGUAGE TypeFamilies #-}

-- | The inductive hierarchy of recursive ellipses.
--
-- @Dot@ is the zeroth level.  Given the preceding level @S(n-1)@,
-- @SuperEllipsis S(n-1)@ is the guarded fixed point
--
-- @
-- S(n) = S(n-1) <.> S(n).
-- @
--
-- Consequently @SuperEllipsis Dot@ has order type omega,
-- @SuperEllipsis (SuperEllipsis Dot)@ has order type omega squared, and
-- finite iteration reaches every power below omega to the omega.
module SuperEllipsis
  ( SuperEllipsis
  , SuperEllipsisValue
  , superEllipsis
  , superEllipsisUnfolded
  , superEllipsisFold
  , superEllipsisUnfold
  , rollSuperEllipsisValue
  , unrollSuperEllipsisValue
  , withSuperEllipsisValue
  ) where

import FixedPoint
  ( FixedPoint
  , FixedPointValue
  , fixedPoint
  , fixedPointLayer
  , rollFixedPoint
  , rollFixedPointValue
  , unrollFixedPoint
  , unrollFixedPointValue
  , withFixedPointValue
  )
import MapOperators.ConcatOperator
  ( ConcatOperatorValue
  , ConcatOperatorValues
  )
import MapOperators.Syntax.ConcatOperatorSyntax ((<.>))
import MapOperators.SequentialOperator (SequentialOperand)
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  )

-- | The nominal tag is derived from the preceding level.  This keeps every
-- level distinct while leaving clients with only the inductive predecessor
-- parameter to supply.
data SuperEllipsisTag predecessor

-- | The successor of one level in the super-ellipsis hierarchy.
--
-- The base of the induction is @Dot@, supplied by the caller; this module
-- deliberately does not import either @Dot@ or @Ellipsis@, so higher levels
-- cannot create a module cycle through their specializations.
type SuperEllipsis predecessor =
  FixedPoint
    (SuperEllipsisTag predecessor)
    (ConcatOperatorValues predecessor)

-- | One observable @predecessor <.> SuperEllipsis predecessor@ layer.
type SuperEllipsisValue predecessor =
  FixedPointValue
    (SuperEllipsisTag predecessor)
    (ConcatOperatorValues predecessor)

-- | Tie the guarded recursive equation for the successor of @predecessor@.
superEllipsis
  :: SequentialOperand predecessor
  => StableConfederalData predecessor
  -> StableConfederalData (SuperEllipsis predecessor)
superEllipsis predecessor = fixedPoint (predecessor <.>)

-- | Expose one layer of the recursive equation.
superEllipsisUnfolded
  :: SequentialOperand predecessor
  => StableConfederalData predecessor
  -> StableConfederalData
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
superEllipsisUnfolded predecessor = fixedPointLayer (predecessor <.>)

-- | Fold one recursive layer into its super ellipsis.
superEllipsisFold
  :: SequentialOperand predecessor
  => StableConfederalData predecessor
  -> StableConfederalDataHom
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
       (SuperEllipsis predecessor)
superEllipsisFold predecessor = rollFixedPoint (predecessor <.>)

-- | Unfold a super ellipsis into one recursive layer.
superEllipsisUnfold
  :: SequentialOperand predecessor
  => StableConfederalData predecessor
  -> StableConfederalDataHom
       (SuperEllipsis predecessor)
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
superEllipsisUnfold predecessor = unrollFixedPoint (predecessor <.>)

-- | Introduce one recursive value layer.
rollSuperEllipsisValue
  :: ConcatOperatorValue
       predecessor
       (SuperEllipsis predecessor)
       object
  -> SuperEllipsisValue predecessor object
rollSuperEllipsisValue = rollFixedPointValue

-- | Observe one recursive value layer.
unrollSuperEllipsisValue
  :: SuperEllipsisValue predecessor object
  -> ConcatOperatorValue
       predecessor
       (SuperEllipsis predecessor)
       object
unrollSuperEllipsisValue = unrollFixedPointValue

-- | Observe one recursive layer without exposing its representation.
withSuperEllipsisValue
  :: SuperEllipsisValue predecessor object
  -> (ConcatOperatorValue
        predecessor
        (SuperEllipsis predecessor)
        object
      -> result)
  -> result
withSuperEllipsisValue = withFixedPointValue
