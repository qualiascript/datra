{-# LANGUAGE RankNTypes #-}

-- | Natural numbers represented as rank-one super-ellipsis values.
module EllipsisNatural
  ( EllipsisNatural
  , EllipsisNaturalElement
  , ellipsisNatural
  , ellipsisNaturalTotal
  , ellipsisNaturalInsertion
  ) where

import DatraOrdinal (finiteOrdinal)
import Ellipsis (Ellipsis)
import Numeric.Natural (Natural)
import SuperEllipsis
  ( dotSuperEllipsisRank
  , nextSuperEllipsisRank
  )
import SuperEllipsisInsertion (SuperEllipsisInsertion)
import SuperEllipsisValue
  ( SuperEllipsisValue
  , SuperEllipsisValueElement
  , superEllipsisValue
  , superEllipsisValueInsertion
  , naturalSuperEllipsisValue
  )

type EllipsisNatural = SuperEllipsisValue Ellipsis

type EllipsisNaturalElement = SuperEllipsisValueElement Ellipsis

ellipsisNatural
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> Maybe result
ellipsisNatural value =
  superEllipsisValue
    (nextSuperEllipsisRank dotSuperEllipsisRank)
    (finiteOrdinal value)

-- | Total constructor justified by every finite natural lying strictly below
-- the rank-one Ellipsis limit.
ellipsisNaturalTotal
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> result
ellipsisNaturalTotal = naturalSuperEllipsisValue

ellipsisNaturalInsertion
  :: EllipsisNatural scope
  -> SuperEllipsisInsertion Ellipsis (EllipsisNaturalElement scope)
ellipsisNaturalInsertion = superEllipsisValueInsertion
