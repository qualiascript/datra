{-# LANGUAGE RankNTypes #-}

-- | Natural numbers represented as rank-one super-ellipsis values.
module EllipsisNatural
  ( EllipsisNatural
  , EllipsisNaturalElement
  , ellipsisNatural
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

ellipsisNaturalInsertion
  :: EllipsisNatural scope
  -> SuperEllipsisInsertion Ellipsis (EllipsisNaturalElement scope)
ellipsisNaturalInsertion = superEllipsisValueInsertion
