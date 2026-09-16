{-# LANGUAGE RankNTypes #-}

-- | Natural numbers as rank-one 'SuperEllipsisValue' values.
module Natural
  ( Natural
  , NaturalElement
  , natural
  , naturalInsertion
  ) where

import DatraOrdinal (finiteOrdinal)
import Ellipsis (ellipsisRank)
import EllipsisInsertion (EllipsisInsertion)
import Numeric.Natural qualified as Numeric
import NaturalRange
  ( NaturalRange
  , NaturalRangeElement
  , naturalRangeFromSuperEllipsisRange
  , naturalRangeSuperEllipsisRange
  )
import SuperEllipsisValue
  ( superEllipsisValue
  , superEllipsisValueInsertion
  )

type Natural = NaturalRange

type NaturalElement = NaturalRangeElement

natural
  :: Numeric.Natural
  -> (forall scope. Natural scope -> result)
  -> Maybe result
natural value useNatural =
  superEllipsisValue ellipsisRank (finiteOrdinal value)
    (useNatural . naturalRangeFromSuperEllipsisRange)

naturalInsertion
  :: Natural scope
  -> EllipsisInsertion (NaturalElement scope)
naturalInsertion =
  superEllipsisValueInsertion . naturalRangeSuperEllipsisRange
