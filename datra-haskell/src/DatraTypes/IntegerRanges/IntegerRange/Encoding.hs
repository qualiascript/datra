{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Canonical @Nat x 2@ insertion used by integers and integer ranges.
module IntegerRange.Encoding
  ( IntegerElement
  , integerElementValue
  , integerSequenceInsertion
  , integerSingletonInsertion
  , withIntegerInsertionAtlasWitness
  ) where

import Atlas (AtlasWitness, atlasWitness)
import Chain (chain)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal, omega)
import Ellipsis (Ellipsis)
import EllipsisInteger
  ( pattern Complemented
  , pattern Direct
  , integerAtCode
  , integerCode
  )
import EmptyAtlas (emptyAtlas)
import IntegerRange.Interval
  ( IntegerRangeTarget (..)
  , integerAtOffset
  , integerInterval
  , integerIntervalContains
  , integerIntervalDirection
  , integerIntervalWidth
  , integerOffset
  )
import MapOperators.IndexedAtlasMap (indexedAtlasAtlas)
import MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (..)
  )
import Numeric.Natural (Natural)
import SuperEllipsis
  ( SuperEllipsisRank
  , dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  )
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , superEllipsisInsertion
  , superEllipsisInsertionOrderedMap
  )

type role IntegerElement nominal
newtype IntegerElement scope = IntegerElement
  { integerElementValue :: Integer
  }
  deriving (Eq, Show)

integerSequenceInsertion
  :: Integer
  -> IntegerRangeTarget
  -> (forall scope.
       SuperEllipsisInsertion Ellipsis (IntegerElement scope)
       -> result)
  -> result
integerSequenceInsertion start target useInsertion =
  useInsertion
    (superEllipsisInsertion
      integerRank
      valueChain
      encode
      decode
      (const ()))
  where
    interval = integerInterval start target
    direction = integerIntervalDirection interval
    orderType =
      case target of
        FiniteIntegerTarget final ->
          finiteOrdinal (integerIntervalWidth start final)
        _ -> omega
    valueAt position = do
      offset <- naturalAtOrdinal position
      case target of
        FiniteIntegerTarget final
          | offset >= integerIntervalWidth start final -> Nothing
        _ -> pure ()
      pure (IntegerElement (integerAtOffset direction start offset))
    valueOffset (IntegerElement value) =
      integerOffset direction start value
    valueChain =
      chain
        orderType
        (finiteOrdinal . valueOffset)
        valueAt
        (const ())
        (\_ _ -> ())
        (const ())
    encode (IntegerElement value) =
      case superEllipsisTerminal integerRank (finiteOrdinal (code value)) of
        Just terminal -> terminal
        Nothing -> superEllipsisZeroTerminal integerRank
    decode terminal = do
      naturalCode <-
        naturalAtOrdinal (superEllipsisTerminalPosition terminal)
      let value = integerAtCode naturalCode
      if integerIntervalContains interval value
        then Just (IntegerElement value)
        else Nothing

integerSingletonInsertion
  :: Integer
  -> (forall scope.
       SuperEllipsisInsertion Ellipsis (IntegerElement scope)
       -> result)
  -> result
integerSingletonInsertion value =
  integerSequenceInsertion value (FiniteIntegerTarget value)

withIntegerInsertionAtlasWitness
  :: SuperEllipsisInsertion Ellipsis (IntegerElement scope)
  -> (forall atlasObject. AtlasWitness atlasObject -> result)
  -> result
withIntegerInsertionAtlasWitness insertion useWitness =
  case superEllipsisInsertionOrderedMap insertion of
    EmptyOrderedAtlasMap ->
      emptyAtlas (useWitness . atlasWitness)
    NonEmptyOrderedAtlasMap valueMap ->
      useWitness (atlasWitness (indexedAtlasAtlas valueMap))

integerRank :: SuperEllipsisRank Ellipsis
integerRank = nextSuperEllipsisRank dotSuperEllipsisRank

code :: Integer -> Natural
code value
  | value >= 0 = integerCode (fromInteger value) Direct
  | otherwise =
      integerCode (fromInteger (negate value - 1)) Complemented
