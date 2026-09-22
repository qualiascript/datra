-- | A lightweight ordinal-indexed sequence used after proof-bearing chains
-- have been erased.  The order type and lookup function travel together so
-- append semantics are implemented once for maps and insertions.
module OrdinalSequence
  ( OrdinalSequence (..)
  , emptyOrdinalSequence
  , singletonOrdinalSequence
  , appendOrdinalSequence
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , ordinalLT
  , subtractOrdinal
  )

data OrdinalSequence value = OrdinalSequence
  { ordinalSequenceOrderType :: Ordinal
  , ordinalSequenceValueAt :: Ordinal -> Maybe value
  }

emptyOrdinalSequence :: OrdinalSequence value
emptyOrdinalSequence = OrdinalSequence (finiteOrdinal 0) (const Nothing)

singletonOrdinalSequence :: value -> OrdinalSequence value
singletonOrdinalSequence value =
  OrdinalSequence
    (finiteOrdinal 1)
    (\position ->
      if position == finiteOrdinal 0 then Just value else Nothing)

appendOrdinalSequence
  :: OrdinalSequence value
  -> OrdinalSequence value
  -> OrdinalSequence value
appendOrdinalSequence left right =
  OrdinalSequence combinedOrderType valueAt
  where
    leftOrderType = ordinalSequenceOrderType left
    combinedOrderType =
      addOrdinals leftOrderType (ordinalSequenceOrderType right)
    valueAt position
      | ordinalLT position leftOrderType = ordinalSequenceValueAt left position
      | otherwise = do
          rightPosition <- subtractOrdinal leftOrderType position
          ordinalSequenceValueAt right rightPosition
