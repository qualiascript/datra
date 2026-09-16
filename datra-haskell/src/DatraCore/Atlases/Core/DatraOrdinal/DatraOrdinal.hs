-- | Public ordinal API backed by the hidden ordinal implementation.
module DatraOrdinal
  ( Ordinal
  , ordinal
  , finiteOrdinal
  , omega
  , omegaPower
  , ordinalLT
  , addOrdinals
  , subtractOrdinal
  , naturalAtOrdinal
  , ordinalAtNaturalRank
  , naturalRankOfOrdinal
  ) where

import DatraOrdinal.Internal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , naturalRankOfOrdinal
  , omega
  , omegaPower
  , ordinal
  , ordinalAtNaturalRank
  , ordinalLT
  , subtractOrdinal
  )
