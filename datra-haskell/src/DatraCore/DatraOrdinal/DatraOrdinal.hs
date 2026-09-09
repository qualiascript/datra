-- | Public ordinal API. The representation and proof machinery live together
-- in the hidden ordinal/chain proof kernel.
module DatraOrdinal
  ( Ordinal
  , ordinal
  , finiteOrdinal
  , omega
  , ordinalLT
  , addOrdinals
  , subtractOrdinal
  , naturalAtOrdinal
  ) where

import OrdinalChain.Internal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinal
  , ordinalLT
  , subtractOrdinal
  )
