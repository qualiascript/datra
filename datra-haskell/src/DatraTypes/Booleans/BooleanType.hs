-- | Datra's two Boolean values.
--
-- At the language boundary the type is presented as
-- @False := 0 | True := 1@.  Keeping the flag here, rather than as a Haskell
-- 'Bool', lets other typed Datra values (notably integers) carry the actual
-- Datra Boolean representation.
module BooleanType
  ( BooleanType
  , DatraBoolean (..)
  , false
  , true
  , booleanNatural
  , booleanFromNatural
  , booleanValue
  ) where

import Numeric.Natural (Natural)

data DatraBoolean = DatraFalse | DatraTrue
  deriving (Eq, Ord, Show)

type BooleanType = DatraBoolean

false :: DatraBoolean
false = DatraFalse

true :: DatraBoolean
true = DatraTrue

booleanNatural :: DatraBoolean -> Natural
booleanNatural DatraFalse = 0
booleanNatural DatraTrue = 1

booleanFromNatural :: Natural -> Maybe DatraBoolean
booleanFromNatural 0 = Just DatraFalse
booleanFromNatural 1 = Just DatraTrue
booleanFromNatural _ = Nothing

booleanValue :: DatraBoolean -> Bool
booleanValue DatraFalse = False
booleanValue DatraTrue = True
