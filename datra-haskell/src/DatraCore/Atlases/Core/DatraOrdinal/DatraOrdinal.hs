-- | Public ordinal API backed by the hidden ordinal implementation.
module DatraOrdinal
  ( Ordinal
  , ordinal
  , finiteOrdinal
  , omega
  , omegaPower
  , ordinalLT
  , addOrdinals
  , multiplyOrdinals
  , powerOrdinal
  , subtractOrdinal
  , naturalAtOrdinal
  , ordinalAtNaturalRank
  , naturalRankOfOrdinal
  ) where

import DatraOrdinal.Internal
  ( Ordinal (Ordinal)
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
import Numeric.Natural (Natural)

-- | Ordinal multiplication below @omega^omega@. Positive-degree terms on
-- the right absorb lower terms on the left, so this is generally not
-- commutative.
multiplyOrdinals :: Ordinal -> Ordinal -> Ordinal
multiplyOrdinals (Ordinal left) (Ordinal right) =
  ordinal (multiplyCoefficients left right)

multiplyCoefficients :: [Natural] -> [Natural] -> [Natural]
multiplyCoefficients [] _ = []
multiplyCoefficients _ [] = []
multiplyCoefficients left [constant] =
  multiplyByFiniteOrdinal left constant
multiplyCoefficients left (coefficient : coefficients) =
  coefficient : multiplyCoefficients left coefficients

-- For a nonzero finite right factor, ordinal addition scales only the
-- leading coefficient; the last copy supplies all lower terms. Returning a
-- zero vector of the same width preserves preceding degree shifts.
multiplyByFiniteOrdinal :: [Natural] -> Natural -> [Natural]
multiplyByFiniteOrdinal [] _ = []
multiplyByFiniteOrdinal (_ : coefficients) 0 =
  0 : zeroCoefficients coefficients
multiplyByFiniteOrdinal (leading : coefficients) factor =
  (leading * factor) : coefficients

zeroCoefficients :: [Natural] -> [Natural]
zeroCoefficients [] = []
zeroCoefficients (_ : coefficients) = 0 : zeroCoefficients coefficients

-- | Raise an ordinal to a finite natural power. Binary exponentiation keeps
-- the recursion logarithmic; @0^0@ is one.
powerOrdinal :: Ordinal -> Natural -> Ordinal
powerOrdinal _ 0 = finiteOrdinal 1
powerOrdinal value power
  | power `mod` 2 == 0 =
      let half = powerOrdinal value (power `div` 2)
      in multiplyOrdinals half half
  | otherwise =
      multiplyOrdinals (powerOrdinal value (power - 1)) value
