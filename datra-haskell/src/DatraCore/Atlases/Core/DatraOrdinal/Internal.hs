{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden ordinal representation, smart constructors, and arithmetic.
module DatraOrdinal.Internal
  ( Ordinal(..)
  , canonicalCoefficients
  , ordinal
  , finiteOrdinal
  , omega
  , omegaPower
  , ordinalLT
  , coefficientsLT
  , listLength
  , lexicographicLT
  , addOrdinals
  , addCoefficients
  , subtractOrdinal
  , naturalAtOrdinal
  , ordinalAtNaturalRank
  , naturalRankOfOrdinal
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

{-@ reflect canonicalCoefficients @-}
canonicalCoefficients :: [Natural] -> Bool
canonicalCoefficients [] = True
canonicalCoefficients (leading : _) = leading > 0

{-@ type CanonicalCoefficients = { values:[Natural] | canonicalCoefficients values } @-}

-- | An ordinal strictly below omega^omega in canonical Cantor normal form.
{-@
data Ordinal = Ordinal
  { coefficients :: CanonicalCoefficients
  }
@-}
{-@
invariant { value:Ordinal |
  canonicalCoefficients (coefficients value) }
@-}
data Ordinal = Ordinal
  { coefficients :: [Natural]
  }
  deriving (Eq, Show)

-- | Construct a canonical ordinal from descending coefficients.
{-@ reflect ordinal @-}
ordinal :: [Natural] -> Ordinal
ordinal values = Ordinal (dropLeadingZeros values)

{-@ reflect dropLeadingZeros @-}
{-@ dropLeadingZeros :: [Natural] -> CanonicalCoefficients @-}
dropLeadingZeros :: [Natural] -> [Natural]
dropLeadingZeros [] = []
dropLeadingZeros values@(leading : rest)
  | leading > 0 = values
  | otherwise = dropLeadingZeros rest

-- | Embed a natural number as a finite ordinal.
{-@ reflect finiteOrdinal @-}
finiteOrdinal :: Natural -> Ordinal
finiteOrdinal value = ordinal [value]

-- | The first infinite ordinal.
{-@ reflect omega @-}
omega :: Ordinal
omega = ordinal [1, 0]

-- | The finite power @omega^n@.  In particular, @omega^0 = 1@.
omegaPower :: Natural -> Ordinal
omegaPower 0 = finiteOrdinal 1
omegaPower power = ordinal (1 : zeros power)
  where
    zeros count
      | count > 0 = 0 : zeros (count - 1)
      | otherwise = []

instance Ord Ordinal where
  compare (Ordinal left) (Ordinal right) =
    compare (length left) (length right)
      <> compare left right

-- | A reflected strict comparison that agrees with the 'Ord' instance.
{-@ reflect ordinalLT @-}
ordinalLT :: Ordinal -> Ordinal -> Bool
ordinalLT (Ordinal left) (Ordinal right) = coefficientsLT left right

{-@ reflect coefficientsLT @-}
{-@
coefficientsLT
  :: left:[Natural]
  -> right:[Natural]
  -> { result:Bool |
       result <=> len left < len right
         || (len left == len right && lexicographicLT left right) }
@-}
coefficientsLT :: [Natural] -> [Natural] -> Bool
coefficientsLT left right =
  listLength left < listLength right
    || listLength left == listLength right && lexicographicLT left right

{-@ reflect listLength @-}
{-@ listLength :: values:[a] -> { result:Int | result == len values } @-}
listLength :: [a] -> Int
listLength [] = 0
listLength (_ : values) = 1 + listLength values

{-@ reflect lexicographicLT @-}
lexicographicLT :: [Natural] -> [Natural] -> Bool
lexicographicLT [] _ = False
lexicographicLT _ [] = False
lexicographicLT (left : lefts) (right : rights)
  | left < right = True
  | left > right = False
  | otherwise = lexicographicLT lefts rights

-- | Ordinal addition. This is generally not commutative.
{-@ reflect addOrdinals @-}
addOrdinals :: Ordinal -> Ordinal -> Ordinal
addOrdinals (Ordinal left) (Ordinal right) =
  Ordinal (addCoefficients left right)

{-@ reflect addCoefficients @-}
{-@
addCoefficients
  :: left:[Natural]
  -> right:[Natural]
  -> { result:[Natural] |
       (canonicalCoefficients left && canonicalCoefficients right
         => canonicalCoefficients result)
       && len result == (if len right == 0 then len left
         else if len left < len right then len right else len left) }
@-}
addCoefficients :: [Natural] -> [Natural] -> [Natural]
addCoefficients left [] = left
addCoefficients [] right = right
addCoefficients left@(leftHead : leftTail) right@(rightHead : rightTail)
  | listLength left < listLength right = right
  | listLength left == listLength right =
      (leftHead + rightHead) : rightTail
  | otherwise = leftHead : addCoefficients leftTail right

-- | Remove a left ordinal prefix when the value lies at or after it.
{-@ reflect subtractOrdinal @-}
subtractOrdinal :: Ordinal -> Ordinal -> Maybe Ordinal
subtractOrdinal (Ordinal left) (Ordinal value)
  | listLength value < listLength left = Nothing
  | listLength value > listLength left = Just (ordinal value)
  | otherwise = ordinal <$> subtractCoefficients left value

subtractCoefficients
  :: [Natural]
  -> [Natural]
  -> Maybe [Natural]
subtractCoefficients [] [] = Just []
subtractCoefficients (left : lefts) (value : values)
  | value < left = Nothing
  | value == left = subtractCoefficients lefts values
  | otherwise = Just ((value - left) : values)
subtractCoefficients _ _ = Nothing

-- | Decode a finite ordinal as a natural number.
{-@ reflect naturalAtOrdinal @-}
naturalAtOrdinal :: Ordinal -> Maybe Natural
naturalAtOrdinal (Ordinal []) = Just 0
naturalAtOrdinal (Ordinal [value]) = Just value
naturalAtOrdinal _ = Nothing

-- | Decode one natural in the canonical enumeration of ordinals below
-- @omega^width@.  A fixed-width coefficient vector is decoded by iterated
-- Cantor unpairing, then canonicalized by 'ordinal'.
ordinalAtNaturalRank :: Natural -> Natural -> Maybe Ordinal
ordinalAtNaturalRank width code = ordinal <$> coefficientTuple width code

-- | Encode an ordinal below @omega^width@ in the inverse canonical natural
-- enumeration.  Ordinals outside that bound are rejected.
naturalRankOfOrdinal :: Natural -> Ordinal -> Maybe Natural
naturalRankOfOrdinal width value@(Ordinal values)
  | not (ordinalLT value (omegaPower width)) = Nothing
  | otherwise = encodeTuple (padCoefficients width values)

coefficientTuple :: Natural -> Natural -> Maybe [Natural]
coefficientTuple 0 0 = Just []
coefficientTuple 0 _ = Nothing
coefficientTuple 1 code = Just [code]
coefficientTuple width code =
  let (leading, rest) = unpairNatural code
  in (leading :) <$> coefficientTuple (width - 1) rest

padCoefficients :: Natural -> [Natural] -> [Natural]
padCoefficients width values = prependZeros (width - listNaturalLength values) values

listNaturalLength :: [value] -> Natural
listNaturalLength [] = 0
listNaturalLength (_ : values) = 1 + listNaturalLength values

prependZeros :: Natural -> [Natural] -> [Natural]
prependZeros count values
  | count > 0 = 0 : prependZeros (count - 1) values
  | otherwise = values

encodeTuple :: [Natural] -> Maybe Natural
encodeTuple [] = Just 0
encodeTuple [value] = Just value
encodeTuple (value : values) = pairNatural value <$> encodeTuple values

pairNatural :: Natural -> Natural -> Natural
pairNatural first second =
  let diagonal = first + second
  in diagonal * (diagonal + 1) `div` 2 + first

{-@ lazy unpairNatural @-}
unpairNatural :: Natural -> (Natural, Natural)
unpairNatural = go 0
  where
    go diagonal remainder
      | remainder <= diagonal = (remainder, diagonal - remainder)
      | otherwise = go (diagonal + 1) (remainder - diagonal - 1)
