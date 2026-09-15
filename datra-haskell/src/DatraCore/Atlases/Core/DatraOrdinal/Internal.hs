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
  , ordinalLT
  , coefficientsLT
  , listLength
  , lexicographicLT
  , addOrdinals
  , addCoefficients
  , subtractOrdinal
  , naturalAtOrdinal
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
