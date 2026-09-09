{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module DatraOrdinal
  ( Ordinal(..)
  , ordinal
  , finiteOrdinal
  , omega
  , ordinalLT
  , addOrdinals
  , subtractOrdinal
  , naturalAtOrdinal
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}

-- | An ordinal strictly below omega^omega in Cantor normal form.
--
-- The list @[a_n, ..., a_1, a_0]@ represents
--
--   omega^n * a_n + ... + omega * a_1 + a_0.
--
-- Leading zero coefficients are removed, so zero has the unique
-- representation @[]@.
newtype Ordinal = Ordinal
  { coefficients :: [Natural]
  }
  deriving (Eq, Show)

-- | Construct a canonical ordinal from descending coefficients.
--
-- For example, @ordinal [4, 3, 9]@ represents
-- @omega^2 * 4 + omega * 3 + 9@.
ordinal :: [Natural] -> Ordinal
ordinal = Ordinal . dropWhile (== 0)

-- | Embed a natural number as a finite ordinal.
finiteOrdinal :: Natural -> Ordinal
finiteOrdinal value = ordinal [value]

-- | The first infinite ordinal.
omega :: Ordinal
omega = ordinal [1, 0]

instance Ord Ordinal where
  compare (Ordinal left) (Ordinal right) =
    compare (length left) (length right)
      <> compare left right

-- | A reflected strict comparison that agrees with the 'Ord' instance.
{-@ reflect ordinalLT @-}
ordinalLT :: Ordinal -> Ordinal -> Bool
ordinalLT (Ordinal left) (Ordinal right) =
  listLength left < listLength right
    || listLength left == listLength right && lexicographicLT left right

{-@ reflect listLength @-}
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
addOrdinals :: Ordinal -> Ordinal -> Ordinal
addOrdinals left (Ordinal []) = left
addOrdinals (Ordinal leftCoefficients)
  right@(Ordinal (rightLeadingCoefficient : rightLowerCoefficients))
  | length leftCoefficients < length rightCoefficients = right
  | otherwise = case matchingAndLowerLeftCoefficients of
      matchingLeftCoefficient : _ ->
        Ordinal
          (higherLeftCoefficients
            ++ (matchingLeftCoefficient + rightLeadingCoefficient)
              : rightLowerCoefficients)
      [] -> right
  where
    rightCoefficients = rightLeadingCoefficient : rightLowerCoefficients

    numberOfHigherLeftCoefficients =
      length leftCoefficients - length rightCoefficients

    (higherLeftCoefficients, matchingAndLowerLeftCoefficients) =
      splitAt numberOfHigherLeftCoefficients leftCoefficients

-- | Remove a left ordinal prefix when the value lies at or after it.
subtractOrdinal :: Ordinal -> Ordinal -> Maybe Ordinal
subtractOrdinal (Ordinal left) (Ordinal value)
  | listLength value < listLength left = Nothing
  | listLength value > listLength left = Just (Ordinal value)
  | otherwise = Ordinal <$> subtractCoefficients left value

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
naturalAtOrdinal :: Ordinal -> Maybe Natural
naturalAtOrdinal (Ordinal []) = Just 0
naturalAtOrdinal (Ordinal [value]) = Just value
naturalAtOrdinal _ = Nothing
