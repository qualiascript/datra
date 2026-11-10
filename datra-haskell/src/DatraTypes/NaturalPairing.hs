-- | Pairing and finite-triangle indexing helpers for natural numbers.
module NaturalPairing
  ( pairNaturals
  , unpairNaturals
  , triangularPrefix
  , unrankFinitePair
  ) where

import Numeric.Natural (Natural)

pairNaturals :: Natural -> Natural -> Natural
pairNaturals left right = triangular (left + right) + right

unpairNaturals :: Natural -> Maybe (Natural, Natural)
unpairNaturals = go 0
  where
    go diagonal remainder
      | remainder < diagonal + 1 =
          Just (diagonal - remainder, remainder)
      | otherwise = go (diagonal + 1) (remainder - diagonal - 1)

triangularPrefix :: Natural -> Natural -> Natural
triangularPrefix width offset =
  offset * (2 * width - offset + 1) `div` 2

unrankFinitePair :: Natural -> Natural -> Maybe (Natural, Natural)
unrankFinitePair width = go 0
  where
    go offset remainder
      | offset >= width = Nothing
      | remainder < rowSize = Just (offset, offset + remainder)
      | otherwise = go (offset + 1) (remainder - rowSize)
      where
        rowSize = width - offset

triangular :: Natural -> Natural
triangular value = value * (value + 1) `div` 2
