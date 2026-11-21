{-# LANGUAGE CPP #-}
#include "../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--max-case-expand=8" @-}
{-@ LIQUID "--smt-timeout=10000" @-}

-- | Total Cantor decoding shared by ordinal and coverage enumeration.
module NaturalEncoding
  ( pairNatural, unpairNatural, unpairPair, pairUnpair
  , decodeNaturalList, encodeNaturalList, decodeEncode, encodeDecode
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

{-@ reflect triangular @-}
triangular :: Natural -> Natural
triangular value = value * (value + 1) `div` 2

{-@ reflect pairNatural @-}
pairNatural :: Natural -> Natural -> Natural
pairNatural first second = triangular (first + second) + first

-- ALIGN: NATURAL-UNPAIR-BOUNDS.
{-@ reflect unpairNatural @-}
{-@ unpairNatural :: code:Natural
      -> {result:(Natural, Natural) | fst result <= code && snd result <= code} @-}
unpairNatural :: Natural -> (Natural, Natural)
unpairNatural = unpairNaturalFrom 0

{-@ reflect unpairNaturalFrom @-}
{-@ unpairNaturalFrom :: diagonal:Natural -> remaining:Natural
      -> {result:(Natural, Natural) |
           fst result <= diagonal + remaining && snd result <= diagonal + remaining}
      / [remaining] @-}
unpairNaturalFrom :: Natural -> Natural -> (Natural, Natural)
unpairNaturalFrom diagonal remaining
  | remaining <= diagonal = (remaining, diagonal - remaining)
  | otherwise = unpairNaturalFrom (diagonal + 1) (remaining - diagonal - 1)

{-@ ple triangularStep @-}
{-@ triangularStep :: value:Natural
      -> {triangular (value + 1) == triangular value + value + 1} @-}
triangularStep :: Natural -> ()
triangularStep _ = ()

{-@ ple triangularMonotone @-}
{-@ triangularMonotone :: lower:Natural -> upper:{Natural | lower <= upper}
      -> {triangular lower <= triangular upper} @-}
triangularMonotone :: Natural -> Natural -> ()
triangularMonotone _ _ = ()

{-@ ple triangularStrict @-}
{-@ triangularStrict :: lower:Natural -> upper:{Natural | lower < upper}
      -> {triangular lower + lower + 1 <= triangular upper} @-}
triangularStrict :: Natural -> Natural -> ()
triangularStrict lower upper =
  triangularStep lower `seq` triangularMonotone (lower + 1) upper

{-@ ple unpairPairFrom @-}
{-@ unpairPairFrom :: diagonal:Natural -> first:Natural
      -> second:{Natural | diagonal <= first + second}
      -> {unpairNaturalFrom diagonal (triangular (first + second) - triangular diagonal + first)
           == (first, second)} / [first + second - diagonal] @-}
unpairPairFrom :: Natural -> Natural -> Natural -> ()
unpairPairFrom diagonal first second
  | diagonal == first + second = ()
  | otherwise =
      triangularStrict diagonal (first + second) `seq`
      unpairPairFrom (diagonal + 1) first second

-- ALIGN: ORDINAL-PAIR-UNPAIR.
{-@ ple unpairPair @-}
{-@ unpairPair :: first:Natural -> second:Natural
      -> {unpairNatural (pairNatural first second) == (first, second)} @-}
unpairPair :: Natural -> Natural -> ()
unpairPair = unpairPairFrom 0

{-@ ple pairUnpairFrom @-}
{-@ pairUnpairFrom :: diagonal:Natural -> remaining:Natural
      -> {pairNatural (fst (unpairNaturalFrom diagonal remaining))
           (snd (unpairNaturalFrom diagonal remaining)) == triangular diagonal + remaining}
      / [remaining] @-}
pairUnpairFrom :: Natural -> Natural -> ()
pairUnpairFrom diagonal remaining
  | remaining <= diagonal = ()
  | otherwise =
      triangularStep diagonal `seq`
      pairUnpairFrom (diagonal + 1) (remaining - diagonal - 1)

-- ALIGN: NATURAL-PAIR-UNPAIR.
{-@ ple pairUnpair @-}
{-@ pairUnpair :: code:Natural
      -> {pairNatural (fst (unpairNatural code)) (snd (unpairNatural code)) == code} @-}
pairUnpair :: Natural -> ()
pairUnpair = pairUnpairFrom 0

-- | Every nonempty list consumes a strictly smaller tail code.
{-@ reflect decodeNaturalList @-}
{-@ decodeNaturalList :: code:Natural -> [Natural] / [code] @-}
decodeNaturalList :: Natural -> [Natural]
decodeNaturalList 0 = []
decodeNaturalList code =
  let (value, rest) = unpairNatural (code - 1)
  in prependNatural value (decodeNaturalList rest)

{-@ reflect prependNatural @-}
prependNatural :: Natural -> [Natural] -> [Natural]
prependNatural value values = value : values

{-@ reflect encodeNaturalList @-}
encodeNaturalList :: [Natural] -> Natural
encodeNaturalList [] = 0
encodeNaturalList (value : values) = pairNatural value (encodeNaturalList values) + 1

{-@ ple encodeCons @-}
{-@ encodeCons :: value:Natural -> values:[Natural]
      -> {encodeNaturalList (prependNatural value values) == pairNatural value (encodeNaturalList values) + 1} @-}
encodeCons :: Natural -> [Natural] -> ()
encodeCons _ _ = ()

{-@ ple emptyListCode @-}
{-@ emptyListCode :: {encodeNaturalList [] == 0 && decodeNaturalList 0 == []} @-}
emptyListCode :: ()
emptyListCode = ()

-- ALIGN: COVERAGE-LIST-DECODE-ENCODE.
{-@ ple decodeEncode @-}
{-@ decodeEncode :: values:[Natural]
      -> {decodeNaturalList (encodeNaturalList values) == values} @-}
decodeEncode :: [Natural] -> ()
decodeEncode [] = emptyListCode
decodeEncode allValues@(value : values) =
  encodeCons value values `seq`
  unpairPair value (encodeNaturalList values) `seq`
  decodeNaturalList (encodeNaturalList allValues) `seq`
  decodeEncode values

{-@ ple decodeStep @-}
{-@ decodeStep :: code:{Natural | code > 0}
      -> value:Natural -> rest:{Natural | unpairNatural (code - 1) == (value, rest)}
      -> {decodeNaturalList code == prependNatural value (decodeNaturalList rest)} @-}
decodeStep :: Natural -> Natural -> Natural -> ()
decodeStep _ _ _ = ()

-- ALIGN: COVERAGE-LIST-ENCODE-DECODE.
{-@ encodeDecode :: code:Natural
      -> {encodeNaturalList (decodeNaturalList code) == code} / [code] @-}
encodeDecode :: Natural -> ()
encodeDecode 0 = emptyListCode
encodeDecode code =
  case unpairNatural (code - 1) of
    (value, rest) ->
      decodeStep code value rest `seq`
      encodeCons value (decodeNaturalList rest) `seq`
      pairUnpair (code - 1) `seq`
      encodeDecode rest

