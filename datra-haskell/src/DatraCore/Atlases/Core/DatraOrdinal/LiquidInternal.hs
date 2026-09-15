{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -Wno-name-shadowing -Wno-unused-imports -Wno-unused-matches -Wno-unused-top-binds #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--max-case-expand=8" @-}

-- | Liquid-only ordinal arithmetic lemmas used by proof-bearing clients.
module DatraOrdinal.LiquidInternal
  ( ordinalAddLeftBelow
  , ordinalAddRightBelow
  , ordinalAddRightInjective
  , ordinalAddSeparatesLeft
  , ordinalSubtractBetween
  , ordinalLongNotBelowOmega
  ) where

import Numeric.Natural (Natural)
import DatraOrdinal.Internal
  ( Ordinal(..)
  , addCoefficients
  , addOrdinals
  , canonicalCoefficients
  , coefficientsLT
  , lexicographicLT
  , listLength
  , omega
  , ordinalLT
  )

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

{-@ type CanonicalCoefficients = { values:[Natural] | canonicalCoefficients values } @-}

-- | The left summand embeds as an initial segment of an ordinal sum.
{-@
ordinalAddLeftBelow
  :: prefix:Ordinal
  -> suffix:Ordinal
  -> value:{Ordinal | ordinalLT value prefix}
  -> { proof:() | ordinalLT value (addOrdinals prefix suffix) }
@-}
ordinalAddLeftBelow :: Ordinal -> Ordinal -> Ordinal -> ()
ordinalAddLeftBelow (Ordinal prefix) (Ordinal suffix) (Ordinal value) =
  addCoefficientsLeftBelow prefix suffix value

{-@
addCoefficientsLeftBelow
  :: prefix:[Natural]
  -> suffix:CanonicalCoefficients
  -> value:{[Natural] | coefficientsLT value prefix}
  -> { proof:() | coefficientsLT value (addCoefficients prefix suffix) }
@-}
addCoefficientsLeftBelow :: [Natural] -> [Natural] -> [Natural] -> ()
{-@ ple addCoefficientsLeftBelow @-}
addCoefficientsLeftBelow prefix [] value =
  coefficientsLT value prefix `seq` ()
addCoefficientsLeftBelow [] suffix value =
  coefficientsLT value [] `seq`
    coefficientsLT value (addCoefficients [] suffix) `seq` ()
addCoefficientsLeftBelow prefix@(_ : _) suffix@(_ : _) value
  | listLength prefix < listLength suffix =
      coefficientsLT value prefix `seq`
        coefficientsLT value (addCoefficients prefix suffix) `seq` ()
  | listLength value < listLength prefix =
      coefficientsLT value (addCoefficients prefix suffix) `seq` ()
  | otherwise =
      addCoefficientsPreservesLexBelow prefix suffix value `seq`
        coefficientsLT value (addCoefficients prefix suffix) `seq` ()

{-@
addCoefficientsPreservesLexBelow
  :: prefix:[Natural]
  -> suffix:{CanonicalCoefficients | 0 < len suffix && len suffix <= len prefix}
  -> value:{[Natural] |
       len value == len prefix && lexicographicLT value prefix}
  -> { proof:() |
       lexicographicLT value (addCoefficients prefix suffix) }
@-}
{-@ ple addCoefficientsPreservesLexBelow @-}
addCoefficientsPreservesLexBelow :: [Natural] -> [Natural] -> [Natural] -> ()
addCoefficientsPreservesLexBelow [] _ _ = ()
addCoefficientsPreservesLexBelow _ [] _ = ()
addCoefficientsPreservesLexBelow _ _ [] = ()
addCoefficientsPreservesLexBelow
  prefix@(prefixHead : prefixTail)
  suffix@(suffixHead : _)
  (valueHead : valueTail)
  | listLength prefix == listLength suffix = suffixHead `seq` ()
  | valueHead < prefixHead = ()
  | valueHead > prefixHead = ()
  | otherwise =
      addCoefficientsPreservesLexBelow prefixTail suffix valueTail

-- | Adding a fixed prefix is strictly monotone in its right argument.
{-@
ordinalAddRightBelow
  :: prefix:Ordinal
  -> left:Ordinal
  -> right:{Ordinal | ordinalLT left right}
  -> { proof:() |
       ordinalLT (addOrdinals prefix left) (addOrdinals prefix right) }
@-}
ordinalAddRightBelow :: Ordinal -> Ordinal -> Ordinal -> ()
ordinalAddRightBelow (Ordinal prefix) (Ordinal left) (Ordinal right) =
  addCoefficientsRightBelow prefix left right

{-@
addCoefficientsRightBelow
  :: prefix:[Natural]
  -> left:CanonicalCoefficients
  -> right:{CanonicalCoefficients | coefficientsLT left right}
  -> { proof:() |
       coefficientsLT (addCoefficients prefix left)
         (addCoefficients prefix right) }
@-}
addCoefficientsRightBelow :: [Natural] -> [Natural] -> [Natural] -> ()
{-@ ple addCoefficientsRightBelow @-}
addCoefficientsRightBelow [] [] [] = coefficientsLT [] [] `seq` ()
addCoefficientsRightBelow [] [] right@(_ : _) =
  coefficientsLT [] (addCoefficients [] right) `seq` ()
addCoefficientsRightBelow [] left@(_ : _) [] =
  coefficientsLT left [] `seq` ()
addCoefficientsRightBelow [] left@(_ : _) right@(_ : _) =
  coefficientsLT left right `seq`
    coefficientsLT (addCoefficients [] left)
      (addCoefficients [] right) `seq` ()
addCoefficientsRightBelow prefix@(_ : _) [] [] =
  coefficientsLT [] [] `seq` ()
addCoefficientsRightBelow prefix@(_ : _) [] right@(_ : _) =
  addCoefficientsPrefixBelowSum prefix right `seq`
    coefficientsLT (addCoefficients prefix [])
      (addCoefficients prefix right) `seq` ()
addCoefficientsRightBelow _ left@(_ : _) [] = coefficientsLT left [] `seq` ()
addCoefficientsRightBelow prefix@(_ : prefixTail) left@(_ : _) right@(_ : _)
  | listLength prefix < listLength left =
      coefficientsLT left right `seq`
        coefficientsLT (addCoefficients prefix left)
          (addCoefficients prefix right) `seq` ()
  | listLength prefix == listLength left =
      addCoefficientsAtLeftLengthBelow prefix left right
  | listLength prefix < listLength right =
      coefficientsLT (addCoefficients prefix left)
        (addCoefficients prefix right) `seq` ()
  | listLength prefix == listLength right =
      coefficientsLT (addCoefficients prefix left)
        (addCoefficients prefix right) `seq` ()
  | otherwise =
      addCoefficientsRightBelow prefixTail left right `seq`
        coefficientsLT (addCoefficients prefix left)
          (addCoefficients prefix right) `seq` ()

{-@
addCoefficientsPrefixBelowSum
  :: prefix:[Natural]
  -> suffix:{CanonicalCoefficients | 0 < len suffix}
  -> { proof:() |
       coefficientsLT prefix (addCoefficients prefix suffix) }
@-}
{-@ ple addCoefficientsPrefixBelowSum @-}
addCoefficientsPrefixBelowSum :: [Natural] -> [Natural] -> ()
addCoefficientsPrefixBelowSum [] suffix =
  coefficientsLT [] (addCoefficients [] suffix) `seq` ()
addCoefficientsPrefixBelowSum _ [] = ()
addCoefficientsPrefixBelowSum prefix@(_ : prefixTail) suffix@(_ : _)
  | listLength prefix < listLength suffix =
      coefficientsLT prefix (addCoefficients prefix suffix) `seq` ()
  | listLength prefix == listLength suffix =
      coefficientsLT prefix (addCoefficients prefix suffix) `seq` ()
  | otherwise =
      addCoefficientsPrefixBelowSum prefixTail suffix `seq`
        coefficientsLT prefix (addCoefficients prefix suffix) `seq` ()

{-@
addCoefficientsAtLeftLengthBelow
  :: prefix:[Natural]
  -> left:{CanonicalCoefficients | len left == len prefix}
  -> right:{CanonicalCoefficients | coefficientsLT left right}
  -> { proof:() |
       coefficientsLT (addCoefficients prefix left)
         (addCoefficients prefix right) }
@-}
{-@ ple addCoefficientsAtLeftLengthBelow @-}
addCoefficientsAtLeftLengthBelow :: [Natural] -> [Natural] -> [Natural] -> ()
addCoefficientsAtLeftLengthBelow [] [] [] = coefficientsLT [] [] `seq` ()
addCoefficientsAtLeftLengthBelow [] [] right@(_ : _) =
  coefficientsLT (addCoefficients [] [])
    (addCoefficients [] right) `seq` ()
addCoefficientsAtLeftLengthBelow [] (_ : _) _ = ()
addCoefficientsAtLeftLengthBelow (_ : _) [] _ = ()
addCoefficientsAtLeftLengthBelow _ left@(_ : _) [] =
  coefficientsLT left [] `seq` ()
addCoefficientsAtLeftLengthBelow
  prefix@(prefixHead : _)
  left@(leftHead : leftTail)
  right@(rightHead : rightTail)
  | listLength left < listLength right =
      coefficientsLT (addCoefficients prefix left)
        (addCoefficients prefix right) `seq` ()
  | leftHead < rightHead =
      addCoefficientsEqualLengthShape prefix left `seq`
        addCoefficientsEqualLengthShape prefix right `seq`
          lexicographicLT
            ((prefixHead + leftHead) : leftTail)
            ((prefixHead + rightHead) : rightTail) `seq`
              coefficientsLT (addCoefficients prefix left)
                (addCoefficients prefix right) `seq` ()
  | leftHead > rightHead = coefficientsLT left right `seq` ()
  | otherwise =
      addCoefficientsEqualLengthShape prefix left `seq`
        addCoefficientsEqualLengthShape prefix right `seq`
          lexicographicLT leftTail rightTail `seq`
            lexicographicLT
              ((prefixHead + leftHead) : leftTail)
              ((prefixHead + rightHead) : rightTail) `seq`
                coefficientsLT (addCoefficients prefix left)
                  (addCoefficients prefix right) `seq` ()

{-@
addCoefficientsEqualLengthShape
  :: prefix:[Natural]
  -> suffix:{[Natural] | 0 < len suffix && len suffix == len prefix}
  -> { proof:() |
       addCoefficients prefix suffix
         == consNatural (head prefix + head suffix) (tail suffix) }
@-}
{-@ ple addCoefficientsEqualLengthShape @-}
addCoefficientsEqualLengthShape :: [Natural] -> [Natural] -> ()
addCoefficientsEqualLengthShape [] _ = ()
addCoefficientsEqualLengthShape _ [] = ()
addCoefficientsEqualLengthShape prefix@(_ : _) suffix@(_ : _)
  | listLength prefix < listLength suffix = ()
  | listLength prefix == listLength suffix = ()
  | otherwise = ()

{-@ reflect consNatural @-}
consNatural :: Natural -> [Natural] -> [Natural]
consNatural value values = value : values

-- | Adding a fixed prefix is injective in its right argument.
{-@
ordinalAddRightInjective
  :: prefix:Ordinal
  -> left:Ordinal
  -> right:Ordinal
  -> { proof:() |
       addOrdinals prefix left == addOrdinals prefix right
         => left == right }
@-}
ordinalAddRightInjective :: Ordinal -> Ordinal -> Ordinal -> ()
ordinalAddRightInjective (Ordinal prefix) (Ordinal left) (Ordinal right) =
  addCoefficientsRightInjective prefix left right

{-@
addCoefficientsRightInjective
  :: prefix:[Natural]
  -> left:CanonicalCoefficients
  -> right:CanonicalCoefficients
  -> { proof:() |
       addCoefficients prefix left == addCoefficients prefix right
         => left == right }
@-}
addCoefficientsRightInjective :: [Natural] -> [Natural] -> [Natural] -> ()
{-@ ple addCoefficientsRightInjective @-}
addCoefficientsRightInjective prefix left right
  | left == right = ()
  | coefficientsLT left right =
      addCoefficientsRightBelow prefix left right `seq`
        coefficientsLTIrreflexive (addCoefficients prefix left)
  | coefficientsLT right left =
      addCoefficientsRightBelow prefix right left `seq`
        coefficientsLTIrreflexive (addCoefficients prefix right)
  | otherwise = coefficientsOrderTotal left right

{-@
coefficientsOrderTotal
  :: left:[Natural]
  -> right:[Natural]
  -> { proof:() |
       not (coefficientsLT left right)
       && not (coefficientsLT right left)
         => left == right }
@-}
{-@ ple coefficientsOrderTotal @-}
coefficientsOrderTotal :: [Natural] -> [Natural] -> ()
coefficientsOrderTotal [] [] = ()
coefficientsOrderTotal [] right@(_ : _) =
  coefficientsLT [] right `seq` ()
coefficientsOrderTotal left@(_ : _) [] =
  coefficientsLT [] left `seq` ()
coefficientsOrderTotal
  left@(leftHead : leftTail)
  right@(rightHead : rightTail)
  | listLength left < listLength right =
      coefficientsLT left right `seq` ()
  | listLength left > listLength right =
      coefficientsLT right left `seq` ()
  | leftHead < rightHead =
      coefficientsLT left right `seq` ()
  | leftHead > rightHead =
      coefficientsLT right left `seq` ()
  | otherwise = coefficientsOrderTotal leftTail rightTail

-- | No point in the left initial segment is in the translated right segment.
{-@
ordinalAddSeparatesLeft
  :: prefix:Ordinal
  -> leftValue:{Ordinal | ordinalLT leftValue prefix}
  -> rightValue:Ordinal
  -> { proof:() |
       leftValue /= addOrdinals prefix rightValue }
@-}
ordinalAddSeparatesLeft :: Ordinal -> Ordinal -> Ordinal -> ()
ordinalAddSeparatesLeft prefix leftValue rightValue =
  case ordinalAddLeftBelow prefix rightValue leftValue of
    () -> ordinalLTIrreflexive leftValue

{-@
ordinalLTIrreflexive
  :: value:Ordinal
  -> { proof:() | not (ordinalLT value value) }
@-}
ordinalLTIrreflexive :: Ordinal -> ()
ordinalLTIrreflexive (Ordinal value) = coefficientsLTIrreflexive value

{-@
coefficientsLTIrreflexive
  :: value:[Natural]
  -> { proof:() | not (coefficientsLT value value) }
@-}
{-@ ple coefficientsLTIrreflexive @-}
coefficientsLTIrreflexive :: [Natural] -> ()
coefficientsLTIrreflexive [] = ()
coefficientsLTIrreflexive (_ : values) = coefficientsLTIrreflexive values

-- | Subtraction decomposes every point in the right interval of a sum.
{-@
ordinalSubtractBetween
  :: prefix:Ordinal
  -> suffix:Ordinal
  -> value:{Ordinal |
       not (ordinalLT value prefix)
       && ordinalLT value (addOrdinals prefix suffix)}
  -> { difference:Ordinal |
       ordinalLT difference suffix
       && addOrdinals prefix difference == value }
@-}
ordinalSubtractBetween :: Ordinal -> Ordinal -> Ordinal -> Ordinal
ordinalSubtractBetween
  (Ordinal prefix)
  (Ordinal suffix)
  (Ordinal value)
  | listLength value > listLength prefix =
      addCoefficientsRightReflectsBelow prefix value suffix `seq`
        Ordinal value
  | listLength value < listLength prefix =
      coefficientsLT value prefix `seq` Ordinal []
  | otherwise =
      let difference = subtractEqualCoefficients prefix value
      in addCoefficientsRightReflectsBelow prefix difference suffix `seq`
          Ordinal difference

{-@ reflect subtractEqualCoefficients @-}
{-@
subtractEqualCoefficients
  :: prefix:[Natural]
  -> value:{[Natural] |
       len value == len prefix && not (lexicographicLT value prefix)}
  -> { difference:[Natural] |
       canonicalCoefficients difference
       && addCoefficients prefix difference == value }
@-}
subtractEqualCoefficients :: [Natural] -> [Natural] -> [Natural]
subtractEqualCoefficients [] [] = []
subtractEqualCoefficients [] (_ : _) = []
subtractEqualCoefficients (_ : _) [] = []
subtractEqualCoefficients
  prefix@(prefixHead : prefixTail)
  value@(valueHead : valueTail)
  | valueHead < prefixHead = lexicographicLT value prefix `seq` []
  | valueHead == prefixHead =
      case subtractEqualCoefficients prefixTail valueTail of
        [] ->
          addCoefficientsLift prefixHead prefixTail [] valueTail `seq` []
        difference@(_ : _) ->
          addCoefficientsLift
            prefixHead prefixTail difference valueTail `seq` difference
  | otherwise =
      addCoefficientsEqualLengthShape prefix difference `seq` difference
  where
    difference
      = (valueHead - prefixHead) : valueTail

{-@
addCoefficientsLift
  :: leading:Natural
  -> prefix:[Natural]
  -> suffix:[Natural]
  -> result:{[Natural] |
       len result == len prefix
       && addCoefficients prefix suffix == result}
  -> { proof:() |
       addCoefficients (consNatural leading prefix) suffix
         == consNatural leading result }
@-}
{-@ ple addCoefficientsLift @-}
addCoefficientsLift :: Natural -> [Natural] -> [Natural] -> [Natural] -> ()
addCoefficientsLift _ _ [] _ = ()
addCoefficientsLift leading prefix suffix@(_ : _) result
  | listLength prefix < listLength suffix = ()
  | listLength prefix == listLength suffix =
      addCoefficients (leading : prefix) suffix `seq` ()
  | otherwise = addCoefficients (leading : prefix) suffix `seq` ()

{-@
addCoefficientsRightReflectsBelow
  :: prefix:[Natural]
  -> left:CanonicalCoefficients
  -> right:CanonicalCoefficients
  -> { proof:() |
       coefficientsLT (addCoefficients prefix left)
         (addCoefficients prefix right)
         => coefficientsLT left right }
@-}
addCoefficientsRightReflectsBelow :: [Natural] -> [Natural] -> [Natural] -> ()
addCoefficientsRightReflectsBelow prefix left right
  | not (coefficientsLT
      (addCoefficients prefix left)
      (addCoefficients prefix right)) = ()
  | coefficientsLT left right = ()
  | coefficientsLT right left =
      addCoefficientsRightBelow prefix right left `seq`
        coefficientsLTAsymmetric
          (addCoefficients prefix left)
          (addCoefficients prefix right)
  | otherwise =
      coefficientsOrderTotal left right `seq`
        coefficientsLTIrreflexive (addCoefficients prefix left)

{-@
coefficientsLTAsymmetric
  :: left:[Natural]
  -> right:{[Natural] | coefficientsLT left right}
  -> { proof:() | not (coefficientsLT right left) }
@-}
{-@ ple coefficientsLTAsymmetric @-}
coefficientsLTAsymmetric :: [Natural] -> [Natural] -> ()
coefficientsLTAsymmetric [] right = coefficientsLT right [] `seq` ()
coefficientsLTAsymmetric left@(_ : _) [] = coefficientsLT left [] `seq` ()
coefficientsLTAsymmetric
  left@(leftHead : leftTail)
  right@(rightHead : rightTail)
  | listLength left < listLength right =
      coefficientsLT right left `seq` ()

  | listLength left > listLength right =
      coefficientsLT left right `seq` ()
  | leftHead < rightHead =
      coefficientsLT right left `seq` ()
  | leftHead > rightHead =
      coefficientsLT left right `seq` ()
  | otherwise =
      coefficientsLTAsymmetric leftTail rightTail `seq`
        coefficientsLT right left `seq` ()

{-@
ordinalLongNotBelowOmega
  :: values:{CanonicalCoefficients | len values >= 2}
  -> { proof:() | not (ordinalLT (Ordinal values) omega) }
@-}
ordinalLongNotBelowOmega :: [Natural] -> ()
ordinalLongNotBelowOmega values@[leading, lower]
  | leading < 1 = canonicalCoefficients values `seq` ()
  | leading > 1 =
      coefficientsLT values [1, 0] `seq`
        ordinalLT (Ordinal values) omega `seq` ()
  | otherwise =
      lexicographicLT [lower] [0] `seq`
        lexicographicLT values [1, 0] `seq`
          coefficientsLT values [1, 0] `seq`
            ordinalLT (Ordinal values) omega `seq` ()
ordinalLongNotBelowOmega values@(_ : _ : _ : _) =
  coefficientsLT values [1, 0] `seq`
    ordinalLT (Ordinal values) omega `seq` ()
ordinalLongNotBelowOmega _ = ()
