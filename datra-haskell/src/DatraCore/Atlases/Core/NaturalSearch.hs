{-# LANGUAGE CPP #-}
#include "../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Inclusive finite search and its canonical least successful index.
module NaturalSearch (search, least, trim, unique, congruent) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

{-@ reflect search @-}
{-@ search :: matches:(Natural -> Bool) -> candidate:Natural -> remaining:Natural
      -> {result:Maybe ({found:Natural | candidate <= found && found <= candidate + remaining
           && matches found}) | matches (candidate + remaining) => result /= Nothing} / [remaining] @-}
search :: (Natural -> Bool) -> Natural -> Natural -> Maybe Natural
search matches candidate remaining
  | matches candidate = Just candidate
  | remaining == 0 = Nothing
  | otherwise = search matches (candidate + 1) (remaining - 1)

{-@ least :: matches:(Natural -> Bool) -> candidate:Natural -> remaining:Natural
      -> found:{Natural | search matches candidate remaining == Just found}
      -> earlier:{Natural | candidate <= earlier && earlier < found}
      -> {not (matches earlier)} / [remaining] @-}
least :: (Natural -> Bool) -> Natural -> Natural -> Natural -> Natural -> ()
least matches candidate remaining found earlier
  | matches candidate = ()
  | remaining == 0 = ()
  | earlier == candidate = ()
  | otherwise = least matches (candidate + 1) (remaining - 1) found earlier

{-@ trim :: matches:(Natural -> Bool) -> candidate:Natural -> remaining:Natural
      -> found:{Natural | candidate <= found && matches found
           && search matches candidate remaining == Just found}
      -> {search matches candidate (found - candidate) == Just found} / [remaining] @-}
trim :: (Natural -> Bool) -> Natural -> Natural -> Natural -> ()
trim matches candidate remaining found
  | matches candidate = ()
  | remaining == 0 = ()
  | otherwise = trim matches (candidate + 1) (remaining - 1) found

{-@ unique :: matches:(Natural -> Bool)
      -> left:{Natural | search matches 0 left == Just left}
      -> right:{Natural | search matches 0 right == Just right}
      -> {left == right} @-}
unique :: (Natural -> Bool) -> Natural -> Natural -> ()
unique matches left right
  | left < right = search matches 0 left `seq` least matches 0 right right left
  | right < left = search matches 0 right `seq` least matches 0 left left right
  | otherwise = ()

-- | Pointwise equal tests select the same result over every finite interval.
{-@ congruent :: left:(Natural -> Bool) -> right:(Natural -> Bool)
      -> (value:Natural -> {left value == right value})
      -> candidate:Natural -> remaining:Natural
      -> {search left candidate remaining == search right candidate remaining} / [remaining] @-}
congruent
  :: (Natural -> Bool) -> (Natural -> Bool) -> (Natural -> ()) -> Natural -> Natural -> ()
congruent left right same candidate remaining =
  same candidate `seq`
    if left candidate
      then ()
      else if remaining == 0
        then ()
        else congruent left right same (candidate + 1) (remaining - 1)
