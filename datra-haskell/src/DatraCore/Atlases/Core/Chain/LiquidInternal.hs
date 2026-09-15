{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--prune-unsorted" @-}
{-@ LIQUID "--max-case-expand=8" @-}

-- | Liquid-checked construction of ordinal sums of chains.
module Chain.LiquidInternal
  ( sumChains
  ) where

import Chain.Internal
  ( Chain
  , chain
  , chainLookup
  , chainOrderType
  , chainOrdinalLT
  , chainPosition
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , positionMatches
  )
import DatraOrdinal.Internal
  ( Ordinal
  , addOrdinals
  )
import DatraOrdinal.LiquidInternal
  ( ordinalAddLeftBelow
  , ordinalAddRightBelow
  , ordinalAddRightInjective
  , ordinalAddSeparatesLeft
  , ordinalSubtractBetween
  )

sumChains :: Chain left -> Chain right -> Chain (Either left right)
sumChains left right =
  chain
    (addOrdinals (chainOrderType left) (chainOrderType right))
    (sumChainPosition left right)
    (sumChainLookup left right)
    (sumChainPositionBelow left right)
    (sumChainPositionInjective left right)
    (sumChainPositionSurjective left right)

{-@ reflect sumChainPosition @-}
sumChainPosition :: Chain left -> Chain right -> Either left right -> Ordinal
sumChainPosition left _ (Left object) = chainPosition left object
sumChainPosition left right (Right object) =
  addOrdinals (chainOrderType left) (chainPosition right object)

{-@ reflect sumChainLookup @-}
sumChainLookup
  :: Chain left -> Chain right -> Ordinal -> Maybe (Either left right)
sumChainLookup left right position
  | chainOrdinalLT position (chainOrderType left) =
      leftMaybe (chainLookup left position)
  | chainOrdinalLT position sumOrder =
      rightMaybe
        (chainLookup right
          (ordinalSubtractBetween
            (chainOrderType left) (chainOrderType right) position))
  | otherwise = Nothing
  where
    sumOrder = addOrdinals (chainOrderType left) (chainOrderType right)

{-@ reflect leftMaybe @-}
leftMaybe :: Maybe left -> Maybe (Either left right)
leftMaybe Nothing = Nothing
leftMaybe (Just object) = Just (Left object)

{-@ reflect rightMaybe @-}
rightMaybe :: Maybe right -> Maybe (Either left right)
rightMaybe Nothing = Nothing
rightMaybe (Just object) = Just (Right object)

{-@
sumChainPositionBelow
  :: left:Chain leftObject
  -> right:Chain rightObject
  -> objectValue:Either leftObject rightObject
  -> { proof:() |
       chainOrdinalLT (sumChainPosition left right objectValue)
         (addOrdinals (chainOrderType left) (chainOrderType right)) }
@-}
sumChainPositionBelow
  :: Chain left -> Chain right -> Either left right -> ()
sumChainPositionBelow left right (Left object) =
  chainPositionBelow left object `seq`
    ordinalAddLeftBelow
      (chainOrderType left)
      (chainOrderType right)
      (chainPosition left object)
sumChainPositionBelow left right (Right object) =
  chainPositionBelow right object `seq`
    ordinalAddRightBelow
      (chainOrderType left)
      (chainPosition right object)
      (chainOrderType right)

{-@
sumChainPositionInjective
  :: left:Chain leftObject
  -> right:Chain rightObject
  -> first:Either leftObject rightObject
  -> second:Either leftObject rightObject
  -> { proof:() |
       sumChainPosition left right first
         == sumChainPosition left right second
         => first == second }
@-}
sumChainPositionInjective
  :: Chain left
  -> Chain right
  -> Either left right
  -> Either left right
  -> ()
sumChainPositionInjective left _ (Left first) (Left second) =
  chainPositionInjective left first second
sumChainPositionInjective left right (Right first) (Right second) =
  ordinalAddRightInjective
    (chainOrderType left)
    (chainPosition right first)
    (chainPosition right second) `seq`
      chainPositionInjective right first second
sumChainPositionInjective left right (Left first) (Right second) =
  chainPositionBelow left first `seq`
    ordinalAddSeparatesLeft
      (chainOrderType left)
      (chainPosition left first)
      (chainPosition right second)
sumChainPositionInjective left right (Right first) (Left second) =
  chainPositionBelow left second `seq`
    ordinalAddSeparatesLeft
      (chainOrderType left)
      (chainPosition left second)
      (chainPosition right first)

{-@
sumChainPositionSurjective
  :: left:Chain leftObject
  -> right:Chain rightObject
  -> position:Ordinal
  -> { proof:() |
       chainOrdinalLT position
         (addOrdinals (chainOrderType left) (chainOrderType right))
         => positionMatches (sumChainPosition left right) position
              (sumChainLookup left right position) }
@-}
sumChainPositionSurjective :: Chain left -> Chain right -> Ordinal -> ()
sumChainPositionSurjective left right position
  | not (chainOrdinalLT position sumOrder) = ()
  | chainOrdinalLT position (chainOrderType left) =
      chainPositionSurjective left position `seq`
        case chainLookup left position of
          Nothing -> ()
          Just object ->
            positionMatches
              (chainPosition left) position (Just object) `seq`
                leftMaybe (Just object) `seq`
                  sumChainPosition left right (Left object) `seq`
                    sumChainLookup left right position `seq`
                      positionMatches
                        (sumChainPosition left right)
                        position
                        (sumChainLookup left right position) `seq` ()
  | otherwise =
      let difference = ordinalSubtractBetween
            (chainOrderType left) (chainOrderType right) position
      in chainPositionSurjective right difference `seq`
          case chainLookup right difference of
            Nothing -> ()
            Just object ->
              positionMatches
                (chainPosition right) difference (Just object) `seq`
                  rightMaybe (Just object) `seq`
                    sumChainPosition left right (Right object) `seq`
                      sumChainLookup left right position `seq`
                        positionMatches
                          (sumChainPosition left right)
                          position
                          (sumChainLookup left right position) `seq` ()
  where
    sumOrder = addOrdinals (chainOrderType left) (chainOrderType right)
