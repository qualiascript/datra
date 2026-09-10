{-# LANGUAGE CPP #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden chain representation and proof-bearing operations.
module Chain.Internal
  ( Chain
  , chainOrdinalLT
  , positionMatches
  , chainOrderType
  , chainPosition
  , chainObjectAt
  , chainPositionBelow
  , chainPositionInjective
  , chainPositionSurjective
  , chain
  , compareInChain
  , hasArrow
  , sumChains
  , spine
  ) where

import Numeric.Natural (Natural)

import DatraOrdinal.Internal
  ( Ordinal(..)
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omega
  , subtractOrdinal
  )

{-@ embed Natural as int @-}

{-@ reflect chainOrdinalLT @-}
chainOrdinalLT :: Ordinal -> Ordinal -> Bool
chainOrdinalLT (Ordinal left) (Ordinal right) =
  chainListLength left < chainListLength right
    || chainListLength left == chainListLength right
      && chainLexicographicLT left right

{-@ reflect chainListLength @-}
chainListLength :: [a] -> Int
chainListLength [] = 0
chainListLength (_ : values) = 1 + chainListLength values

{-@ reflect chainLexicographicLT @-}
chainLexicographicLT :: [Natural] -> [Natural] -> Bool
chainLexicographicLT [] _ = False
chainLexicographicLT _ [] = False
chainLexicographicLT (left : lefts) (right : rights)
  | left < right = True
  | left > right = False
  | otherwise = chainLexicographicLT lefts rights

{-@ reflect positionMatches @-}
positionMatches :: (object -> Ordinal) -> Ordinal -> Maybe object -> Bool
positionMatches _ _ Nothing = False
positionMatches position expected (Just object) = position object == expected

{-@
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainObjectAt :: Ordinal -> Maybe object
  , chainPositionBelow :: objectValue:object ->
      { proof:() |
          chainOrdinalLT (chainPosition objectValue) chainOrderType }
  , chainPositionInjective :: left:object -> right:object ->
      { proof:() |
          chainPosition left == chainPosition right => left == right }
  , chainPositionSurjective :: position:Ordinal ->
      { proof:() |
          chainOrdinalLT position chainOrderType
            => positionMatches chainPosition position
                 (chainObjectAt position) }
  }
@-}
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  , chainObjectAt :: Ordinal -> Maybe object
  , chainPositionBelow :: object -> ()
  , chainPositionInjective :: object -> object -> ()
  , chainPositionSurjective :: Ordinal -> ()
  }

-- | Construct a chain from its indexing equivalence and proofs.
{-@
chain
  :: orderType:Ordinal
  -> position:(object -> Ordinal)
  -> objectAt:(Ordinal -> Maybe object)
  -> (objectValue:object ->
       { proof:() | chainOrdinalLT (position objectValue) orderType })
  -> (left:object -> right:object ->
       { proof:() | position left == position right => left == right })
  -> (ordinalValue:Ordinal ->
       { proof:() |
           chainOrdinalLT ordinalValue orderType
             => positionMatches position ordinalValue
                  (objectAt ordinalValue) })
  -> Chain object
@-}
chain
  :: Ordinal
  -> (object -> Ordinal)
  -> (Ordinal -> Maybe object)
  -> (object -> ())
  -> (object -> object -> ())
  -> (Ordinal -> ())
  -> Chain object
chain = Chain

compareInChain :: Chain object -> object -> object -> Ordering
compareInChain valueChain left right =
  compare (chainPosition valueChain left) (chainPosition valueChain right)

hasArrow :: Chain object -> object -> object -> Bool
hasArrow valueChain source target =
  compareInChain valueChain source target /= GT

{-@ assume sumChains :: Chain left -> Chain right -> Chain (Either left right) @-}
{-@ ignore sumChains @-}
sumChains :: Chain left -> Chain right -> Chain (Either left right)
sumChains left right =
  Chain
    { chainOrderType =
        addOrdinals (chainOrderType left) (chainOrderType right)
    , chainPosition = positionInSum
    , chainObjectAt = objectInSum
    , chainPositionBelow = const ()
    , chainPositionInjective = \_ _ -> ()
    , chainPositionSurjective = const ()
    }
  where
    positionInSum (Left object) = chainPosition left object
    positionInSum (Right object) =
      addOrdinals (chainOrderType left) (chainPosition right object)

    objectInSum position
      | chainOrdinalLT position (chainOrderType left) =
          Left <$> chainObjectAt left position
      | otherwise =
          subtractOrdinal (chainOrderType left) position
            >>= fmap Right . chainObjectAt right

{-@ assume spine :: Chain Natural @-}
{-@ ignore spine @-}
spine :: Chain Natural
spine =
  Chain
    omega
    finiteOrdinal
    naturalAtOrdinal
    (const ())
    (\_ _ -> ())
    (const ())
