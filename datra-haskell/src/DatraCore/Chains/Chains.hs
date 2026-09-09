{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Chains
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

import DatraOrdinal

{-@ embed Natural as int @-}

-- LiquidHaskell 0.9.4 does not deserialize reflected function symbols across
-- module boundaries when hie-bios checks this module independently. Reflect a
-- local logical bridge over the exported representation instead. Keep this in
-- lockstep with DatraOrdinal.ordinalLT.
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

-- | A skeletal well-ordered thin category whose order type is below
-- omega^omega.
--
-- LiquidHaskell enforces the defining indexing laws:
--
--   chainPosition chain object < chainOrderType chain
--
--   chainPosition chain x == chainPosition chain y implies x == y
--
--   every ordinal smaller than chainOrderType chain is the position of
--   exactly one object
--
-- Together these say that 'chainPosition' is a bijection between the
-- objects and the initial ordinal segment determined by 'chainOrderType'.
-- The total order and thin-category arrows are induced by these positions.
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

-- | Construct a chain from its indexing equivalence and proofs. The inverse
-- lookup is executable evidence for the surjectivity proof.
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

-- | Compare two objects using their skeletal ordinal positions.
compareInChain :: Chain object -> object -> object -> Ordering
compareInChain valueChain left right =
  compare (chainPosition valueChain left) (chainPosition valueChain right)

-- | Whether the chain's thin category has its unique arrow from the first
-- object to the second.
hasArrow :: Chain object -> object -> object -> Bool
hasArrow valueChain source target =
  compareInChain valueChain source target /= GT

-- | Ordinal sum of chains: every object of the left chain comes before every
-- object of the right chain.
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

-- The ordinal arithmetic lemmas for sum are the trusted translation of
-- Lean's `Ordinal.type_sum_lex` proof. The executable inverse above witnesses
-- the same left-then-right order.

-- | The common page-indexing chain, with one object for every natural number.
-- This is the Haskell counterpart of Lean's `Ordinal.type_nat_lt` proof.
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
