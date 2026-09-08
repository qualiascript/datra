{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module Chains
  ( Ordinal
  , coefficients
  , ordinal
  , finiteOrdinal
  , omega
  , ordinalLT
  , positionMatches
  , addOrdinals
  , Chain
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

-- | A reflected strict comparison used by chain refinements. It agrees with
-- the 'Ord' instance while remaining visible to LiquidHaskell's logic.
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
          ordinalLT (chainPosition objectValue) chainOrderType }
  , chainPositionInjective :: left:object -> right:object ->
      { proof:() |
          chainPosition left == chainPosition right => left == right }
  , chainPositionSurjective :: position:Ordinal ->
      { proof:() |
          ordinalLT position chainOrderType
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
       { proof:() | ordinalLT (position objectValue) orderType })
  -> (left:object -> right:object ->
       { proof:() | position left == position right => left == right })
  -> (ordinalValue:Ordinal ->
       { proof:() |
           ordinalLT ordinalValue orderType
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
      | ordinalLT position (chainOrderType left) =
          Left <$> chainObjectAt left position
      | otherwise =
          subtractOrdinal (chainOrderType left) position
            >>= fmap Right . chainObjectAt right

-- The ordinal arithmetic lemmas for sum are the trusted translation of
-- Lean's `Ordinal.type_sum_lex` proof. The executable inverse above witnesses
-- the same left-then-right order.

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

naturalAtOrdinal :: Ordinal -> Maybe Natural
naturalAtOrdinal (Ordinal []) = Just 0
naturalAtOrdinal (Ordinal [value]) = Just value
naturalAtOrdinal _ = Nothing
