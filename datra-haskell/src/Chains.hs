module Chains
  ( Ordinal
  , coefficients
  , ordinal
  , finiteOrdinal
  , omega
  , addOrdinals
  , Chain
  , chainOrderType
  , chainPosition
  , unsafeChain
  , compareInChain
  , hasArrow
  , sumChains
  , spine
  ) where

import Numeric.Natural (Natural)

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

-- | Ordinal addition. This is generally not commutative.
addOrdinals :: Ordinal -> Ordinal -> Ordinal
addOrdinals left@(Ordinal leftCoefficients) right@(Ordinal rightCoefficients)
  | null rightCoefficients = left
  | length leftCoefficients < length rightCoefficients = right
  | otherwise =
      Ordinal
        (higherLeftCoefficients
          ++ (matchingLeftCoefficient + rightLeadingCoefficient)
            : rightLowerCoefficients)
  where
    numberOfHigherLeftCoefficients =
      length leftCoefficients - length rightCoefficients

    (higherLeftCoefficients, matchingAndLowerLeftCoefficients) =
      splitAt numberOfHigherLeftCoefficients leftCoefficients

    matchingLeftCoefficient = head matchingAndLowerLeftCoefficients
    rightLeadingCoefficient = head rightCoefficients
    rightLowerCoefficients = tail rightCoefficients

-- | A skeletal well-ordered thin category whose order type is below
-- omega^omega.
--
-- Vanilla Haskell cannot enforce the defining indexing laws:
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
data Chain object = Chain
  { chainOrderType :: Ordinal
  , chainPosition :: object -> Ordinal
  }

-- | Assert that an order type and position function satisfy the laws
-- documented on 'Chain'.
unsafeChain :: Ordinal -> (object -> Ordinal) -> Chain object
unsafeChain = Chain

-- | Compare two objects using their skeletal ordinal positions.
compareInChain :: Chain object -> object -> object -> Ordering
compareInChain chain left right =
  compare (chainPosition chain left) (chainPosition chain right)

-- | Whether the chain's thin category has its unique arrow from the first
-- object to the second.
hasArrow :: Chain object -> object -> object -> Bool
hasArrow chain source target =
  compareInChain chain source target /= GT

-- | Ordinal sum of chains: every object of the left chain comes before every
-- object of the right chain.
sumChains :: Chain left -> Chain right -> Chain (Either left right)
sumChains left right =
  Chain
    { chainOrderType =
        addOrdinals (chainOrderType left) (chainOrderType right)
    , chainPosition = positionInSum
    }
  where
    positionInSum (Left object) = chainPosition left object
    positionInSum (Right object) =
      addOrdinals (chainOrderType left) (chainPosition right object)

-- | The common page-indexing chain, with one object for every natural number.
spine :: Chain Natural
spine = Chain omega finiteOrdinal
