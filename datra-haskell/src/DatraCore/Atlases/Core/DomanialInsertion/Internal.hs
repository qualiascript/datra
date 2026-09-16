{-# OPTIONS_GHC -Wno-orphans #-}

-- | Hidden domanial insertion implementation.
module DomanialInsertion.Internal
  ( DomanialInsertion (..)
  , domanialInsertion
  , identityInsertion
  , composeInsertions
  , pullbackDominion
  , CodomanialInsertion (..)
  , op
  , unop
  ) where

import Control.Category (Category (..))
import DomanialInsertion.LiquidInternal
  ( DomanialInsertion (..)
  , domanialInsertion
  )
import Dominion
  ( Dominion
  , dominion
  , dominionCoherence
  , rank
  , unrank
  )
import Prelude hiding ((.), id)

composePreimage
  :: (b -> Maybe a)
  -> (c -> Maybe b)
  -> c
  -> Maybe a
composePreimage firstPreimage secondPreimage value =
  firstPreimage =<< secondPreimage value

-- | Compose the executable maps and their left-inverse certificates.
composeInsertions
  :: DomanialInsertion b c
  -> DomanialInsertion a b
  -> DomanialInsertion a c
composeInsertions
  (DomanialInsertion second secondPreimage secondLeft)
  (DomanialInsertion first firstPreimage firstLeft) =
    DomanialInsertion
      (second . first)
      (composePreimage firstPreimage secondPreimage)
      (\value -> secondLeft (first value) `seq` firstLeft value)

-- | The proof-carrying identity insertion.
identityInsertion :: DomanialInsertion a a
identityInsertion =
  DomanialInsertion id Just (const ())

-- | Equip an insertion's source with the ranking induced from its target.
-- The target dominion and the insertion's partial inverse jointly provide the
-- source's total rank, executable unranking, and round-trip witness.
pullbackDominion
  :: Dominion b
  -> DomanialInsertion a b
  -> Dominion a
pullbackDominion targetDominion insertion =
  dominion
    (rank targetDominion . applyInsertion insertion)
    (\valueRank ->
      unrank targetDominion valueRank >>= preimage insertion)
    (\value ->
      dominionCoherence targetDominion (applyInsertion insertion value)
        `seq` insertionLeftInverse insertion value)

-- LiquidHaskell 0.9.4 cannot parse declarations for the symbolic Category
-- method `(.)`. The law-carrying representation and smart constructor are
-- checked in DomanialInsertion.LiquidInternal; these operations are
-- mechanically derived from them in this non-plugin implementation layer.
instance Category DomanialInsertion where
  id = identityInsertion
  (.) = composeInsertions

-- | The opposite category of domanial insertions.
--
-- A morphism from @a@ to @b@ here is a domanial insertion from @b@ to @a@.
newtype CodomanialInsertion a b = CodomanialInsertion
  { getOppositeInsertion :: DomanialInsertion b a
  }

-- | Reverse the categorical direction of a domanial insertion.
op :: DomanialInsertion a b -> CodomanialInsertion b a
op = CodomanialInsertion

-- | Recover the underlying domanial insertion.
unop :: CodomanialInsertion b a -> DomanialInsertion a b
unop = getOppositeInsertion

instance Category CodomanialInsertion where
  id = CodomanialInsertion id

  CodomanialInsertion second . CodomanialInsertion first =
    CodomanialInsertion (first . second)
