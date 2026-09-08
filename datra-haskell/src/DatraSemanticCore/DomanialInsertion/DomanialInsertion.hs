{-# OPTIONS_GHC -Wno-orphans #-}

module DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , preimage
  , insertionLeftInverse
  , domanialInsertion
  , identityInsertion
  , composeInsertions
  , CodomanialInsertion
  , op
  , unop
  ) where

import Control.Category (Category (..))
import DomanialInsertion.Internal
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

-- LiquidHaskell 0.9.4 cannot parse declarations for the symbolic Category
-- method `(.)`. The law-carrying type and general smart constructor are checked
-- in DomanialInsertion.Internal; this wrapper supplies the mechanically derived
-- identity and composition operations.
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
