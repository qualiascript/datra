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
import DomanialInsertion.Core
  ( DomanialInsertion (..)
  , domanialInsertion
  , identityInsertion
  , composeInsertions
  , pullbackDominion
  )
import Prelude hiding ((.), id)

-- Category instances only delegate to the checked operations.
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
-- ALIGN: CODOMANIAL-OP.
op :: DomanialInsertion a b -> CodomanialInsertion b a
op = CodomanialInsertion

-- | Recover the underlying domanial insertion.
-- ALIGN: CODOMANIAL-UNOP.
unop :: CodomanialInsertion b a -> DomanialInsertion a b
unop = getOppositeInsertion

instance Category CodomanialInsertion where
  id = CodomanialInsertion id

  CodomanialInsertion second . CodomanialInsertion first =
    CodomanialInsertion (first . second)
