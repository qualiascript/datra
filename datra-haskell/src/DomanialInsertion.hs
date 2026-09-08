module DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , preimage
  , unsafeDomanialInsertion
  , finiteSetInsertion
  , CodomanialInsertion
  , op
  , unop
  ) where

import Control.Category (Category (..))
import Control.Monad ((>=>))
import Data.Set (Set)
import Prelude hiding ((.), id)

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | An injective function between dominions.
--
-- Vanilla Haskell cannot enforce the defining partial-inverse laws:
--
--   preimage insertion (applyInsertion insertion x) == Just x
--
--   preimage insertion y == Just x
--     implies applyInsertion insertion x == y
--
-- These laws imply that 'applyInsertion' is injective.
--
-- The constructor is kept private so that every unchecked construction is
-- visible at a call to 'unsafeDomanialInsertion'.
data DomanialInsertion a b = DomanialInsertion
  { applyInsertion :: a -> b
  , preimage :: b -> Maybe a
  }

-- | Assert that two functions satisfy the partial-inverse laws and regard
-- them as a domanial insertion.
--
-- The caller must ensure that the functions satisfy the laws
-- documented on 'DomanialInsertion'.
unsafeDomanialInsertion
  :: (a -> b)
  -> (b -> Maybe a)
  -> DomanialInsertion a b
unsafeDomanialInsertion = DomanialInsertion

-- | Construct an insertion between two finite sets.
--
-- Returns 'Nothing' when the function maps a source element outside the
-- target set or maps two different source elements to the same target.
-- The partial-inverse laws hold for elements of the supplied source and
-- target sets.
finiteSetInsertion
  :: Ord b
  => Set a
  -> Set b
  -> (a -> b)
  -> Maybe (DomanialInsertion a b)
finiteSetInsertion source target forward
  | landsInTarget && isInjective =
      Just (DomanialInsertion forward (`Map.lookup` inverse))
  | otherwise = Nothing
  where
    imageWithSources =
      [ (forward sourceValue, sourceValue)
      | sourceValue <- Set.toAscList source
      ]

    inverse = Map.fromList imageWithSources

    landsInTarget = all (`Set.member` target) (Map.keys inverse)

    isInjective = Map.size inverse == Set.size source

instance Category DomanialInsertion where
  id = DomanialInsertion id Just

  DomanialInsertion second secondPreimage
    . DomanialInsertion first firstPreimage =
      DomanialInsertion
        (second . first)
        (secondPreimage >=> firstPreimage)

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
