{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--reflection" @-}

module DomanialInsertion.Internal
  ( DomanialInsertion (..)
  , domanialInsertion
  ) where

-- | An injective function between dominions. The executable left-inverse proof
-- establishes injectivity, exactly as Lean's `Function.Embedding` requires.
{-@
data DomanialInsertion a b = DomanialInsertion
  { applyInsertion :: a -> b
  , preimage :: b -> Maybe a
  , insertionLeftInverse :: x:a ->
      { proof:() |
          preimage (applyInsertion x) == Just x }
  }
@-}
data DomanialInsertion a b = DomanialInsertion
  { applyInsertion :: a -> b
  , preimage :: b -> Maybe a
  , insertionLeftInverse :: a -> ()
  }

-- | Construct an insertion. LiquidHaskell verifies the left-inverse proof.
{-@
domanialInsertion
  :: forward:(a -> b)
  -> backward:(b -> Maybe a)
  -> (x:a -> { proof:() | backward (forward x) == Just x })
  -> DomanialInsertion a b
@-}
domanialInsertion
  :: (a -> b)
  -> (b -> Maybe a)
  -> (a -> ())
  -> DomanialInsertion a b
domanialInsertion = DomanialInsertion
