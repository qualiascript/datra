-- | Public domanial insertion API backed by the hidden implementation.
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

import DomanialInsertion.Internal
  ( CodomanialInsertion
  , DomanialInsertion
  , applyInsertion
  , composeInsertions
  , domanialInsertion
  , identityInsertion
  , insertionLeftInverse
  , op
  , preimage
  , unop
  )
