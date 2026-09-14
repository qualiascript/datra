-- | The wide subcategory of Atlases whose page-element maps are injective.
--
-- This is the Haskell presentation of Lean's @AtlTrap@: objects are unchanged
-- from 'Atlas', while arrows are restricted by an executable left inverse for
-- their action on Atlas elements.
module AtlasTransposal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposalElement
  , withAtlasTransposalElement
  , atlasTransposalElementLT
  , atlasTransposal
  , atlasTransposalHom
  , mapAtlasTransposalObject
  , atlasTransposalPreimage
  , atlasTransposalLeftInverse
  , identityAtlasTransposal
  , composeAtlasTransposals
  , atlasTransposalPagination
  , mapAtlasTransposalElement
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  ) where

import AtlasTransposal.Internal
  ( AtlasTransposal
  , AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , atlasTransposalElementLT
  , atlasTransposalHom
  , atlasTransposalLeftInverse
  , atlasTransposalPagination
  , atlasTransposalPreimage
  , composeAtlasTransposals
  , identityAtlasTransposal
  , mapAtlasTransposalArrow
  , mapAtlasTransposalData
  , mapAtlasTransposalElement
  , mapAtlasTransposalObject
  , withAtlasTransposalElement
  )
