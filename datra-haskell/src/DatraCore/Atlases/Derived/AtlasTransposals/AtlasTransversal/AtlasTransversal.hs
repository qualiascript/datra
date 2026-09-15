-- | Atlas transversals: ordered transposals that preserve covered page elements.
--
-- This completes the two restrictions in Lean's @IsTransversal@: injectivity
-- and strict-order preservation come from 'OrderedAtlasTransposal', while this
-- module adds preservation of coverage by final regions.
module AtlasTransversal
  ( AtlasTransversal
  , atlasTransversal
  , atlasTransversalOrderedTransposal
  , atlasTransversalTransposal
  , atlasTransversalHom
  , atlasTransversalPreservesCoverage
  , mapAtlasTransversalCoveredPageElement
  , identityAtlasTransversal
  , composeAtlasTransversals
  , mapAtlasTransversalObject
  , atlasTransversalPreimage
  , atlasTransversalLeftInverse
  , atlasTransversalPreservesOrder
  , atlasTransversalPagination
  , mapAtlasTransversalElement
  , mapAtlasTransversalArrow
  , mapAtlasTransversalData
  ) where

import AtlasTransversal.Internal
  ( AtlasTransversal
  , atlasTransversal
  , atlasTransversalHom
  , atlasTransversalLeftInverse
  , atlasTransversalOrderedTransposal
  , atlasTransversalPagination
  , atlasTransversalPreimage
  , atlasTransversalPreservesOrder
  , atlasTransversalPreservesCoverage
  , atlasTransversalTransposal
  , composeAtlasTransversals
  , identityAtlasTransversal
  , mapAtlasTransversalArrow
  , mapAtlasTransversalCoveredPageElement
  , mapAtlasTransversalData
  , mapAtlasTransversalElement
  , mapAtlasTransversalObject
  )
