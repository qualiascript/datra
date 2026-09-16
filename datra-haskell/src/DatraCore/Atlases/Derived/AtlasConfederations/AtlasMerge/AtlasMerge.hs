-- | The object-level merge of two Atlases.
--
-- A merge introduces a fresh singleton extent containing the disjoint union
-- of the input extents.  Its following pages combine the corresponding pages
-- of both input Atlases on their full padded spines.
module AtlasMerge
  ( AtlasMergeDatum
  , AtlasMergeSide (..)
  , AtlasMergePageCell
  , atlasMergeDatumSide
  , atlasMergeDatumRank
  , atlasMergeLength
  , atlasMergeFolio
  , atlasMerge
  , atlasMergeLeftOrderedTransposal
  , atlasMergeRightOrderedTransposal
  ) where

import AtlasMerge.Internal
  ( AtlasMergeDatum
  , AtlasMergePageCell
  , AtlasMergeSide (..)
  , atlasMerge
  , atlasMergeLeftOrderedTransposal
  , atlasMergeRightOrderedTransposal
  , atlasMergeDatumRank
  , atlasMergeDatumSide
  , atlasMergeFolio
  , atlasMergeLength
  )
