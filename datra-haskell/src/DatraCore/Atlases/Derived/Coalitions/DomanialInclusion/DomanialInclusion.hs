-- | The Domanial Inclusion functor and its adjunction with Coalization.
--
-- A dominion is sent to the constant-data atlas on the singleton folio.
-- Stable transversals out of that atlas are naturally equivalent to
-- domanial insertions into the target coalition.
module DomanialInclusion
  ( DominionCellData
  , DominionAtlasObject
  , dominionCellDataValue
  , emptyDominion
  , singletonChain
  , onePageFolio
  , onePagePagination
  , dominionAtlas
  , dominionMap
  , domanialInclusionFunctorObject
  , domanialInclusionFunctorHom
  , domanialInclusionFunctorIdentity
  , domanialInclusionFunctorComposition
  , coaDomIncIso
  , coaDomIncIsoLeftInverse
  , coaDomIncIsoRightInverse
  , domIncToCoa
  , coaToDomInc
  , domIncCoaHomEquivTo
  , domIncCoaHomEquivFrom
  , domIncCoaHomEquivLeftInverse
  , domIncCoaHomEquivRightInverse
  , domIncCoaHomEquivNaturalityLeft
  , domIncCoaHomEquivNaturalityRight
  , dominionAdjunction
  , dominionLemma
  ) where

import DomanialInclusion.Internal
