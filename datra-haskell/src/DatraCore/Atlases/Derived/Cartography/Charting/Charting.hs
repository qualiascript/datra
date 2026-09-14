-- | The Charting functor from Atlas transversals to Atlas transversal maps.
--
-- Its object action restricts every cell to data covered by a final region;
-- its arrow action is induced by preservation of coverage. The counit and
-- natural hom-set equivalence expose the right adjunction to the canonical
-- inclusion.
module Charting
  ( ChartedCellData
  , ChartedAtlasObject
  , chartedCellDataValue
  , chartAtlas
  , chartAtlasMap
  , chartCounit
  , chartMap
  , chartingFunctorObject
  , chartingFunctorHom
  , chartingFunctorIdentity
  , chartingFunctorComposition
  , chartLift
  , chartLower
  , chartHomEquivTo
  , chartHomEquivFrom
  , chartHomEquivLeftInverse
  , chartHomEquivRightInverse
  , chartHomEquivNaturalityLeft
  , chartHomEquivNaturalityRight
  , cartographyAdjunction
  , cartographyLemma
  ) where

import Charting.Internal
