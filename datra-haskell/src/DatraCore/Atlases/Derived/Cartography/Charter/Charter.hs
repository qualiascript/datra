-- | The Charter functor from Atlas transversals to Atlas transversal maps.
--
-- Its object action restricts every cell to data covered by a final region;
-- its arrow action is induced by preservation of coverage. The counit and
-- natural hom-set equivalence expose the right adjunction to the canonical
-- inclusion.
module Charter
  ( ChartedCellData
  , ChartedAtlasObject
  , chartedCellDataValue
  , chartAtlas
  , chartAtlasMap
  , chartCounit
  , chartMap
  , charterFunctorObject
  , charterFunctorHom
  , charterFunctorIdentity
  , charterFunctorComposition
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

import Charter.Internal
