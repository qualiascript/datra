-- | Data transformations are presheaves on the category of Atlases.
--
-- Consequently 'DataTransformation' and 'DataTransformationHom' present the
-- presheaf category @[AtlasHom^op, Hask]@ directly. Its categorical structure
-- is inherited pointwise, and the standard presheaf-topos results apply to
-- this representation without additional Atlas-specific laws.
--
-- A presheaf is named by a type-level family symbol. Define its carriers with an
-- injective 'DataTransformationValue' instance; this is the defunctionalized
-- form LiquidHaskell can track through rank-N presheaf actions.
module DataTransformation
  ( DataTransformationValue
  , DataTransformation
  , dataTransformation
  , mapDataTransformation
  , dataTransformationIdentity
  , dataTransformationComposition
  , DataTransformationHom
  , dataTransformationHom
  , mapDataTransformationHom
  , dataTransformationHomNaturality
  , YonedaPresheaf
  , Yoneda (..)
  , yoneda
  , yonedaMap
  ) where

import DataTransformation.Internal
  ( DataTransformation
  , DataTransformationValue
  , DataTransformationHom
  , YonedaPresheaf
  , Yoneda (..)
  , dataTransformation
  , dataTransformationComposition
  , dataTransformationHom
  , dataTransformationHomNaturality
  , dataTransformationIdentity
  , mapDataTransformation
  , mapDataTransformationHom
  , yoneda
  , yonedaMap
  )
