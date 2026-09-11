{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Presheaves on the category of Atlases and their natural transformations.
module DataTransformation.Internal
  ( DataTransformation
  , DataTransformationValue
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

import Atlas (AtlasHom)
import Control.Category (Category (..))
import Data.Kind (Type)
import DataTransformation.LiquidInternal
  ( DataTransformation
  , DataTransformationNatural
  , DataTransformationValue
  , YonedaPresheaf
  , Yoneda (..)
  , dataTransformation
  , dataTransformationComposition
  , dataTransformationIdentity
  , dataTransformationNatural
  , dataTransformationNaturalNaturality
  , mapDataTransformation
  , mapDataTransformationNatural
  , yoneda
  , yonedaNatural
  )
import Prelude hiding ((.), id)

-- | A natural transformation between DaTra sets.
--
-- Primitive arrows retain their naturality witness. Identity and composition
-- are constructors of the presheaf category itself, so their naturality is
-- derived from their components rather than requested again from callers.
type role DataTransformationHom nominal nominal
data DataTransformationHom
  (source :: Type)
  (target :: Type) where
  PrimitiveDataTransformationHom
    :: DataTransformationNatural source target
    -> DataTransformationHom source target
  IdentityDataTransformationHom
    :: DataTransformationHom values values
  CompositeDataTransformationHom
    :: DataTransformationHom middle target
    -> DataTransformationHom source middle
    -> DataTransformationHom source target

-- | Construct a natural transformation.
--
-- Given the source and target presheaves, the callback should establish:
--
-- @
-- component (mapDataTransformation sourceP arrow value)
--   == mapDataTransformation targetP arrow (component value)
-- @
--
-- for every Atlas arrow and source value. 'dataTransformationNatural' checks
-- this callback in the LiquidHaskell layer before the primitive can enter the
-- categorical syntax.
dataTransformationHom
  :: DataTransformation source
  -> DataTransformation target
  -> (forall atlas.
       DataTransformationValue source atlas
       -> DataTransformationValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       AtlasHom sourceAtlas targetAtlas
       -> DataTransformationValue source targetAtlas
       -> ())
  -> DataTransformationHom source target
dataTransformationHom source target component naturality =
  PrimitiveDataTransformationHom
    (dataTransformationNatural source target component naturality)

-- | Evaluate one component of a natural transformation.
mapDataTransformationHom
  :: DataTransformationHom source target
  -> DataTransformationValue source atlas
  -> DataTransformationValue target atlas
mapDataTransformationHom
  (PrimitiveDataTransformationHom natural) =
    mapDataTransformationNatural natural
mapDataTransformationHom IdentityDataTransformationHom = id
mapDataTransformationHom
  (CompositeDataTransformationHom second first) =
    mapDataTransformationHom second . mapDataTransformationHom first

-- | Invoke or derive the naturality witness for a natural transformation.
dataTransformationHomNaturality
  :: DataTransformationHom source target
  -> AtlasHom sourceAtlas targetAtlas
  -> DataTransformationValue source targetAtlas
  -> ()
dataTransformationHomNaturality
  (PrimitiveDataTransformationHom natural) arrow value =
    dataTransformationNaturalNaturality natural arrow value
dataTransformationHomNaturality IdentityDataTransformationHom _ _ = ()
dataTransformationHomNaturality
  (CompositeDataTransformationHom second first) arrow value =
    dataTransformationHomNaturality first arrow value `seq`
      dataTransformationHomNaturality
        second arrow (mapDataTransformationHom first value)

-- | Natural transformations form the ordinary category of presheaves.
instance Category DataTransformationHom where
  id = IdentityDataTransformationHom

  IdentityDataTransformationHom . first = first
  second . IdentityDataTransformationHom = second
  second . first = CompositeDataTransformationHom second first

-- | Yoneda's action on an Atlas arrow, by postcomposition.
yonedaMap
  :: AtlasHom source target
  -> DataTransformationHom
       (YonedaPresheaf source)
       (YonedaPresheaf target)
yonedaMap = PrimitiveDataTransformationHom . yonedaNatural
