{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--fast" @-}

-- | Checked assembly of representable natural transformations.
module DataTransformation.LiquidInternal
  ( module DataTransformation.Core, yonedaNatural, yonedaComponentAgrees ) where

import DataTransformation.Core
import Atlas.Presheaf (AtlasHom)

-- ALIGN: YONEDA-NATURAL-PACKAGE.
{-@ reflect yonedaNatural @-}
yonedaNatural :: AtlasHom source target
  -> DataTransformationNatural (YonedaPresheaf source) (YonedaPresheaf target)
yonedaNatural arrow =
  dataTransformationNatural yoneda yoneda (mapYonedaNatural arrow)
    (yonedaNaturalityForAction arrow)

-- ALIGN: YONEDA-PACKAGE-NATURALITY.
{-@ yonedaNaturalityForAction :: representedArrow:AtlasHom source target
      -> arrow:AtlasHom sourceAtlas targetAtlas -> value:Yoneda source targetAtlas
      -> {mapYonedaNatural representedArrow (mapDataTransformation yoneda arrow value)
           == mapDataTransformation yoneda arrow (mapYonedaNatural representedArrow value)} @-}
yonedaNaturalityForAction :: AtlasHom source target -> AtlasHom sourceAtlas targetAtlas
  -> Yoneda source targetAtlas -> ()
yonedaNaturalityForAction representedArrow arrow value =
  yonedaActionAgrees arrow value `seq`
  yonedaActionAgrees arrow (mapYonedaNatural representedArrow value) `seq`
  yonedaNaturality representedArrow arrow value

-- ALIGN: YONEDA-PACKAGE-COMPONENT.
{-@ yonedaComponentAgrees :: arrow:AtlasHom source target -> value:Yoneda source atlas
      -> {mapDataTransformationNatural (yonedaNatural arrow) value == mapYonedaNatural arrow value} @-}
yonedaComponentAgrees :: AtlasHom source target -> Yoneda source atlas -> ()
yonedaComponentAgrees _ _ = ()
