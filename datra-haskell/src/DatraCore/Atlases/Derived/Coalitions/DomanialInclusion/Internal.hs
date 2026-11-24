{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
-- | The one-page inclusion of dominions and its adjunction with coalization.
module DomanialInclusion.Internal
  ( DominionCellData
  , DominionAtlasObject
  , DominionAtlas
  , withDominionAtlas
  , CanonicalDominion (..)
  , CanonicalDominionAtlasScope
  , canonicalDominionAtlas
  , dominionCellDataValue
  , emptyDominion
  , singletonChain
  , onePageFolio
  , onePagePagination
  , dominionAtlas
  , dominionAtlasMap
  , dominionCoalitionElement
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

import Atlas
  ( Atlas
  , AtlasMappedObject
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectMap
  , AtlasObjectPaginationScope
  , AtlasWitness
  , withAtlasPresentation
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasOriginCell
  , atlasWitness
  , withAtlasWitness
  )
import Atlas.Construction (AtlasConstruction (..), FixedAtlasScope, constructAtlas)
import AtlasCoveredPageElement
  ( withAtlasCoveredPageElement
  , AtlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import AtlasTransposal
  ( atlasTransposal
  , atlasTransposalElement
  )
import AtlasTransversal (atlasTransversal)
import Chain.Singleton (singletonChain)
import Coalition
  ( CoalitionElement
  , stableCoalitionMap
  , withCoalitionElement
  )
import Coalition.Element
  ( coalitionElement
  , coalitionElementCoverageAt
  )
import Data.Void (Void, absurd)
import DomanialInclusion.LiquidInternal (coalitionComponentInsertion, onePageCoverage)
import DomanialInclusion.Presentation
  ( DominionPaginationScope, onePageFolio, onePagePagination, dominionPresentation )
import DomanialInclusion.Data
  ( DominionCellData
  , domIncHomLeftInverseValue
  , domIncHomNaturalityLeftValue
  , domIncHomNaturalityRightValue
  , domIncHomRightInverseValue
  , dominionCellData
  , dominionCellDataValue
  , dominionFunctorCompositionValue
  , dominionFunctorIdentityValue
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , composeInsertions
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion
  ( Dominion
  , dominion
  )
import OrderedAtlasTransposal (orderedAtlasTransposal)
import PageElements (PageElement, withPageElement)
import Data.Proxy (Proxy (..))
import StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  )

type DominionAtlasObject owner a =
  AtlasObject
    owner
    (DominionPaginationScope a)
    (DominionCellData a)

-- | A constant object-map whose codomain is the hidden target-origin cell.
data OriginObjectMap targetObject

type instance
  AtlasMappedObject (OriginObjectMap targetObject) sourceObject = targetObject

originObjectMap :: AtlasObjectMap (OriginObjectMap targetObject)
originObjectMap = atlasObjectMap

-- | The initial dominion from the Lean construction.
emptyDominion :: Dominion Void
emptyDominion = dominion absurd (const Nothing) absurd

-- | A runtime inclusion retains the exact Atlas used by all its operations.
type role DominionAtlas nominal nominal
data DominionAtlas owner a = DominionAtlas
  (Atlas owner (DominionPaginationScope a) (DominionCellData a) () ())

-- | A canonical Dominion is a fixed instance recipe, with no runtime input.
class CanonicalDominion a where
  canonicalDominion :: Proxy a -> Dominion a

data CanonicalDominionRecipe a
type CanonicalDominionAtlasScope a =
  FixedAtlasScope (CanonicalDominionRecipe a) (DominionPaginationScope a) (DominionCellData a) () ()

instance CanonicalDominion a => AtlasConstruction (CanonicalDominionRecipe a)
    (DominionPaginationScope a) (DominionCellData a) () () where
  atlasConstructionPresentation _ = dominionPresentation (canonicalDominion (Proxy :: Proxy a))

canonicalDominionAtlas :: forall a. CanonicalDominion a => DominionAtlas (CanonicalDominionAtlasScope a) a
canonicalDominionAtlas = DominionAtlas (constructAtlas (Proxy :: Proxy (CanonicalDominionRecipe a)))

-- ALIGN: DOMINC-ATLAS-INTERPRETATION.
-- ALIGN: DOMINC-STABLE-ISOMORPHISM.
withDominionAtlas :: Dominion a -> (forall owner. DominionAtlas owner a -> result) -> result
withDominionAtlas valueDominion useOwner =
  withAtlasPresentation (dominionPresentation valueDominion) (useOwner . DominionAtlas)

-- | Regard a dominion as the constant data assignment on a one-page atlas.
dominionAtlas :: DominionAtlas owner a
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
dominionAtlas (DominionAtlas valueAtlas) = valueAtlas

-- | Every datum of a one-page dominion atlas is covered by that same cell.
-- ALIGN: DOMINC-COVERAGE.
dominionCoverage
  :: Atlas
       owner
       (DominionPaginationScope a)
       (DominionCellData a)
       ()
       ()
  -> PageElement (DominionPaginationScope a) object
  -> DominionCellData a object
  -> AtlasCoverageWitness (DominionAtlasObject owner a)
dominionCoverage = onePageCoverage

-- | The one-page domanial inclusion is automatically an Atlas map: its
-- unique cell is simultaneously the extent and the final region.
dominionAtlasMap
  :: DominionAtlas owner a
  -> AtlasMap (DominionAtlasObject owner a)
dominionAtlasMap valueDominion =
  let valueAtlas = dominionAtlas valueDominion
  in atlasMap valueAtlas (dominionCoverage valueAtlas)

dominionCoalitionElement
  :: DominionAtlas owner a
  -> a
  -> CoalitionElement (DominionAtlasObject owner a)
dominionCoalitionElement valueDominion value =
  withPageElement
    (atlasOriginCell valueAtlas) $ \origin ->
      let datum = dominionCellData value
      in coalitionElement
          valueAtlas
          origin
          datum
          (dominionCoverage valueAtlas origin datum)
  where
    valueAtlas = dominionAtlas valueDominion

coalitionValue :: CoalitionElement (DominionAtlasObject owner a) -> a
coalitionValue element =
  withCoalitionElement element $ \_ datum ->
    dominionCellDataValue datum

-- | The canonical isomorphism @Coa (DomInc X) ≅ X@, represented by its two
-- proof-carrying domanial insertions.
-- ALIGN: DOMINC-COALITION-EQUIVALENCE.
coaDomIncIso
  :: DominionAtlas owner a
  -> ( DomanialInsertion (CoalitionElement (DominionAtlasObject owner a)) a
     , DomanialInsertion a (CoalitionElement (DominionAtlasObject owner a))
     )
coaDomIncIso valueDominion = (counit, unit)
  where
    counit =
      domanialInsertion
        coalitionValue
        (Just . dominionCoalitionElement valueDominion)
        (const ())

    unit =
      domanialInsertion
        (dominionCoalitionElement valueDominion)
        (Just . coalitionValue)
        (const ())

-- ALIGN: DOMINC-COALITION-LEFT-INVERSE.
coaDomIncIsoLeftInverse
  :: DominionAtlas owner a
  -> CoalitionElement (DominionAtlasObject owner a)
  -> ()
coaDomIncIsoLeftInverse valueDominion =
  insertionLeftInverse (fst (coaDomIncIso valueDominion))

-- ALIGN: DOMINC-COALITION-RIGHT-INVERSE.
coaDomIncIsoRightInverse :: DominionAtlas owner a -> a -> ()
coaDomIncIsoRightInverse valueDominion =
  insertionLeftInverse (snd (coaDomIncIso valueDominion))

-- | Forward half of the adjunction hom equivalence.
-- ALIGN: DOMINC-HOM-TO.
-- ALIGN: DOMINC-HOM-TO-INTERPRETATION.
domIncToCoa
  :: DominionAtlas owner a
  -> AtlasWitness target
  -> StableAtlasTransversal (DominionAtlasObject owner a) target
  -> DomanialInsertion a (CoalitionElement target)
domIncToCoa sourceDominion targetWitness arrow =
  composeInsertions
    (stableCoalitionMap sourceWitness targetWitness arrow)
    (snd (coaDomIncIso sourceDominion))
  where
    sourceWitness = atlasWitness (dominionAtlas sourceDominion)

-- | Inverse half of the adjunction.  The target origin is captured as a
-- type-level object-map witness. The explicit component inverse must recover
-- each source value from its coalition image transported to the target origin.
-- It can reject uncovered target data without searching for a coverage witness.
-- ALIGN: DOMINC-HOM-FROM.
coaToDomInc
  :: forall owner a target.
     DominionAtlas owner a
  -> AtlasWitness target
  -> DomanialInsertion a (CoalitionElement target)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> AtlasObjectCellData target object -> Maybe a)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> a -> ())
  -> StableAtlasTransversal (DominionAtlasObject owner a) target
coaToDomInc sourceDominion targetOwner insertion backward leftInverse =
  withAtlasWitness targetOwner $ \targetAtlas ->
  withPageElement (atlasOriginCell targetAtlas) $
    \(targetOrigin :: PageElement targetScope targetObject) ->
    let sourceAtlas = dominionAtlas sourceDominion
        sourceWitness = atlasWitness sourceAtlas
        targetWitness = atlasWitness targetAtlas

        component
          :: forall sourceObject.
             PageElement (DominionPaginationScope a) sourceObject
          -> DomanialInsertion
               (DominionCellData a sourceObject)
               (AtlasObjectCellData target targetObject)
        component _ =
          coalitionComponentInsertion targetAtlas targetOrigin (applyInsertion insertion)
            (backward targetOrigin) (leftInverse targetOrigin)

        action =
          atlasMorphismAction
            (originObjectMap @targetObject)
            sourceAtlas
            targetAtlas
            (const targetOrigin)
            component
            (\_ _ -> ())
            (\_ _ -> ())

        hom = atlasHom (atlasMorphism action)

        sourceOriginElement =
          withPageElement (atlasOriginCell sourceAtlas) $ \sourceOrigin ->
            atlasTransposalElement sourceWitness sourceOrigin

        targetOriginElement =
          atlasTransposalElement targetWitness targetOrigin

        objectPreimage targetElement
          | targetElement == targetOriginElement = Just sourceOriginElement
          | otherwise = Nothing

        transposal =
          atlasTransposal
            sourceWitness
            hom
            objectPreimage
            (const ())

        ordered = orderedAtlasTransposal transposal (\_ _ -> ())

        transversal =
          atlasTransversal
            sourceAtlas
            targetAtlas
            ordered
            (\covered ->
              withAtlasCoveredPageElement covered $ \_ sourceDatum ->
                  coalitionElementCoverageAt
                    targetAtlas
                    targetOrigin
                    (applyInsertion insertion
                      (dominionCellDataValue sourceDatum)))
    in stableAtlasTransversal
        sourceAtlas targetAtlas transversal ()
        (fmap (dominionCoalitionElement sourceDominion) . preimage insertion)
        (\element ->
          insertionLeftInverse insertion (coalitionValue element) `seq`
            coaDomIncIsoLeftInverse sourceDominion element)

-- | Arrow action of the Domanial Inclusion functor.
-- ALIGN: DOMINC-MAP.
-- ALIGN: DOMINC-MAP-IDENTITY.
-- ALIGN: DOMINC-MAP-COMPOSITION.
dominionMap
  :: DominionAtlas owner a
  -> DominionAtlas targetOwner b
  -> DomanialInsertion a b
  -> StableAtlasTransversal
       (DominionAtlasObject owner a)
       (DominionAtlasObject targetOwner b)
dominionMap sourceDominion targetDominion insertion =
  coaToDomInc
    sourceDominion
    targetWitness
    (composeInsertions
      (snd (coaDomIncIso targetDominion))
      insertion)
    (\_ -> preimage insertion . dominionCellDataValue)
    (\_ -> insertionLeftInverse insertion)
  where
    targetWitness = atlasWitness (dominionAtlas targetDominion)

domanialInclusionFunctorObject
  :: DominionAtlas owner a
  -> AtlasWitness (DominionAtlasObject owner a)
domanialInclusionFunctorObject = atlasWitness . dominionAtlas

domanialInclusionFunctorHom
  :: DominionAtlas owner a
  -> DominionAtlas targetOwner b
  -> DomanialInsertion a b
  -> StableAtlasTransversal
       (DominionAtlasObject owner a)
       (DominionAtlasObject targetOwner b)
domanialInclusionFunctorHom = dominionMap

domanialInclusionFunctorIdentity
  :: DominionCellData a object
  -> ()
domanialInclusionFunctorIdentity = dominionFunctorIdentityValue

domanialInclusionFunctorComposition
  :: (a -> b)
  -> (b -> c)
  -> DominionCellData a object
  -> ()
domanialInclusionFunctorComposition = dominionFunctorCompositionValue

-- ALIGN: DOMINC-HOM-EQUIV-TO.
domIncCoaHomEquivTo
  :: DominionAtlas owner a
  -> AtlasWitness target
  -> StableAtlasTransversal (DominionAtlasObject owner a) target
  -> DomanialInsertion a (CoalitionElement target)
domIncCoaHomEquivTo = domIncToCoa

-- ALIGN: DOMINC-HOM-EQUIV-FROM.
domIncCoaHomEquivFrom
  :: DominionAtlas owner a
  -> AtlasWitness target
  -> DomanialInsertion a (CoalitionElement target)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> AtlasObjectCellData target object -> Maybe a)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> a -> ())
  -> StableAtlasTransversal (DominionAtlasObject owner a) target
domIncCoaHomEquivFrom = coaToDomInc

-- The following four LiquidHaskell-checked equations are the pointwise
-- extensionality proofs used by Lean for the inverse and naturality laws.
-- ALIGN: DOMINC-HOM-LEFT-INVERSE-FULL.
domIncCoaHomEquivLeftInverse
  :: (DominionCellData a object -> b)
  -> DominionCellData a object
  -> ()
domIncCoaHomEquivLeftInverse = domIncHomLeftInverseValue

-- ALIGN: DOMINC-HOM-RIGHT-INVERSE-FULL.
domIncCoaHomEquivRightInverse :: (a -> b) -> a -> ()
domIncCoaHomEquivRightInverse = domIncHomRightInverseValue

-- ALIGN: DOMINC-HOM-NATURALITY-LEFT-FULL.
domIncCoaHomEquivNaturalityLeft
  :: (a' -> a)
  -> (DominionCellData a object -> b)
  -> a'
  -> ()
domIncCoaHomEquivNaturalityLeft = domIncHomNaturalityLeftValue

-- ALIGN: DOMINC-HOM-NATURALITY-RIGHT-FULL.
domIncCoaHomEquivNaturalityRight
  :: (DominionCellData a object -> b)
  -> (b -> c)
  -> a
  -> ()
domIncCoaHomEquivNaturalityRight = domIncHomNaturalityRightValue

-- | The adjunction proof, following the no-record presentation established by
-- Charter: a tuple of the two inverse and two naturality witnesses.
dominionAdjunction =
  ( domIncCoaHomEquivLeftInverse
  , domIncCoaHomEquivRightInverse
  , domIncCoaHomEquivNaturalityLeft
  , domIncCoaHomEquivNaturalityRight
  )

dominionLemma = dominionAdjunction
