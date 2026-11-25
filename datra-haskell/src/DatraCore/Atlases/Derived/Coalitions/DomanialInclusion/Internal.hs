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
  ( AtlasMappedObject
  , AtlasObjectCellData
  , AtlasObjectMap
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasOriginCell
  , atlasWitness
  , withAtlasWitness
  )
import AtlasCoveredPageElement
  ( withAtlasCoveredPageElement
  )
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
  ( coalitionElementCoverageAt
  )
import Data.Void (Void, absurd)
import DomanialInclusion.LiquidInternal
  ( coalitionComponentInsertion, dominionAtlasMap, dominionCoalitionElement )
import DomanialInclusion.Presentation
  ( DominionPaginationScope, onePageFolio, onePagePagination
  , DominionAtlas, DominionAtlasObject, dominionAtlas, withDominionAtlas
  , CanonicalDominion (..), CanonicalDominionAtlasScope, canonicalDominionAtlas )
import DomanialInclusion.Data
  ( DominionCellData
  , domIncHomLeftInverseValue
  , domIncHomNaturalityLeftValue
  , domIncHomNaturalityRightValue
  , domIncHomRightInverseValue
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
import StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  )

-- | A constant object-map whose codomain is the hidden target-origin cell.
data OriginObjectMap targetObject

type instance
  AtlasMappedObject (OriginObjectMap targetObject) sourceObject = targetObject

originObjectMap :: AtlasObjectMap (OriginObjectMap targetObject)
originObjectMap = atlasObjectMap

-- | The initial dominion from the Lean construction.
emptyDominion :: Dominion Void
emptyDominion = dominion absurd (const Nothing) absurd

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
