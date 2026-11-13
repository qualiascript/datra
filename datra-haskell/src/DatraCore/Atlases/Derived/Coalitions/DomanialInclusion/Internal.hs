{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
-- | The one-page inclusion of dominions and its adjunction with coalization.
module DomanialInclusion.Internal
  ( DominionCellData
  , DominionAtlasObject
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

import qualified Pagination
import Atlas
  ( Atlas
  , AtlasMappedObject
  , AtlasObject
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
  )
import Atlas.Internal
  ( atlasDataAction
  , atlasWithScope
  )
import Atlas.Morphism.Internal (AtlasWitness (..))
import AtlasCoveredPageElement.Internal
  ( AtlasCoveredPageElement (..)
  , AtlasCoverageWitness
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import AtlasTransposal
  ( atlasTransposal
  , atlasTransposalElement
  )
import AtlasTransversal (atlasTransversal)
import Chain (Chain, chain)
import Coalition
  ( CoalitionElement
  , stableCoalitionMap
  , withCoalitionElement
  )
import Coalition.Internal
  ( coalitionElement
  , coalitionElementCoverageAt
  )
import DatraOrdinal (finiteOrdinal)
import Data.Void (Void, absurd)
import DomanialInclusion.LiquidInternal
  ( DominionCellData
  , coalitionComponentInsertion
  , domIncHomLeftInverseValue
  , domIncHomNaturalityLeftValue
  , domIncHomNaturalityRightValue
  , domIncHomRightInverseValue
  , dominionCellData
  , dominionCellDataValue
  , dominionFunctorCompositionValue
  , dominionFunctorIdentityValue
  , mapDominionCellData
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
  , dominionCoherence
  , rank
  , unrank
  )
import Folio (Folio, singletonFolio)
import OrderedAtlasTransposal (orderedAtlasTransposal)
import PageElements (PageElement, withPageElement)
import Pagination (Pagination)
import Pagination.Internal (paginationWithScope)
import StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  )

-- Deterministic tokens make the functor's object action stable across calls.
data DominionAtlasScope a
data DominionPaginationScope a

type DominionAtlasObject a =
  AtlasObject
    (DominionAtlasScope a)
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

-- | The singleton chain used by the one-page folio.
singletonChain :: Chain ()
singletonChain =
  chain
    (finiteOrdinal 1)
    (const (finiteOrdinal 0))
    (\position ->
      if position == finiteOrdinal 0 then Just () else Nothing)
    (const ())
    (\_ _ -> ())
    (const ())

onePageFolio :: Folio () ()
onePageFolio = singletonFolio singletonChain

-- | The deterministically scoped one-page pagination used by @DomInc@.
onePagePagination
  :: forall a. Pagination (DominionPaginationScope a) () ()
onePagePagination = paginationWithScope onePageFolio

-- ALIGN: DOMINC-CONSTANT-DOMINION.
constantDominion :: Dominion a -> Dominion (DominionCellData a object)
constantDominion valueDominion =
  dominion
    (rank valueDominion . dominionCellDataValue)
    (fmap dominionCellData . unrank valueDominion)
    (dominionCoherence valueDominion . dominionCellDataValue)

-- | Regard a dominion as the constant data assignment on a one-page atlas.
-- ALIGN: DOMINC-ATLAS-INTERPRETATION.
-- ALIGN: DOMINC-STABLE-ISOMORPHISM.
dominionAtlas
  :: forall a.
     Dominion a
  -> Atlas
       (DominionAtlasScope a)
       (DominionPaginationScope a)
       (DominionCellData a)
       ()
       ()
dominionAtlas valueDominion =
  atlasWithScope
    (onePagePagination @a)
    (atlasDataAction (Pagination.paginationPageElements (onePagePagination @a))
      (const (constantDominion valueDominion))
      (const identityDominionCellInsertion))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())

identityDominionCellInsertion
  :: DomanialInsertion
       (DominionCellData a sourceObject)
       (DominionCellData a targetObject)
identityDominionCellInsertion =
  domanialInsertion
    (mapDominionCellData id)
    (Just . mapDominionCellData id)
    (const ())

-- | Every datum of a one-page dominion atlas is covered by that same cell.
-- ALIGN: DOMINC-COVERAGE.
dominionCoverage
  :: Atlas
       (DominionAtlasScope a)
       (DominionPaginationScope a)
       (DominionCellData a)
       ()
       ()
  -> PageElement (DominionPaginationScope a) object
  -> DominionCellData a object
  -> AtlasCoverageWitness (DominionAtlasObject a)
dominionCoverage valueAtlas occurrence datum =
  atlasCoverageWitness
    valueAtlas occurrence datum occurrence datum ()

-- | The one-page domanial inclusion is automatically an Atlas map: its
-- unique cell is simultaneously the extent and the final region.
dominionAtlasMap
  :: Dominion a
  -> AtlasMap (DominionAtlasObject a)
dominionAtlasMap valueDominion =
  let valueAtlas = dominionAtlas valueDominion
  in atlasMap valueAtlas (dominionCoverage valueAtlas)

dominionCoalitionElement
  :: Dominion a
  -> a
  -> CoalitionElement (DominionAtlasObject a)
dominionCoalitionElement valueDominion value =
  withPageElement
    (atlasOriginCell valueAtlas) $ \origin ->
      let datum = dominionCellData value
      in coalitionElement
          origin
          datum
          (dominionCoverage valueAtlas origin datum)
  where
    valueAtlas = dominionAtlas valueDominion

coalitionValue :: CoalitionElement (DominionAtlasObject a) -> a
coalitionValue element =
  withCoalitionElement element $ \_ datum ->
    dominionCellDataValue datum

-- | The canonical isomorphism @Coa (DomInc X) ≅ X@, represented by its two
-- proof-carrying domanial insertions.
-- ALIGN: DOMINC-COALITION-EQUIVALENCE.
coaDomIncIso
  :: Dominion a
  -> ( DomanialInsertion (CoalitionElement (DominionAtlasObject a)) a
     , DomanialInsertion a (CoalitionElement (DominionAtlasObject a))
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
  :: Dominion a
  -> CoalitionElement (DominionAtlasObject a)
  -> ()
coaDomIncIsoLeftInverse valueDominion =
  insertionLeftInverse (fst (coaDomIncIso valueDominion))

-- ALIGN: DOMINC-COALITION-RIGHT-INVERSE.
coaDomIncIsoRightInverse :: Dominion a -> a -> ()
coaDomIncIsoRightInverse valueDominion =
  insertionLeftInverse (snd (coaDomIncIso valueDominion))

-- | Forward half of the adjunction hom equivalence.
-- ALIGN: DOMINC-HOM-TO.
-- ALIGN: DOMINC-HOM-TO-INTERPRETATION.
domIncToCoa
  :: Dominion a
  -> AtlasWitness target
  -> StableAtlasTransversal (DominionAtlasObject a) target
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
  :: forall a target.
     Dominion a
  -> AtlasWitness target
  -> DomanialInsertion a (CoalitionElement target)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> AtlasObjectCellData target object -> Maybe a)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> a -> ())
  -> StableAtlasTransversal (DominionAtlasObject a) target
coaToDomInc sourceDominion (AtlasWitness targetAtlas) insertion backward leftInverse =
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
              case covered of
                AtlasCoveredPageElement _ sourceDatum _ ->
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
  :: Dominion a
  -> Dominion b
  -> DomanialInsertion a b
  -> StableAtlasTransversal
       (DominionAtlasObject a)
       (DominionAtlasObject b)
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
  :: Dominion a
  -> AtlasWitness (DominionAtlasObject a)
domanialInclusionFunctorObject = atlasWitness . dominionAtlas

domanialInclusionFunctorHom
  :: Dominion a
  -> Dominion b
  -> DomanialInsertion a b
  -> StableAtlasTransversal
       (DominionAtlasObject a)
       (DominionAtlasObject b)
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
  :: Dominion a
  -> AtlasWitness target
  -> StableAtlasTransversal (DominionAtlasObject a) target
  -> DomanialInsertion a (CoalitionElement target)
domIncCoaHomEquivTo = domIncToCoa

-- ALIGN: DOMINC-HOM-EQUIV-FROM.
domIncCoaHomEquivFrom
  :: Dominion a
  -> AtlasWitness target
  -> DomanialInsertion a (CoalitionElement target)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> AtlasObjectCellData target object -> Maybe a)
  -> (forall object. PageElement (AtlasObjectPaginationScope target) object
        -> a -> ())
  -> StableAtlasTransversal (DominionAtlasObject a) target
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
