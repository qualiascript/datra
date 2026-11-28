{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- | Coalitions and the Coalizing functor.
module Coalition.Internal
  ( CoalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalition
  , stableCoalitionMap
  , coalizingFunctorObject
  , coalizingFunctorHom
  , coalizingIdentityMap
  , coalizingFunctorIdentity
  , coalizingFunctorComposition
  , coalizingFunctorCompositionPreimage
  ) where
import Atlas (Atlas, atlasPageElements)
import Atlas.Witness (AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData, atlasOwner)
import Coalition.Element (CoalitionElement, CoalitionData, coalitionElementValid, coalitionElementSource, coalitionElementCode,
  coalition, coalitionElementRank, withCoalitionElement)
import DomanialInsertion.Core (DomanialInsertion (..), composePartialInverses)
import Dominion (Dominion)
import PageElements (originPageElement)
import StableAtlasTransversal
  (StableAtlasTransversal, stableCoalitionInsertionData, scopedInsertionValue,
   scopedInsertionForwardObservation, scopedInsertionInverseObservation, coalitionMaybeCode, coalitionCodeExtensionality, coalitionIdentityCode,
   normalizedForwardCodes, normalizedInverseCodes,
   stableCoalitionSourceOwner, stableCoalitionTargetOwner, stableCoalitionOwnersEmpty,
   identityStableAtlasTransversal, composeStableAtlasTransversals)

{-@ predicate CoalitionCanonical O V = coalitionElementValid O V
      && coalitionElementSource V == originPageElement (atlasPageElements O) @-}


-- | Interpret a stable arrow on its actual canonical coalition domains.
-- ALIGN: COALITION-LEFT-INVERSE.
-- ALIGN: COALITION-STABLE-INTERPRETATION.
-- ALIGN: COALITION-OWNED-DOMAINS.
{-@ reflect stableCoalitionMap @-}
{-@ stableCoalitionMap
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target | StableCoalitionOwned sourceOwner targetOwner arrow}
      -> DomanialInsertion ({v:CoalitionElement source | CoalitionCanonical sourceOwner v})
           ({v:CoalitionElement target | CoalitionCanonical targetOwner v}) @-}
stableCoalitionMap
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target
  -> DomanialInsertion (CoalitionElement source) (CoalitionElement target)
stableCoalitionMap sourceOwner targetOwner arrow =
  scopedInsertionValue (stableCoalitionInsertionData sourceOwner targetOwner arrow)

-- | The object action retains the canonical coalition carrier.
{-@ coalizingFunctorObject :: owner:Atlas a s d o f
      -> Dominion ({v:CoalitionData a s d | CoalitionCanonical owner v}) @-}
coalizingFunctorObject :: Atlas a s d o f -> Dominion (CoalitionData a s d)
coalizingFunctorObject = coalition

-- | The arrow action retains both supplied owning domains.
{-@ coalizingFunctorHom
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target | StableCoalitionOwned sourceOwner targetOwner arrow}
      -> DomanialInsertion ({v:CoalitionElement source | CoalitionCanonical sourceOwner v})
           ({v:CoalitionElement target | CoalitionCanonical targetOwner v}) @-}
coalizingFunctorHom
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target
  -> DomanialInsertion (CoalitionElement source) (CoalitionElement target)
coalizingFunctorHom = stableCoalitionMap

-- | Specialize the public stable map to the identity at the supplied owner.
-- ALIGN: COALITION-IDENTITY-MAP.
{-@ reflect coalizingIdentityMap @-}
{-@ coalizingIdentityMap :: owner:Atlas (AtlasObjectAtlasScope object) (AtlasObjectPaginationScope object) (AtlasObjectCellData object) o f
      -> DomanialInsertion ({v:CoalitionElement object | CoalitionCanonical owner v})
           ({v:CoalitionElement object | CoalitionCanonical owner v}) @-}
coalizingIdentityMap :: forall object o f. Atlas (AtlasObjectAtlasScope object) (AtlasObjectPaginationScope object) (AtlasObjectCellData object) o f
  -> DomanialInsertion (CoalitionElement object) (CoalitionElement object)
coalizingIdentityMap owner = stableCoalitionMap owner owner
  (identityStableAtlasTransversal :: StableAtlasTransversal object object)

-- | Identity preserves the complete canonical record in both directions.
-- ALIGN: COALITION-IDENTITY.
{-@ coalizingFunctorIdentity :: owner:Atlas (AtlasObjectAtlasScope object) (AtlasObjectPaginationScope object) (AtlasObjectCellData object) o f
      -> element:{CoalitionElement object | CoalitionCanonical owner element}
      -> {applyInsertion (coalizingIdentityMap owner) element == element
           && preimage (coalizingIdentityMap owner) element == Just element} @-}
coalizingFunctorIdentity :: forall object o f. Atlas (AtlasObjectAtlasScope object) (AtlasObjectPaginationScope object) (AtlasObjectCellData object) o f -> CoalitionElement object -> ()
coalizingFunctorIdentity owner element =
  let arrow = identityStableAtlasTransversal :: StableAtlasTransversal object object
      insertion = coalizingIdentityMap @object owner
  in coalitionIdentityCode (coalitionElementCode element) `seq`
     coalizingMapForwardCode owner owner arrow element `seq`
     coalizingMapInverseCode owner owner arrow element `seq`
     coalitionCodeExtensionality owner (applyInsertion insertion element) element `seq`
     coalitionMaybeCodeExtensionality owner (preimage insertion element) (Just element)

-- | Pointwise composition law for the actual canonical forward maps.
-- ALIGN: COALITION-COMPOSITION.
{-@ coalizingFunctorComposition
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> middleOwner:Atlas (AtlasObjectAtlasScope middle) (AtlasObjectPaginationScope middle) (AtlasObjectCellData middle) mo mf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> first:{StableAtlasTransversal source middle | StableCoalitionOwned sourceOwner middleOwner first}
      -> second:{StableAtlasTransversal middle target | StableCoalitionOwned middleOwner targetOwner second}
      -> element:{CoalitionElement source | CoalitionCanonical sourceOwner element}
      -> {applyInsertion (stableCoalitionMap sourceOwner targetOwner (composeStableAtlasTransversals second first)) element
           == applyInsertion (stableCoalitionMap middleOwner targetOwner second)
                (applyInsertion (stableCoalitionMap sourceOwner middleOwner first) element)} @-}
coalizingFunctorComposition
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope middle) (AtlasObjectPaginationScope middle) (AtlasObjectCellData middle) mo mf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source middle
  -> StableAtlasTransversal middle target
  -> CoalitionElement source -> ()
coalizingFunctorComposition sourceOwner middleOwner targetOwner first second element =
  stableCoalitionOwnersEmpty first `seq`
  stableCoalitionOwnersEmpty second `seq`
  let firstMap = stableCoalitionMap sourceOwner middleOwner first
      secondMap = stableCoalitionMap middleOwner targetOwner second
      composed = composeStableAtlasTransversals second first
      directMap = stableCoalitionMap sourceOwner targetOwner composed
      middleElement = applyInsertion firstMap element
  in coalizingMapForwardCode sourceOwner middleOwner first element `seq`
     coalizingMapForwardCode middleOwner targetOwner second middleElement `seq`
     normalizedForwardCodes second first (coalitionElementCode element) `seq`
     coalizingMapForwardCode sourceOwner targetOwner composed element `seq`
     coalitionCodeExtensionality targetOwner
       (applyInsertion directMap element) (applyInsertion secondMap middleElement)

-- ALIGN: COALITION-FORWARD-CODE-OBSERVATION.
{-@ coalizingMapForwardCode
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target | StableCoalitionOwned sourceOwner targetOwner arrow}
      -> source:{CoalitionElement source | CoalitionCanonical sourceOwner source}
      -> {stableCoalitionForwardCodes arrow (coalitionElementCode source)
           == Just (coalitionElementCode (applyInsertion (stableCoalitionMap sourceOwner targetOwner arrow) source))} @-}
coalizingMapForwardCode
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target -> CoalitionElement source -> ()
coalizingMapForwardCode sourceOwner targetOwner arrow =
  scopedInsertionForwardObservation (stableCoalitionInsertionData sourceOwner targetOwner arrow)

-- ALIGN: COALITION-INVERSE-CODE-OBSERVATION.
{-@ coalizingMapInverseCode
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> arrow:{StableAtlasTransversal source target | StableCoalitionOwned sourceOwner targetOwner arrow}
      -> target:{CoalitionElement target | CoalitionCanonical targetOwner target}
      -> {stableCoalitionInverseCodes arrow (coalitionElementCode target)
           == coalitionMaybeCode (preimage (stableCoalitionMap sourceOwner targetOwner arrow) target)} @-}
coalizingMapInverseCode
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source target -> CoalitionElement target -> ()
coalizingMapInverseCode sourceOwner targetOwner arrow =
  scopedInsertionInverseObservation (stableCoalitionInsertionData sourceOwner targetOwner arrow)

{-@ coalitionMaybeCodeExtensionality :: owner:Atlas a s d o f
      -> left:Maybe ({value:CoalitionData a s d | CoalitionCanonical owner value})
      -> right:{Maybe ({value:CoalitionData a s d | CoalitionCanonical owner value}) |
           coalitionMaybeCode left == coalitionMaybeCode right}
      -> {left == right} @-}
coalitionMaybeCodeExtensionality :: Atlas a s d o f
  -> Maybe (CoalitionData a s d) -> Maybe (CoalitionData a s d) -> ()
coalitionMaybeCodeExtensionality _ Nothing Nothing = ()
coalitionMaybeCodeExtensionality _ Nothing (Just _) = ()
coalitionMaybeCodeExtensionality _ (Just _) Nothing = ()
coalitionMaybeCodeExtensionality owner (Just left) (Just right) =
  coalitionCodeExtensionality owner left right

-- | Composition preserves every supplied inverse result on canonical targets.
-- ALIGN: COALITION-COMPOSITION-PREIMAGE.
{-@ coalizingFunctorCompositionPreimage
      :: sourceOwner:Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
      -> middleOwner:Atlas (AtlasObjectAtlasScope middle) (AtlasObjectPaginationScope middle) (AtlasObjectCellData middle) mo mf
      -> targetOwner:Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
      -> first:{StableAtlasTransversal source middle | StableCoalitionOwned sourceOwner middleOwner first}
      -> second:{StableAtlasTransversal middle target | StableCoalitionOwned middleOwner targetOwner second}
      -> target:{CoalitionElement target | CoalitionCanonical targetOwner target}
      -> {preimage (stableCoalitionMap sourceOwner targetOwner (composeStableAtlasTransversals second first)) target
           == composePartialInverses (preimage (stableCoalitionMap sourceOwner middleOwner first))
                (preimage (stableCoalitionMap middleOwner targetOwner second)) target} @-}
coalizingFunctorCompositionPreimage
  :: Atlas (AtlasObjectAtlasScope source) (AtlasObjectPaginationScope source) (AtlasObjectCellData source) so sf
  -> Atlas (AtlasObjectAtlasScope middle) (AtlasObjectPaginationScope middle) (AtlasObjectCellData middle) mo mf
  -> Atlas (AtlasObjectAtlasScope target) (AtlasObjectPaginationScope target) (AtlasObjectCellData target) to tf
  -> StableAtlasTransversal source middle -> StableAtlasTransversal middle target -> CoalitionElement target -> ()
coalizingFunctorCompositionPreimage sourceOwner middleOwner targetOwner first second target =
  stableCoalitionOwnersEmpty first `seq`
  stableCoalitionOwnersEmpty second `seq`
  let firstMap = stableCoalitionMap sourceOwner middleOwner first
      secondMap = stableCoalitionMap middleOwner targetOwner second
      composed = composeStableAtlasTransversals second first
      directMap = stableCoalitionMap sourceOwner targetOwner composed
  in coalizingMapInverseCode middleOwner targetOwner second target `seq`
     normalizedInverseCodes second first (coalitionElementCode target) `seq`
     coalizingMapInverseCode sourceOwner targetOwner composed target `seq`
     case preimage secondMap target of
       Nothing ->
         coalitionMaybeCodeExtensionality sourceOwner (preimage directMap target) Nothing
       Just middle ->
         coalizingMapInverseCode sourceOwner middleOwner first middle `seq`
           coalitionMaybeCodeExtensionality sourceOwner
             (preimage directMap target) (preimage firstMap middle)
