-- | Coalitions and the Coalizing functor.
module Coalition.Internal
  ( CoalitionElement
  , coalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalitionElementAt
  , coalitionElementCoverageAt
  , coalition
  , stableCoalitionMap
  , coalizingFunctorObject
  , coalizingFunctorHom
  , coalizingFunctorIdentity
  , coalizingFunctorComposition
  ) where

import Atlas (Atlas, AtlasObject, AtlasWitness)
import Coalition.Element.Internal
  ( CoalitionElement, coalitionElement, coalitionElementRank, withCoalitionElement
  , coalitionElementAt, coalitionElementCoverageAt, coalition )
import DomanialInsertion (DomanialInsertion, applyInsertion, insertionLeftInverse)
import Dominion (Dominion)
import StableAtlasTransversal
  ( StableAtlasTransversal, composeStableAtlasTransversals, identityStableAtlasTransversal )
import StableAtlasTransversal.Internal (stableAtlasTransversalCoalitionInsertion)

-- | The object action of the Coalizing functor.
coalizingFunctorObject
  :: Atlas atlasScope scope cellData origin final
  -> Dominion
       (CoalitionElement (AtlasObject atlasScope scope cellData))
coalizingFunctorObject = coalition

-- | The checked coalition insertion retained by the stable arrow. Identity
-- and composition derive both directions from their constituent certificates.
-- ALIGN: COALITION-LEFT-INVERSE.
-- ALIGN: COALITION-STABLE-INTERPRETATION.
stableCoalitionMap
  :: AtlasWitness source
  -> AtlasWitness target
  -> StableAtlasTransversal source target
  -> DomanialInsertion (CoalitionElement source) (CoalitionElement target)
stableCoalitionMap _ _ = stableAtlasTransversalCoalitionInsertion

-- | The arrow action of the Coalizing functor.
coalizingFunctorHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> StableAtlasTransversal source target
  -> DomanialInsertion
       (CoalitionElement source)
       (CoalitionElement target)
coalizingFunctorHom = stableCoalitionMap

-- | Pointwise identity law for the Coalizing functor.
-- ALIGN: COALITION-IDENTITY.
coalizingFunctorIdentity
  :: AtlasWitness object
  -> CoalitionElement object
  -> ()
coalizingFunctorIdentity witness = insertionLeftInverse
      (stableCoalitionMap
        witness witness identityStableAtlasTransversal)

-- | Pointwise composition law for the Coalizing functor.
-- ALIGN: COALITION-COMPOSITION.
coalizingFunctorComposition
  :: AtlasWitness source
  -> AtlasWitness middle
  -> AtlasWitness target
  -> StableAtlasTransversal source middle
  -> StableAtlasTransversal middle target
  -> CoalitionElement source
  -> ()
coalizingFunctorComposition
  sourceWitness middleWitness targetWitness first second element =
    insertionLeftInverse firstMap element `seq`
      insertionLeftInverse secondMap
        (applyInsertion firstMap element) `seq`
          insertionLeftInverse directMap element
  where
    firstMap =
      stableCoalitionMap sourceWitness middleWitness first

    secondMap =
      stableCoalitionMap middleWitness targetWitness second

    directMap =
      stableCoalitionMap
        sourceWitness
        targetWitness
        (composeStableAtlasTransversals second first)
