{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | Hidden representation of presheaves on ordered Atlas transposals.
module OrderedDataTransposal.Internal
  ( OrderedDataTransposalValue
  , OrderedDataTransposal
  , orderedDataTransposal
  , mapOrderedDataTransposal
  , orderedDataTransposalIdentity
  , orderedDataTransposalComposition
  , OrderedDataTransposalHom
  , orderedDataTransposalHom
  , mapOrderedDataTransposalHom
  , orderedDataTransposalHomNaturality
  ) where

import Control.Category (Category (..))
import Data.Kind (Type)
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import Prelude hiding ((.), id)

-- | Interpret a defunctionalized ordered Data-transposal carrier at an Atlas.
type family OrderedDataTransposalValue
  (values :: Type)
  (atlas :: Type) = (value :: Type) | value -> values atlas

type role OrderedDataTransposal nominal
data OrderedDataTransposal (values :: Type) = OrderedDataTransposal
  (forall source target.
    OrderedAtlasTransposal source target
    -> OrderedDataTransposalValue values target
    -> OrderedDataTransposalValue values source)
  (forall object. OrderedDataTransposalValue values object -> ())
  (forall source middle target.
    OrderedAtlasTransposal middle target
    -> OrderedAtlasTransposal source middle
    -> OrderedDataTransposalValue values target
    -> ())

-- | Construct a contravariant functor on ordered Atlas transposals.
orderedDataTransposal
  :: (forall source target.
       OrderedAtlasTransposal source target
       -> OrderedDataTransposalValue values target
       -> OrderedDataTransposalValue values source)
  -> (forall object. OrderedDataTransposalValue values object -> ())
  -> (forall source middle target.
       OrderedAtlasTransposal middle target
       -> OrderedAtlasTransposal source middle
       -> OrderedDataTransposalValue values target
       -> ())
  -> OrderedDataTransposal values
orderedDataTransposal = OrderedDataTransposal

mapOrderedDataTransposal
  :: OrderedDataTransposal values
  -> OrderedAtlasTransposal source target
  -> OrderedDataTransposalValue values target
  -> OrderedDataTransposalValue values source
mapOrderedDataTransposal (OrderedDataTransposal action _ _) = action

orderedDataTransposalIdentity
  :: OrderedDataTransposal values
  -> OrderedDataTransposalValue values object
  -> ()
orderedDataTransposalIdentity
  (OrderedDataTransposal _ identityLaw _) = identityLaw

orderedDataTransposalComposition
  :: OrderedDataTransposal values
  -> OrderedAtlasTransposal middle target
  -> OrderedAtlasTransposal source middle
  -> OrderedDataTransposalValue values target
  -> ()
orderedDataTransposalComposition
  (OrderedDataTransposal _ _ compositionLaw) = compositionLaw

type role OrderedDataTransposalHom nominal nominal
data OrderedDataTransposalHom (source :: Type) (target :: Type) where
  PrimitiveOrderedDataTransposalHom
    :: OrderedDataTransposal source
    -> OrderedDataTransposal target
    -> (forall atlas.
         OrderedDataTransposalValue source atlas
         -> OrderedDataTransposalValue target atlas)
    -> (forall sourceAtlas targetAtlas.
         OrderedAtlasTransposal sourceAtlas targetAtlas
         -> OrderedDataTransposalValue source targetAtlas
         -> ())
    -> OrderedDataTransposalHom source target
  IdentityOrderedDataTransposalHom
    :: OrderedDataTransposalHom values values
  CompositeOrderedDataTransposalHom
    :: OrderedDataTransposalHom middle target
    -> OrderedDataTransposalHom source middle
    -> OrderedDataTransposalHom source target

orderedDataTransposalHom
  :: OrderedDataTransposal source
  -> OrderedDataTransposal target
  -> (forall atlas.
       OrderedDataTransposalValue source atlas
       -> OrderedDataTransposalValue target atlas)
  -> (forall sourceAtlas targetAtlas.
       OrderedAtlasTransposal sourceAtlas targetAtlas
       -> OrderedDataTransposalValue source targetAtlas
       -> ())
  -> OrderedDataTransposalHom source target
orderedDataTransposalHom = PrimitiveOrderedDataTransposalHom

mapOrderedDataTransposalHom
  :: OrderedDataTransposalHom source target
  -> OrderedDataTransposalValue source atlas
  -> OrderedDataTransposalValue target atlas
mapOrderedDataTransposalHom
  (PrimitiveOrderedDataTransposalHom _ _ component _) = component
mapOrderedDataTransposalHom IdentityOrderedDataTransposalHom = id
mapOrderedDataTransposalHom
  (CompositeOrderedDataTransposalHom second first) =
    mapOrderedDataTransposalHom second
      . mapOrderedDataTransposalHom first

orderedDataTransposalHomNaturality
  :: OrderedDataTransposalHom source target
  -> OrderedAtlasTransposal sourceAtlas targetAtlas
  -> OrderedDataTransposalValue source targetAtlas
  -> ()
orderedDataTransposalHomNaturality
  (PrimitiveOrderedDataTransposalHom _ _ _ naturality) arrow value =
    naturality arrow value
orderedDataTransposalHomNaturality
  IdentityOrderedDataTransposalHom _ _ = ()
orderedDataTransposalHomNaturality
  (CompositeOrderedDataTransposalHom second first) arrow value =
    orderedDataTransposalHomNaturality first arrow value `seq`
      orderedDataTransposalHomNaturality
        second arrow (mapOrderedDataTransposalHom first value)

instance Category OrderedDataTransposalHom where
  id = IdentityOrderedDataTransposalHom
  IdentityOrderedDataTransposalHom . first = first
  second . IdentityOrderedDataTransposalHom = second
  second . first = CompositeOrderedDataTransposalHom second first
