{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of the symmetric monoidal base category and its
-- commutative monads.
module StableConfederalDataMonoidal.Internal
  ( StableConfederalDataEndofunctor
  , stableConfederalDataEndofunctor
  , mapStableConfederalDataObject
  , mapStableConfederalDataArrow
  , stableConfederalEndofunctorIdentity
  , stableConfederalEndofunctorComposition
  , CommutativeStableConfederalDataMonad
  , commutativeStableConfederalDataMonad
  , stableConfederalReturn
  , stableConfederalFmap
  , stableConfederalJoin
  , stableConfederalBind
  , stableConfederalFubini
  , stableConfederalMonadLeftIdentity
  , stableConfederalMonadRightIdentity
  , stableConfederalMonadAssociativity
  , stableConfederalMonadCommutativity
  ) where

import qualified Control.Category as Category
import Data.Kind (Type)
import HorizontalSum
  ( HorizontalSumValues
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  )

-- | An endofunctor on the category of stable confederal data.
-- @transform@ maps defunctionalized presheaf carriers to carriers.
type role StableConfederalDataEndofunctor nominal
data StableConfederalDataEndofunctor
  (transform :: Type -> Type) =
  StableConfederalDataEndofunctor
    (forall values.
      StableConfederalData values
      -> StableConfederalData (transform values))
    (forall source target.
      StableConfederalData source
      -> StableConfederalData target
      -> StableConfederalDataHom source target
      -> StableConfederalDataHom
           (transform source) (transform target))
    (forall values.
      StableConfederalData values
      -> ())
    (forall source middle target.
      StableConfederalData source
      -> StableConfederalData middle
      -> StableConfederalData target
      -> StableConfederalDataHom middle target
      -> StableConfederalDataHom source middle
      -> ())

-- | Construct an endofunctor from its object and arrow actions and the two
-- functor-law witnesses.
stableConfederalDataEndofunctor
  :: (forall values.
       StableConfederalData values
       -> StableConfederalData (transform values))
  -> (forall source target.
       StableConfederalData source
       -> StableConfederalData target
       -> StableConfederalDataHom source target
       -> StableConfederalDataHom
            (transform source) (transform target))
  -> (forall values.
       StableConfederalData values
       -> ())
  -> (forall source middle target.
       StableConfederalData source
       -> StableConfederalData middle
       -> StableConfederalData target
       -> StableConfederalDataHom middle target
       -> StableConfederalDataHom source middle
       -> ())
  -> StableConfederalDataEndofunctor transform
stableConfederalDataEndofunctor =
  StableConfederalDataEndofunctor

-- | Apply the endofunctor to an object.
mapStableConfederalDataObject
  :: StableConfederalDataEndofunctor transform
  -> StableConfederalData values
  -> StableConfederalData (transform values)
mapStableConfederalDataObject
  (StableConfederalDataEndofunctor objectMap _ _ _) = objectMap

-- | Categorical 'fmap' for natural transformations.
mapStableConfederalDataArrow
  :: StableConfederalDataEndofunctor transform
  -> StableConfederalData source
  -> StableConfederalData target
  -> StableConfederalDataHom source target
  -> StableConfederalDataHom
       (transform source) (transform target)
mapStableConfederalDataArrow
  (StableConfederalDataEndofunctor _ arrowMap _ _) = arrowMap

-- | Invoke the endofunctor identity-law witness.
stableConfederalEndofunctorIdentity
  :: StableConfederalDataEndofunctor transform
  -> StableConfederalData values
  -> ()
stableConfederalEndofunctorIdentity
  (StableConfederalDataEndofunctor _ _ law _) = law

-- | Invoke the endofunctor composition-law witness.
stableConfederalEndofunctorComposition
  :: StableConfederalDataEndofunctor transform
  -> StableConfederalData source
  -> StableConfederalData middle
  -> StableConfederalData target
  -> StableConfederalDataHom middle target
  -> StableConfederalDataHom source middle
  -> ()
stableConfederalEndofunctorComposition
  (StableConfederalDataEndofunctor _ _ _ law) = law

-- | A commutative monad on the symmetric monoidal category of stable
-- confederal data.
--
-- The Fubini arrow combines independent effects across horizontal sum.  Its
-- final witness states that the two orders induced by the symmetry agree.
type role CommutativeStableConfederalDataMonad nominal
data CommutativeStableConfederalDataMonad
  (transform :: Type -> Type) =
  CommutativeStableConfederalDataMonad
    (StableConfederalDataEndofunctor transform)
    (forall values.
      StableConfederalData values
      -> StableConfederalDataHom values (transform values))
    (forall values.
      StableConfederalData values
      -> StableConfederalDataHom
           (transform (transform values)) (transform values))
    (forall left right.
      StableConfederalData left
      -> StableConfederalData right
      -> StableConfederalDataHom
           (HorizontalSumValues (transform left) (transform right))
           (transform (HorizontalSumValues left right)))
    (forall values.
      StableConfederalData values
      -> ())
    (forall values.
      StableConfederalData values
      -> ())
    (forall values.
      StableConfederalData values
      -> ())
    (forall left right.
      StableConfederalData left
      -> StableConfederalData right
      -> ())

-- | Construct a commutative monad from an endofunctor, unit, multiplication,
-- Fubini map, the three monad laws, and the commutativity law.
commutativeStableConfederalDataMonad
  :: StableConfederalDataEndofunctor transform
  -> (forall values.
       StableConfederalData values
       -> StableConfederalDataHom values (transform values))
  -> (forall values.
       StableConfederalData values
       -> StableConfederalDataHom
            (transform (transform values)) (transform values))
  -> (forall left right.
       StableConfederalData left
       -> StableConfederalData right
       -> StableConfederalDataHom
            (HorizontalSumValues (transform left) (transform right))
            (transform (HorizontalSumValues left right)))
  -> (forall values.
       StableConfederalData values
       -> ())
  -> (forall values.
       StableConfederalData values
       -> ())
  -> (forall values.
       StableConfederalData values
       -> ())
  -> (forall left right.
       StableConfederalData left
       -> StableConfederalData right
       -> ())
  -> CommutativeStableConfederalDataMonad transform
commutativeStableConfederalDataMonad =
  CommutativeStableConfederalDataMonad

-- | Monad unit, analogous to Haskell's 'return'.
stableConfederalReturn
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> StableConfederalDataHom values (transform values)
stableConfederalReturn
  (CommutativeStableConfederalDataMonad _ unit _ _ _ _ _ _) =
    unit

-- | Monad endofunctor action, analogous to Haskell's 'fmap'.
stableConfederalFmap
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData source
  -> StableConfederalData target
  -> StableConfederalDataHom source target
  -> StableConfederalDataHom
       (transform source) (transform target)
stableConfederalFmap
  (CommutativeStableConfederalDataMonad functor _ _ _ _ _ _ _) =
    mapStableConfederalDataArrow functor

-- | Monad multiplication, analogous to Haskell's 'join'.
stableConfederalJoin
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> StableConfederalDataHom
       (transform (transform values)) (transform values)
stableConfederalJoin
  (CommutativeStableConfederalDataMonad _ _ multiplication _ _ _ _ _) =
    multiplication

-- | Haskell-style Kleisli bind in the stable-confederal presheaf category.
stableConfederalBind
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData middle
  -> StableConfederalData target
  -> StableConfederalDataHom source (transform middle)
  -> StableConfederalDataHom middle (transform target)
  -> StableConfederalDataHom source (transform target)
stableConfederalBind monad middle target computation continuation =
  stableConfederalJoin monad target
    Category.. stableConfederalFmap
      monad
      middle
      (mapMonadObject monad target)
      continuation
    Category.. computation

mapMonadObject
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> StableConfederalData (transform values)
mapMonadObject
  (CommutativeStableConfederalDataMonad functor _ _ _ _ _ _ _) =
    mapStableConfederalDataObject functor

-- | The symmetric Fubini map witnessing compatibility with horizontal sum.
stableConfederalFubini
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalDataHom
       (HorizontalSumValues (transform left) (transform right))
       (transform (HorizontalSumValues left right))
stableConfederalFubini
  (CommutativeStableConfederalDataMonad _ _ _ fubini _ _ _ _) =
    fubini

stableConfederalMonadLeftIdentity
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> ()
stableConfederalMonadLeftIdentity
  (CommutativeStableConfederalDataMonad _ _ _ _ law _ _ _) = law

stableConfederalMonadRightIdentity
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> ()
stableConfederalMonadRightIdentity
  (CommutativeStableConfederalDataMonad _ _ _ _ _ law _ _) = law

stableConfederalMonadAssociativity
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> ()
stableConfederalMonadAssociativity
  (CommutativeStableConfederalDataMonad _ _ _ _ _ _ law _) = law

stableConfederalMonadCommutativity
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData left
  -> StableConfederalData right
  -> ()
stableConfederalMonadCommutativity
  (CommutativeStableConfederalDataMonad _ _ _ _ _ _ _ law) = law
