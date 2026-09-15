{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of the symmetric monoidal base category and its
-- commutative monads.
module StableConfederalDataTransversalMonoidal.Internal
  ( StableConfederalDataTransversalEndofunctor
  , stableConfederalDataTransversalEndofunctor
  , mapStableConfederalDataTransversalObject
  , mapStableConfederalDataTransversalArrow
  , stableConfederalEndofunctorIdentity
  , stableConfederalEndofunctorComposition
  , CommutativeStableConfederalDataTransversalMonad
  , commutativeStableConfederalDataTransversalMonad
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
import StableConfederalDataTransversal
  ( StableConfederalDataTransversal
  , StableConfederalDataTransversalHom
  )

-- | An endofunctor on the category of stable confederal data transversals.
-- @transform@ maps defunctionalized presheaf carriers to carriers.
type role StableConfederalDataTransversalEndofunctor nominal
data StableConfederalDataTransversalEndofunctor
  (transform :: Type -> Type) =
  StableConfederalDataTransversalEndofunctor
    (forall values.
      StableConfederalDataTransversal values
      -> StableConfederalDataTransversal (transform values))
    (forall source target.
      StableConfederalDataTransversal source
      -> StableConfederalDataTransversal target
      -> StableConfederalDataTransversalHom source target
      -> StableConfederalDataTransversalHom
           (transform source) (transform target))
    (forall values.
      StableConfederalDataTransversal values
      -> ())
    (forall source middle target.
      StableConfederalDataTransversal source
      -> StableConfederalDataTransversal middle
      -> StableConfederalDataTransversal target
      -> StableConfederalDataTransversalHom middle target
      -> StableConfederalDataTransversalHom source middle
      -> ())

-- | Construct an endofunctor from its object and arrow actions and the two
-- functor-law witnesses.
stableConfederalDataTransversalEndofunctor
  :: (forall values.
       StableConfederalDataTransversal values
       -> StableConfederalDataTransversal (transform values))
  -> (forall source target.
       StableConfederalDataTransversal source
       -> StableConfederalDataTransversal target
       -> StableConfederalDataTransversalHom source target
       -> StableConfederalDataTransversalHom
            (transform source) (transform target))
  -> (forall values.
       StableConfederalDataTransversal values
       -> ())
  -> (forall source middle target.
       StableConfederalDataTransversal source
       -> StableConfederalDataTransversal middle
       -> StableConfederalDataTransversal target
       -> StableConfederalDataTransversalHom middle target
       -> StableConfederalDataTransversalHom source middle
       -> ())
  -> StableConfederalDataTransversalEndofunctor transform
stableConfederalDataTransversalEndofunctor =
  StableConfederalDataTransversalEndofunctor

-- | Apply the endofunctor to an object.
mapStableConfederalDataTransversalObject
  :: StableConfederalDataTransversalEndofunctor transform
  -> StableConfederalDataTransversal values
  -> StableConfederalDataTransversal (transform values)
mapStableConfederalDataTransversalObject
  (StableConfederalDataTransversalEndofunctor objectMap _ _ _) = objectMap

-- | Categorical 'fmap' for natural transformations.
mapStableConfederalDataTransversalArrow
  :: StableConfederalDataTransversalEndofunctor transform
  -> StableConfederalDataTransversal source
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalHom source target
  -> StableConfederalDataTransversalHom
       (transform source) (transform target)
mapStableConfederalDataTransversalArrow
  (StableConfederalDataTransversalEndofunctor _ arrowMap _ _) = arrowMap

-- | Invoke the endofunctor identity-law witness.
stableConfederalEndofunctorIdentity
  :: StableConfederalDataTransversalEndofunctor transform
  -> StableConfederalDataTransversal values
  -> ()
stableConfederalEndofunctorIdentity
  (StableConfederalDataTransversalEndofunctor _ _ law _) = law

-- | Invoke the endofunctor composition-law witness.
stableConfederalEndofunctorComposition
  :: StableConfederalDataTransversalEndofunctor transform
  -> StableConfederalDataTransversal source
  -> StableConfederalDataTransversal middle
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalHom middle target
  -> StableConfederalDataTransversalHom source middle
  -> ()
stableConfederalEndofunctorComposition
  (StableConfederalDataTransversalEndofunctor _ _ _ law) = law

-- | A commutative monad on the symmetric monoidal category of stable
-- confederal data transversals.
--
-- The Fubini arrow combines independent effects across horizontal sum.  Its
-- final witness states that the two orders induced by the symmetry agree.
type role CommutativeStableConfederalDataTransversalMonad nominal
data CommutativeStableConfederalDataTransversalMonad
  (transform :: Type -> Type) =
  CommutativeStableConfederalDataTransversalMonad
    (StableConfederalDataTransversalEndofunctor transform)
    (forall values.
      StableConfederalDataTransversal values
      -> StableConfederalDataTransversalHom values (transform values))
    (forall values.
      StableConfederalDataTransversal values
      -> StableConfederalDataTransversalHom
           (transform (transform values)) (transform values))
    (forall left right.
      StableConfederalDataTransversal left
      -> StableConfederalDataTransversal right
      -> StableConfederalDataTransversalHom
           (HorizontalSumValues (transform left) (transform right))
           (transform (HorizontalSumValues left right)))
    (forall values.
      StableConfederalDataTransversal values
      -> ())
    (forall values.
      StableConfederalDataTransversal values
      -> ())
    (forall values.
      StableConfederalDataTransversal values
      -> ())
    (forall left right.
      StableConfederalDataTransversal left
      -> StableConfederalDataTransversal right
      -> ())

-- | Construct a commutative monad from an endofunctor, unit, multiplication,
-- Fubini map, the three monad laws, and the commutativity law.
commutativeStableConfederalDataTransversalMonad
  :: StableConfederalDataTransversalEndofunctor transform
  -> (forall values.
       StableConfederalDataTransversal values
       -> StableConfederalDataTransversalHom values (transform values))
  -> (forall values.
       StableConfederalDataTransversal values
       -> StableConfederalDataTransversalHom
            (transform (transform values)) (transform values))
  -> (forall left right.
       StableConfederalDataTransversal left
       -> StableConfederalDataTransversal right
       -> StableConfederalDataTransversalHom
            (HorizontalSumValues (transform left) (transform right))
            (transform (HorizontalSumValues left right)))
  -> (forall values.
       StableConfederalDataTransversal values
       -> ())
  -> (forall values.
       StableConfederalDataTransversal values
       -> ())
  -> (forall values.
       StableConfederalDataTransversal values
       -> ())
  -> (forall left right.
       StableConfederalDataTransversal left
       -> StableConfederalDataTransversal right
       -> ())
  -> CommutativeStableConfederalDataTransversalMonad transform
commutativeStableConfederalDataTransversalMonad =
  CommutativeStableConfederalDataTransversalMonad

-- | Monad unit, analogous to Haskell's 'return'.
stableConfederalReturn
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> StableConfederalDataTransversalHom values (transform values)
stableConfederalReturn
  (CommutativeStableConfederalDataTransversalMonad _ unit _ _ _ _ _ _) =
    unit

-- | Monad endofunctor action, analogous to Haskell's 'fmap'.
stableConfederalFmap
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal source
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalHom source target
  -> StableConfederalDataTransversalHom
       (transform source) (transform target)
stableConfederalFmap
  (CommutativeStableConfederalDataTransversalMonad functor _ _ _ _ _ _ _) =
    mapStableConfederalDataTransversalArrow functor

-- | Monad multiplication, analogous to Haskell's 'join'.
stableConfederalJoin
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> StableConfederalDataTransversalHom
       (transform (transform values)) (transform values)
stableConfederalJoin
  (CommutativeStableConfederalDataTransversalMonad _ _ multiplication _ _ _ _ _) =
    multiplication

-- | Haskell-style Kleisli bind in the stable-confederal presheaf category.
stableConfederalBind
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal middle
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalHom source (transform middle)
  -> StableConfederalDataTransversalHom middle (transform target)
  -> StableConfederalDataTransversalHom source (transform target)
stableConfederalBind monad middle target computation continuation =
  stableConfederalJoin monad target
    Category.. stableConfederalFmap
      monad
      middle
      (mapMonadObject monad target)
      continuation
    Category.. computation

mapMonadObject
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> StableConfederalDataTransversal (transform values)
mapMonadObject
  (CommutativeStableConfederalDataTransversalMonad functor _ _ _ _ _ _ _) =
    mapStableConfederalDataTransversalObject functor

-- | The symmetric Fubini map witnessing compatibility with horizontal sum.
stableConfederalFubini
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal left
  -> StableConfederalDataTransversal right
  -> StableConfederalDataTransversalHom
       (HorizontalSumValues (transform left) (transform right))
       (transform (HorizontalSumValues left right))
stableConfederalFubini
  (CommutativeStableConfederalDataTransversalMonad _ _ _ fubini _ _ _ _) =
    fubini

stableConfederalMonadLeftIdentity
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> ()
stableConfederalMonadLeftIdentity
  (CommutativeStableConfederalDataTransversalMonad _ _ _ _ law _ _ _) = law

stableConfederalMonadRightIdentity
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> ()
stableConfederalMonadRightIdentity
  (CommutativeStableConfederalDataTransversalMonad _ _ _ _ _ law _ _) = law

stableConfederalMonadAssociativity
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> ()
stableConfederalMonadAssociativity
  (CommutativeStableConfederalDataTransversalMonad _ _ _ _ _ _ law _) = law

stableConfederalMonadCommutativity
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal left
  -> StableConfederalDataTransversal right
  -> ()
stableConfederalMonadCommutativity
  (CommutativeStableConfederalDataTransversalMonad _ _ _ _ _ _ _ law) = law
