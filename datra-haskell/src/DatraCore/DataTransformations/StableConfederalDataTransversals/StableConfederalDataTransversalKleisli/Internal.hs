{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the Kleisli category for a stable-confederal
-- monad.
module StableConfederalDataTransversalKleisli.Internal
  ( StableConfederalDataTransversalKleisliHom
  , stableConfederalKleisliHom
  , stableConfederalKleisliArrow
  , mapStableConfederalKleisliHom
  , stableConfederalKleisliReturn
  , composeStableConfederalKleisliHoms
  , stableConfederalKleisliBind
  ) where

import Data.Kind (Type)
import StableConfederalDataTransversal
  ( StableConfederalDataTransversal
  , StableConfederalDataTransversalHom
  , StableConfederalDataTransversalValue
  , mapStableConfederalDataTransversalHom
  )
import StableConfederalDataTransversalMonoidal
  ( CommutativeStableConfederalDataTransversalMonad
  , stableConfederalBind
  , stableConfederalReturn
  )

-- | A Kleisli arrow @source -> target@ is a natural transformation
-- @source -> T target@ in the base presheaf category.
type role StableConfederalDataTransversalKleisliHom nominal nominal nominal
newtype StableConfederalDataTransversalKleisliHom
  (transform :: Type -> Type)
  (source :: Type)
  (target :: Type) =
    StableConfederalDataTransversalKleisliHom
      (StableConfederalDataTransversalHom source (transform target))

-- | Regard a base-category arrow into @T target@ as a Kleisli arrow.
stableConfederalKleisliHom
  :: StableConfederalDataTransversalHom source (transform target)
  -> StableConfederalDataTransversalKleisliHom transform source target
stableConfederalKleisliHom =
  StableConfederalDataTransversalKleisliHom

-- | Forget a Kleisli arrow to its underlying natural transformation.
stableConfederalKleisliArrow
  :: StableConfederalDataTransversalKleisliHom transform source target
  -> StableConfederalDataTransversalHom source (transform target)
stableConfederalKleisliArrow
  (StableConfederalDataTransversalKleisliHom arrow) = arrow

-- | Evaluate a Kleisli arrow at one Atlas confederation.
mapStableConfederalKleisliHom
  :: StableConfederalDataTransversalKleisliHom transform source target
  -> StableConfederalDataTransversalValue source object
  -> StableConfederalDataTransversalValue (transform target) object
mapStableConfederalKleisliHom =
  mapStableConfederalDataTransversalHom . stableConfederalKleisliArrow

-- | The identity Kleisli arrow, supplied by the monad unit.
stableConfederalKleisliReturn
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal values
  -> StableConfederalDataTransversalKleisliHom transform values values
stableConfederalKleisliReturn monad =
  stableConfederalKleisliHom . stableConfederalReturn monad

-- | Compose Kleisli arrows in categorical order.
composeStableConfederalKleisliHoms
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal middle
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalKleisliHom transform middle target
  -> StableConfederalDataTransversalKleisliHom transform source middle
  -> StableConfederalDataTransversalKleisliHom transform source target
composeStableConfederalKleisliHoms monad middle target second first =
  stableConfederalKleisliHom
    (stableConfederalBind
      monad
      middle
      target
      (stableConfederalKleisliArrow first)
      (stableConfederalKleisliArrow second))

-- | Haskell-style bind order: computation first, continuation second.
stableConfederalKleisliBind
  :: CommutativeStableConfederalDataTransversalMonad transform
  -> StableConfederalDataTransversal middle
  -> StableConfederalDataTransversal target
  -> StableConfederalDataTransversalKleisliHom transform source middle
  -> StableConfederalDataTransversalKleisliHom transform middle target
  -> StableConfederalDataTransversalKleisliHom transform source target
stableConfederalKleisliBind monad middle target computation continuation =
  composeStableConfederalKleisliHoms
    monad middle target continuation computation
