{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the Kleisli category for a stable-confederal
-- monad.
module StableConfederalDataKleisli.Internal
  ( StableConfederalDataKleisliHom
  , stableConfederalKleisliHom
  , stableConfederalKleisliArrow
  , mapStableConfederalKleisliHom
  , stableConfederalKleisliReturn
  , composeStableConfederalKleisliHoms
  , stableConfederalKleisliBind
  ) where

import Data.Kind (Type)
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , StableConfederalDataValue
  , mapStableConfederalDataHom
  )
import StableConfederalDataMonoidal
  ( CommutativeStableConfederalDataMonad
  , stableConfederalBind
  , stableConfederalReturn
  )

-- | A Kleisli arrow @source -> target@ is a natural transformation
-- @source -> T target@ in the base presheaf category.
type role StableConfederalDataKleisliHom nominal nominal nominal
newtype StableConfederalDataKleisliHom
  (transform :: Type -> Type)
  (source :: Type)
  (target :: Type) =
    StableConfederalDataKleisliHom
      (StableConfederalDataHom source (transform target))

-- | Regard a base-category arrow into @T target@ as a Kleisli arrow.
stableConfederalKleisliHom
  :: StableConfederalDataHom source (transform target)
  -> StableConfederalDataKleisliHom transform source target
stableConfederalKleisliHom =
  StableConfederalDataKleisliHom

-- | Forget a Kleisli arrow to its underlying natural transformation.
stableConfederalKleisliArrow
  :: StableConfederalDataKleisliHom transform source target
  -> StableConfederalDataHom source (transform target)
stableConfederalKleisliArrow
  (StableConfederalDataKleisliHom arrow) = arrow

-- | Evaluate a Kleisli arrow at one Atlas confederation.
mapStableConfederalKleisliHom
  :: StableConfederalDataKleisliHom transform source target
  -> StableConfederalDataValue source object
  -> StableConfederalDataValue (transform target) object
mapStableConfederalKleisliHom =
  mapStableConfederalDataHom . stableConfederalKleisliArrow

-- | The identity Kleisli arrow, supplied by the monad unit.
stableConfederalKleisliReturn
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData values
  -> StableConfederalDataKleisliHom transform values values
stableConfederalKleisliReturn monad =
  stableConfederalKleisliHom . stableConfederalReturn monad

-- | Compose Kleisli arrows in categorical order.
composeStableConfederalKleisliHoms
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData middle
  -> StableConfederalData target
  -> StableConfederalDataKleisliHom transform middle target
  -> StableConfederalDataKleisliHom transform source middle
  -> StableConfederalDataKleisliHom transform source target
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
  :: CommutativeStableConfederalDataMonad transform
  -> StableConfederalData middle
  -> StableConfederalData target
  -> StableConfederalDataKleisliHom transform source middle
  -> StableConfederalDataKleisliHom transform middle target
  -> StableConfederalDataKleisliHom transform source target
stableConfederalKleisliBind monad middle target computation continuation =
  composeStableConfederalKleisliHoms
    monad middle target continuation computation
