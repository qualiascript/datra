{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Qualified-do syntax for stable-confederal Kleisli arrows.
--
-- Import this module qualified and enable @QualifiedDo@:
--
-- @
-- import qualified StableConfederalDataKleisli.Syntax as K
--
-- pipeline = K.do
--   validate
--   enrich
--   persist
-- @
--
-- This syntax expresses categorical sequencing.  It intentionally does not
-- define '(>>=)': a Kleisli arrow produces a categorical codomain, not a
-- Haskell value that could be supplied to a continuation.
module StableConfederalDataKleisli.Syntax
  ( Program
  , step
  , lift
  , run
  , return
  , (>>)
  , (>=>)
  , (<=<)
  ) where

import qualified Control.Category as Category
import Data.Kind (Type)
import Prelude hiding ((>>), return)
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  )
import StableConfederalDataKleisli
  ( StableConfederalDataKleisliHom
  , stableConfederalKleisliBind
  , stableConfederalKleisliHom
  , stableConfederalKleisliReturn
  )
import StableConfederalDataMonoidal
  ( CommutativeStableConfederalDataMonad
  , stableConfederalReturn
  )

-- | A composable Kleisli program.
--
-- The target object is carried with each program because it is required by
-- categorical bind.  The monad is supplied only when the whole program is
-- 'run', ensuring that every step is composed using the same monad.
type Program transform source target =
  ProgramResult transform source target ()

-- The final unit parameter tells GHC that a syntax statement has no Haskell
-- result to discard.  Without it, -Wunused-do-bind mistakes the categorical
-- target index for an ordinary do-notation result.
type role ProgramResult nominal nominal nominal representational
data ProgramResult
  (transform :: Type -> Type)
  (source :: Type)
  (target :: Type)
  result =
    ProgramResult
      (StableConfederalData target)
      (CommutativeStableConfederalDataMonad transform
        -> StableConfederalDataKleisliHom
             transform source target)

-- | Introduce an existing Kleisli arrow as one syntax step.
step
  :: StableConfederalData target
  -> StableConfederalDataKleisliHom transform source target
  -> Program transform source target
step target arrow = ProgramResult target (const arrow)

-- | Lift a base-category arrow into the Kleisli syntax.
lift
  :: StableConfederalData target
  -> StableConfederalDataHom source target
  -> Program transform source target
lift target arrow =
  ProgramResult target $ \monad ->
    stableConfederalKleisliHom
      (stableConfederalReturn monad target Category.. arrow)

-- | Interpret a program using one commutative stable-confederal monad.
run
  :: CommutativeStableConfederalDataMonad transform
  -> Program transform source target
  -> StableConfederalDataKleisliHom transform source target
run monad (ProgramResult _ build) = build monad

-- | The identity program, given by the Kleisli-category identity.
return
  :: StableConfederalData values
  -> Program transform values values
return values =
  ProgramResult values $ \monad ->
    stableConfederalKleisliReturn monad values

-- | Sequence two programs from left to right.
--
-- This is the operation used for expression statements by @QualifiedDo@.
infixl 1 >>
(>>)
  :: Program transform source middle
  -> Program transform middle target
  -> Program transform source target
ProgramResult middle buildFirst >> ProgramResult target buildSecond =
  ProgramResult target $ \monad ->
    stableConfederalKleisliBind
      monad
      middle
      target
      (buildFirst monad)
      (buildSecond monad)

-- | Left-to-right Kleisli composition.
infixr 1 >=>
(>=>)
  :: Program transform source middle
  -> Program transform middle target
  -> Program transform source target
(>=>) = (>>)

-- | Right-to-left Kleisli composition.
infixr 1 <=<
(<=<)
  :: Program transform middle target
  -> Program transform source middle
  -> Program transform source target
second <=< first = first >> second
