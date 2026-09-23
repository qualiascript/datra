{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Common mechanics for presentation-only wrappers around stable-confederal
-- carriers.
module MapOperators.Internal
  ( wrapStableConfederalData
  , forgetStableConfederalDataWrapper
  ) where

import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , StableConfederalDataValue
  , mapStableConfederalData
  , stableConfederalData
  , stableConfederalDataComposition
  , stableConfederalDataHom
  , stableConfederalDataIdentity
  )

wrapStableConfederalData
  :: StableConfederalData underlying
  -> (forall object.
       StableConfederalDataValue wrapper object
       -> StableConfederalDataValue underlying object)
  -> (forall object.
       StableConfederalDataValue underlying object
       -> StableConfederalDataValue wrapper object)
  -> StableConfederalData wrapper
wrapStableConfederalData underlying unwrap wrap =
  stableConfederalData
    (\arrow value ->
      wrap (mapStableConfederalData underlying arrow (unwrap value)))
    (\value -> stableConfederalDataIdentity underlying (unwrap value))
    (\second first value ->
      stableConfederalDataComposition
        underlying second first (unwrap value))

forgetStableConfederalDataWrapper
  :: StableConfederalData wrapper
  -> StableConfederalData underlying
  -> (forall object.
       StableConfederalDataValue wrapper object
       -> StableConfederalDataValue underlying object)
  -> StableConfederalDataHom wrapper underlying
forgetStableConfederalDataWrapper wrapper underlying unwrap =
  stableConfederalDataHom wrapper underlying unwrap (\_ _ -> ())
