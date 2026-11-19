{-# LANGUAGE RoleAnnotations #-}

-- | Dependent argument types over an existing Atlas-map federation.
--
-- Each federation index denotes the two-position map whose first page is the
-- identifier string followed by the selected value. The string function is
-- intentionally part of the type value: access and specification must retain
-- the dependency instead of treating the pair as an ordinary map product.
module DependentArgumentType
  ( DependentArgumentType
  , DependentArgumentTypeMember (..)
  , dependentArgumentType
  , dependentArgumentTypeFederation
  , dependentArgumentTypeStringAt
  , dependentArgumentTypeMemberAt
  ) where

import AtlasMapFederation (AtlasMapFederation)
import DatraTypes.DependentTypes
  ( DependentSum
  , dependentSum
  , dependentSumDomain
  , dependentSumFiberAt
  )

type role DependentArgumentType nominal nominal
newtype DependentArgumentType federationScope index =
  DependentArgumentType
    (DependentSum
      (AtlasMapFederation federationScope index)
      index
      String)

data DependentArgumentTypeMember index = DependentArgumentTypeMember
  { identifierMemberString :: String
  , identifierMemberValue :: index
  }

dependentArgumentType
  :: AtlasMapFederation federationScope index
  -> (index -> String)
  -> DependentArgumentType federationScope index
dependentArgumentType federation stringAt =
  DependentArgumentType (dependentSum federation stringAt)

dependentArgumentTypeFederation
  :: DependentArgumentType federationScope index
  -> AtlasMapFederation federationScope index
dependentArgumentTypeFederation (DependentArgumentType value) =
  dependentSumDomain value

dependentArgumentTypeStringAt
  :: DependentArgumentType federationScope index
  -> index
  -> String
dependentArgumentTypeStringAt (DependentArgumentType value) =
  dependentSumFiberAt value

dependentArgumentTypeMemberAt
  :: DependentArgumentType federationScope index
  -> index
  -> DependentArgumentTypeMember index
dependentArgumentTypeMemberAt value index =
  DependentArgumentTypeMember (dependentArgumentTypeStringAt value index) index
