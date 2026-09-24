{-# LANGUAGE RoleAnnotations #-}

-- | Dependent identifier types over an existing Atlas-map federation.
--
-- Each federation index denotes the two-position map whose first page is the
-- identifier string followed by the selected value. The string function is
-- intentionally part of the type value: access and specification must retain
-- the dependency instead of treating the pair as an ordinary map product.
module DependentIdentifierType
  ( DependentIdentifierType
  , DependentIdentifierTypeMember (..)
  , dependentIdentifierType
  , dependentIdentifierTypeFederation
  , dependentIdentifierTypeStringAt
  , dependentIdentifierTypeMemberAt
  ) where

import AtlasMapFederation (AtlasMapFederation)

type role DependentIdentifierType nominal nominal
data DependentIdentifierType federationScope index = DependentIdentifierType
  (AtlasMapFederation federationScope index)
  (index -> String)

data DependentIdentifierTypeMember index = DependentIdentifierTypeMember
  { identifierMemberString :: String
  , identifierMemberValue :: index
  }

dependentIdentifierType
  :: AtlasMapFederation federationScope index
  -> (index -> String)
  -> DependentIdentifierType federationScope index
dependentIdentifierType = DependentIdentifierType

dependentIdentifierTypeFederation
  :: DependentIdentifierType federationScope index
  -> AtlasMapFederation federationScope index
dependentIdentifierTypeFederation (DependentIdentifierType federation _) = federation

dependentIdentifierTypeStringAt
  :: DependentIdentifierType federationScope index
  -> index
  -> String
dependentIdentifierTypeStringAt (DependentIdentifierType _ stringAt) = stringAt

dependentIdentifierTypeMemberAt
  :: DependentIdentifierType federationScope index
  -> index
  -> DependentIdentifierTypeMember index
dependentIdentifierTypeMemberAt value index =
  DependentIdentifierTypeMember (dependentIdentifierTypeStringAt value index) index
