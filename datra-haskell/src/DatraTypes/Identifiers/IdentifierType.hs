{-# LANGUAGE RoleAnnotations #-}

-- | Dependent identifier types over an existing Atlas-map federation.
--
-- Each federation index denotes the two-position map whose first page is the
-- identifier string followed by the selected value. The string function is
-- intentionally part of the type value: access and specification must retain
-- the dependency instead of treating the pair as an ordinary map product.
module IdentifierType
  ( IdentifierType
  , IdentifierTypeMember (..)
  , identifierType
  , identifierTypeFederation
  , identifierTypeStringAt
  , identifierTypeMemberAt
  ) where

import AtlasMapFederation (AtlasMapFederation)

type role IdentifierType nominal nominal
data IdentifierType federationScope index = IdentifierType
  (AtlasMapFederation federationScope index)
  (index -> String)

data IdentifierTypeMember index = IdentifierTypeMember
  { identifierMemberString :: String
  , identifierMemberValue :: index
  }

identifierType
  :: AtlasMapFederation federationScope index
  -> (index -> String)
  -> IdentifierType federationScope index
identifierType = IdentifierType

identifierTypeFederation
  :: IdentifierType federationScope index
  -> AtlasMapFederation federationScope index
identifierTypeFederation (IdentifierType federation _) = federation

identifierTypeStringAt
  :: IdentifierType federationScope index
  -> index
  -> String
identifierTypeStringAt (IdentifierType _ stringAt) = stringAt

identifierTypeMemberAt
  :: IdentifierType federationScope index
  -> index
  -> IdentifierTypeMember index
identifierTypeMemberAt value index =
  IdentifierTypeMember (identifierTypeStringAt value index) index
