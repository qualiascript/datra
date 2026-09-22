-- | Constant-name specialization of 'IdentifierType'.
module SimpleIdentifierType
  ( SimpleIdentifierType
  , simpleIdentifierType
  , simpleIdentifierTypeName
  , simpleIdentifierTypeAsIdentifierType
  ) where

import AtlasMapFederation (AtlasMapFederation)
import IdentifierType (IdentifierType, identifierType)

data SimpleIdentifierType federationScope index = SimpleIdentifierType
  String
  (IdentifierType federationScope index)

simpleIdentifierType
  :: String
  -> AtlasMapFederation federationScope index
  -> SimpleIdentifierType federationScope index
simpleIdentifierType name federation =
  SimpleIdentifierType name (identifierType federation (const name))

simpleIdentifierTypeName
  :: SimpleIdentifierType federationScope index
  -> String
simpleIdentifierTypeName (SimpleIdentifierType name _) = name

simpleIdentifierTypeAsIdentifierType
  :: SimpleIdentifierType federationScope index
  -> IdentifierType federationScope index
simpleIdentifierTypeAsIdentifierType (SimpleIdentifierType _ value) = value
