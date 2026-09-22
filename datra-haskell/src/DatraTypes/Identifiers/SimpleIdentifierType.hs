-- | Constant-string specialization of 'IdentifierType'.
module SimpleIdentifierType
  ( SimpleIdentifierType
  , simpleIdentifierType
  , simpleIdentifierTypeString
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
simpleIdentifierType identifierString federation =
  SimpleIdentifierType
    identifierString
    (identifierType federation (const identifierString))

simpleIdentifierTypeString
  :: SimpleIdentifierType federationScope index
  -> String
simpleIdentifierTypeString (SimpleIdentifierType identifierString _) =
  identifierString

simpleIdentifierTypeAsIdentifierType
  :: SimpleIdentifierType federationScope index
  -> IdentifierType federationScope index
simpleIdentifierTypeAsIdentifierType (SimpleIdentifierType _ value) = value
