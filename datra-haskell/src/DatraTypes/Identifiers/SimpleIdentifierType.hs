-- | Constant-string specialization of 'DependentIdentifierType'.
module SimpleIdentifierType
  ( SimpleIdentifierType
  , simpleIdentifierType
  , simpleIdentifierTypeString
  , simpleIdentifierTypeAsDependentIdentifierType
  ) where

import AtlasMapFederation (AtlasMapFederation)
import DependentIdentifierType (DependentIdentifierType, dependentIdentifierType)

data SimpleIdentifierType federationScope index = SimpleIdentifierType
  String
  (AtlasMapFederation federationScope index)

simpleIdentifierType
  :: String
  -> AtlasMapFederation federationScope index
  -> SimpleIdentifierType federationScope index
simpleIdentifierType identifierString federation =
  SimpleIdentifierType identifierString federation

simpleIdentifierTypeString
  :: SimpleIdentifierType federationScope index
  -> String
simpleIdentifierTypeString (SimpleIdentifierType identifierString _) =
  identifierString

simpleIdentifierTypeAsDependentIdentifierType
  :: SimpleIdentifierType federationScope index
  -> DependentIdentifierType federationScope index
simpleIdentifierTypeAsDependentIdentifierType
    (SimpleIdentifierType identifierString federation) =
  dependentIdentifierType federation (const identifierString)
