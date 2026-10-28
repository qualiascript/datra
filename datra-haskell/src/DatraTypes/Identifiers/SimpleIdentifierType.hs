-- | Constant-string specialization of 'DependentArgumentType'.
module SimpleIdentifierType
  ( SimpleIdentifierType
  , simpleIdentifierType
  , simpleIdentifierTypeString
  , simpleIdentifierTypeAsDependentArgumentType
  ) where

import AtlasMapFederation (AtlasMapFederation)
import DependentArgumentType (DependentArgumentType, dependentArgumentType)

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

simpleIdentifierTypeAsDependentArgumentType
  :: SimpleIdentifierType federationScope index
  -> DependentArgumentType federationScope index
simpleIdentifierTypeAsDependentArgumentType
    (SimpleIdentifierType identifierString federation) =
  dependentArgumentType federation (const identifierString)
