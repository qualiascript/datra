{-# LANGUAGE RoleAnnotations #-}

-- | The two dependent type constructors shared by Datra's concrete type
-- families.  These structures deliberately retain their indexing family:
-- consumers select a fibre only after supplying a witness from the domain.
module DatraTypes.DependentTypes
  ( DependentSum
  , DependentSumMember (..)
  , dependentSum
  , dependentSumDomain
  , dependentSumFiberAt
  , dependentSumMemberAt
  , DependentProduct
  , dependentProduct
  , dependentProductDomain
  , dependentProductFiberAt
  ) where

type role DependentSum nominal nominal nominal
data DependentSum domain index fiber = DependentSum
  domain
  (index -> fiber)

data DependentSumMember index fiber = DependentSumMember
  { dependentSumMemberIndex :: index
  , dependentSumMemberFiber :: fiber
  }

dependentSum
  :: domain
  -> (index -> fiber)
  -> DependentSum domain index fiber
dependentSum = DependentSum

dependentSumDomain
  :: DependentSum domain index fiber
  -> domain
dependentSumDomain (DependentSum domain _) = domain

dependentSumFiberAt
  :: DependentSum domain index fiber
  -> index
  -> fiber
dependentSumFiberAt (DependentSum _ fiberAt) = fiberAt

dependentSumMemberAt
  :: DependentSum domain index fiber
  -> index
  -> DependentSumMember index fiber
dependentSumMemberAt value index =
  DependentSumMember index (dependentSumFiberAt value index)

type role DependentProduct nominal nominal nominal
data DependentProduct domain index fiber = DependentProduct
  domain
  (index -> fiber)

dependentProduct
  :: domain
  -> (index -> fiber)
  -> DependentProduct domain index fiber
dependentProduct = DependentProduct

dependentProductDomain
  :: DependentProduct domain index fiber
  -> domain
dependentProductDomain (DependentProduct domain _) = domain

dependentProductFiberAt
  :: DependentProduct domain index fiber
  -> index
  -> fiber
dependentProductFiberAt (DependentProduct _ fiberAt) = fiberAt
