-- | The operations every runtime Datra type must provide.
--
-- Datra values are also singleton or federated types.  Construction therefore
-- requires an explicit dictionary naming the implementation used for the two
-- fundamental typing operations.  Keeping this dictionary data-only avoids
-- tying the runtime representation to the current Haskell evaluator: a future
-- self-hosted standard library can select the same capabilities declaratively.
module Evaluation.DatraType
  ( BuiltinMetaType (..)
  , CanonicalType
  , DatraType
  , DatraTypeFamily (..)
  , StringRepresentation (..)
  , makeCanonicalType
  , canonicalTypeAsDatraType
  , makeNonCanonicalDatraType
  , structuralDatraType
  , weakStructuralDatraType
  , functionDatraType
  , builtinMetaDatraType
  , totalBlockDatraType
  , structuralDatraTypeWith
  , composedStructuralDatraType
  , datraTypeFamily
  , datraCanonicalType
  , datraStringRepresentation
  ) where

-- | Host-provided primitive families exposed through declarations in
-- @std_lib.datra@.  These names are capabilities, not language-level
-- bindings; the standard library remains responsible for publishing them.
data BuiltinMetaType
  = ASTMetaType (Maybe String)
  | NatRangeMetaType
  | IntRangeMetaType
  | NatValRangeMetaType
  | IntValRangeMetaType
  | StringTemplateMetaType
  deriving (Eq, Show)

-- | One family owns both fundamental typing operations. Keeping this as one
-- capability key makes it impossible to construct a type whose specification
-- and subfederation implementations come from different families.
data DatraTypeFamily
  = StructuralTypeFamily
  | FunctionTypeFamily
  | BuiltinMetaTypeFamily BuiltinMetaType
  | TotalBlockTypeFamily
  deriving (Eq, Show)

-- | Canonical string conversion is injective and can participate in
-- specification.  Weak conversion is display-only.  Both are legitimate
-- Datra types; this capability records the distinction without demoting the
-- weak-only family to an invalid type.
data StringRepresentation
  = CanonicalStringRepresentation
  | WeakStringRepresentation
  deriving (Eq, Show)

newtype TypeImplementations = TypeImplementations
  { implementationFamily :: DatraTypeFamily }
  deriving (Eq, Show)

-- | The narrower class of Datra types with an injective, round-trippable
-- source representation. Specification and subfederation remain mandatory.
newtype CanonicalType = CanonicalType TypeImplementations
  deriving (Eq, Show)

-- | The complete runtime typing contract. Every Datra type implements
-- specification and subfederation; only the canonical branch additionally
-- promises an injective source representation.
data DatraType
  = CanonicalDatraType CanonicalType
  | NonCanonicalDatraType TypeImplementations
  deriving (Eq, Show)

structuralDatraType :: DatraType
structuralDatraType = canonicalTypeAsDatraType
  (makeCanonicalType StructuralTypeFamily)

weakStructuralDatraType :: DatraType
weakStructuralDatraType = makeNonCanonicalDatraType StructuralTypeFamily

structuralDatraTypeWith
  :: StringRepresentation
  -> DatraType
structuralDatraTypeWith representation =
  case representation of
    CanonicalStringRepresentation -> structuralDatraType
    WeakStringRepresentation -> weakStructuralDatraType

composedStructuralDatraType
  :: [DatraType]
  -> DatraType
composedStructuralDatraType components =
  structuralDatraTypeWith
    (if all ((== CanonicalStringRepresentation)
          . datraStringRepresentation) components
      then CanonicalStringRepresentation
      else WeakStringRepresentation)

functionDatraType :: DatraType
functionDatraType = makeNonCanonicalDatraType FunctionTypeFamily

builtinMetaDatraType :: BuiltinMetaType -> DatraType
builtinMetaDatraType kind =
  makeNonCanonicalDatraType (BuiltinMetaTypeFamily kind)

-- | An evaluated begin/yield block is a total singleton type.  Its sole
-- member is the yielded value; block source is retained separately as
-- canonical presentation provenance rather than becoming nominal identity.
totalBlockDatraType :: DatraType
totalBlockDatraType = canonicalTypeAsDatraType
  (makeCanonicalType TotalBlockTypeFamily)

-- | Constructing either layer requires both fundamental typing operations.
-- There is deliberately no constructor for a partial Datra type.
makeCanonicalType
  :: DatraTypeFamily
  -> CanonicalType
makeCanonicalType family =
  CanonicalType (TypeImplementations family)

canonicalTypeAsDatraType :: CanonicalType -> DatraType
canonicalTypeAsDatraType = CanonicalDatraType

makeNonCanonicalDatraType
  :: DatraTypeFamily
  -> DatraType
makeNonCanonicalDatraType family =
  NonCanonicalDatraType (TypeImplementations family)

datraTypeFamily
  :: DatraType
  -> DatraTypeFamily
datraTypeFamily =
  implementationFamily . datraTypeImplementations

datraCanonicalType :: DatraType -> Maybe CanonicalType
datraCanonicalType datraType =
  case datraType of
    CanonicalDatraType canonical -> Just canonical
    NonCanonicalDatraType _ -> Nothing

datraStringRepresentation :: DatraType -> StringRepresentation
datraStringRepresentation datraType =
  case datraCanonicalType datraType of
    Just _ -> CanonicalStringRepresentation
    Nothing -> WeakStringRepresentation

datraTypeImplementations :: DatraType -> TypeImplementations
datraTypeImplementations datraType =
  case datraType of
    CanonicalDatraType (CanonicalType implementations) -> implementations
    NonCanonicalDatraType implementations -> implementations
