-- | The operations every runtime Datra type must provide.
--
-- Datra values are also singleton or federated types.  Construction therefore
-- requires an explicit dictionary naming the implementation used for the two
-- fundamental typing operations.  Keeping this dictionary data-only avoids
-- tying the runtime representation to the current Haskell evaluator: a future
-- self-hosted standard library can select the same capabilities declaratively.
module Evaluation.CanonicalType
  ( BuiltinMetaType (..)
  , CanonicalType
  , SpecificationImplementation (..)
  , SubfederationImplementation (..)
  , StringRepresentation (..)
  , structuralCanonicalType
  , weakStructuralCanonicalType
  , functionCanonicalType
  , builtinMetaCanonicalType
  , totalBlockCanonicalType
  , structuralCanonicalTypeWith
  , composedStructuralCanonicalType
  , canonicalSpecificationImplementation
  , canonicalSubfederationImplementation
  , canonicalStringRepresentation
  ) where

-- | Host-provided primitive families exposed through declarations in
-- @standard_library.datra@.  These names are capabilities, not language-level
-- bindings; the standard library remains responsible for publishing them.
data BuiltinMetaType
  = ASTMetaType (Maybe String)
  | NatRangeMetaType
  | IntRangeMetaType
  | StringTemplateMetaType
  deriving (Eq, Show)

data SpecificationImplementation
  = StructuralSpecification
  | FunctionSpecification
  | BuiltinMetaSpecification BuiltinMetaType
  | TotalBlockSpecification
  deriving (Eq, Show)

data SubfederationImplementation
  = StructuralSubfederation
  | FunctionSubfederation
  | BuiltinMetaSubfederation BuiltinMetaType
  | TotalBlockSubfederation
  deriving (Eq, Show)

-- | Canonical string conversion is injective and can participate in
-- specification.  Weak conversion is display-only.  Both are legitimate
-- Datra types; this capability records the distinction without demoting the
-- weak-only family to an invalid type.
data StringRepresentation
  = CanonicalStringRepresentation
  | WeakStringRepresentation
  deriving (Eq, Show)

-- | A value is a canonical Datra type only when both fundamental operations are
-- present.  There is intentionally no partial or optional constructor.
data CanonicalType = CanonicalType
  { canonicalSpecificationImplementation :: SpecificationImplementation
  , canonicalSubfederationImplementation :: SubfederationImplementation
  , canonicalStringRepresentation :: StringRepresentation
  }
  deriving (Eq, Show)

structuralCanonicalType :: CanonicalType
structuralCanonicalType = CanonicalType
  StructuralSpecification
  StructuralSubfederation
  CanonicalStringRepresentation

weakStructuralCanonicalType :: CanonicalType
weakStructuralCanonicalType =
  structuralCanonicalTypeWith WeakStringRepresentation

structuralCanonicalTypeWith
  :: StringRepresentation
  -> CanonicalType
structuralCanonicalTypeWith representation = CanonicalType
  StructuralSpecification StructuralSubfederation representation

composedStructuralCanonicalType
  :: [CanonicalType]
  -> CanonicalType
composedStructuralCanonicalType components =
  structuralCanonicalTypeWith
    (if all ((== CanonicalStringRepresentation)
          . canonicalStringRepresentation) components
      then CanonicalStringRepresentation
      else WeakStringRepresentation)

functionCanonicalType :: CanonicalType
functionCanonicalType = CanonicalType
  FunctionSpecification FunctionSubfederation WeakStringRepresentation

builtinMetaCanonicalType :: BuiltinMetaType -> CanonicalType
builtinMetaCanonicalType kind = CanonicalType
  (BuiltinMetaSpecification kind)
  (BuiltinMetaSubfederation kind)
  WeakStringRepresentation

-- | An evaluated begin/yield block is a total singleton type.  Its sole
-- member is the yielded value; block source is retained separately as
-- canonical presentation provenance rather than becoming nominal identity.
totalBlockCanonicalType :: CanonicalType
totalBlockCanonicalType = CanonicalType
  TotalBlockSpecification
  TotalBlockSubfederation
  CanonicalStringRepresentation
