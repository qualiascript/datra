-- | The operations every runtime Datra type must provide.
--
-- Datra values are also singleton or federated types.  Construction therefore
-- requires an explicit dictionary naming the implementation used for the two
-- fundamental typing operations.  Keeping this dictionary data-only avoids
-- tying the runtime representation to the current Haskell evaluator: a future
-- self-hosted standard library can select the same capabilities declaratively.
module Evaluation.DatraType
  ( SyntaxCategory (..)
  , PrimitiveType (..)
  , CanonicalStringImplementation (..)
  , DatraType
  , DatraTypeFamily (..)
  , structuralDatraType
  , functionDatraType
  , primitiveDatraType
  , totalBlockDatraType
  , composedStructuralDatraType
  , datraTypeFamily
  , canonicalStringImplementation
  ) where

-- | Host-provided primitive families exposed through declarations in
-- @libs/std.datra@.  These names are capabilities, not language-level
-- bindings; the standard library remains responsible for publishing them.
data SyntaxCategory
  = ExpressionAST
  | BlockAST
  | FunctionBodyAST
  | DeclarationAST
  | DependentArgumentAST
  | IdentifierExpressionAST
  deriving (Eq, Show)

data PrimitiveType
  = AnyPrimitive
  | OrdinalPrimitive
  | SyntaxPrimitive SyntaxCategory
  | NatRangePrimitive
  | IntRangePrimitive
  | NatValRangePrimitive
  | IntValRangePrimitive
  deriving (Eq, Show)

-- | One family owns both fundamental typing operations. Keeping this as one
-- capability key makes it impossible to construct a type whose specification
-- and subfederation implementations come from different families.
data DatraTypeFamily
  = StructuralTypeFamily
  | FunctionTypeFamily
  | PrimitiveTypeFamily PrimitiveType
  | TotalBlockTypeFamily
  deriving (Eq, Show)

newtype TypeImplementations = TypeImplementations
  { implementationFamily :: DatraTypeFamily }
  deriving (Eq, Show)

-- | The canonical-string implementation carried by every Datra type.
data CanonicalStringImplementation
  = StructuralCanonicalString
  | FunctionCanonicalString
  | PrimitiveCanonicalString PrimitiveType
  | TotalBlockCanonicalString
  deriving (Eq, Show)

data DatraType = DatraType
  TypeImplementations
  CanonicalStringImplementation
  deriving (Eq, Show)

structuralDatraType :: DatraType
structuralDatraType = makeDatraType
  StructuralTypeFamily StructuralCanonicalString

composedStructuralDatraType
  :: [DatraType]
  -> DatraType
composedStructuralDatraType _ = structuralDatraType

functionDatraType :: DatraType
functionDatraType = makeDatraType
  FunctionTypeFamily FunctionCanonicalString

primitiveDatraType :: PrimitiveType -> DatraType
primitiveDatraType kind =
  makeDatraType
    (PrimitiveTypeFamily kind) (PrimitiveCanonicalString kind)

-- | An evaluated begin/yield block is a total singleton type.  Its sole
-- member is the yielded value; block source is retained separately as
-- canonical presentation provenance rather than becoming nominal identity.
totalBlockDatraType :: DatraType
totalBlockDatraType = makeDatraType
  TotalBlockTypeFamily TotalBlockCanonicalString

-- | There is no constructor for a Datra type without its canonical-string
-- implementation. Keeping this constructor private makes injectivity part of
-- the type witness rather than a second, fallible lookup table.
makeDatraType
  :: DatraTypeFamily
  -> CanonicalStringImplementation
  -> DatraType
makeDatraType family stringImplementation =
  DatraType (TypeImplementations family) stringImplementation

datraTypeFamily
  :: DatraType
  -> DatraTypeFamily
datraTypeFamily =
  implementationFamily . datraTypeImplementations

canonicalStringImplementation
  :: DatraType
  -> CanonicalStringImplementation
canonicalStringImplementation (DatraType _ implementation) = implementation

datraTypeImplementations :: DatraType -> TypeImplementations
datraTypeImplementations (DatraType implementations _) = implementations
