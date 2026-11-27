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
  , DatraType
  , DatraTypeFamily (..)
  , structuralDatraType
  , functionDatraType
  , primitiveDatraType
  , totalBlockDatraType
  , composedStructuralDatraType
  , datraTypeFamily
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

newtype DatraType = DatraType TypeImplementations
  deriving (Eq, Show)

structuralDatraType :: DatraType
structuralDatraType = makeDatraType StructuralTypeFamily

composedStructuralDatraType
  :: [DatraType]
  -> DatraType
composedStructuralDatraType _ = structuralDatraType

functionDatraType :: DatraType
functionDatraType = makeDatraType FunctionTypeFamily

primitiveDatraType :: PrimitiveType -> DatraType
primitiveDatraType kind =
  makeDatraType (PrimitiveTypeFamily kind)

-- | An evaluated begin/yield block is a total singleton type.  Its sole
-- member is the yielded value; block source is retained separately as
-- canonical presentation provenance rather than becoming nominal identity.
totalBlockDatraType :: DatraType
totalBlockDatraType = makeDatraType TotalBlockTypeFamily

makeDatraType :: DatraTypeFamily -> DatraType
makeDatraType = DatraType . TypeImplementations

datraTypeFamily
  :: DatraType
  -> DatraTypeFamily
datraTypeFamily =
  implementationFamily . datraTypeImplementations

datraTypeImplementations :: DatraType -> TypeImplementations
datraTypeImplementations (DatraType implementations) = implementations
