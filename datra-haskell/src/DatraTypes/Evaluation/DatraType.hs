-- | The operations every runtime Datra type must provide.
--
-- Datra values are also singleton or federated types.  Construction therefore
-- requires an explicit dictionary naming the implementation used for the two
-- fundamental typing operations.  Keeping this dictionary data-only avoids
-- tying the runtime representation to the current Haskell evaluator: a future
-- self-hosted standard library can select the same capabilities declaratively.
module Evaluation.DatraType
  ( ASTMetaCategory (..)
  , BuiltinMetaType (..)
  , CanonicalType
  , DatraType
  , DatraTypeFamily (..)
  , makeCanonicalType
  , canonicalTypeAsDatraType
  , makeNonCanonicalDatraType
  , structuralDatraType
  , functionDatraType
  , builtinMetaDatraType
  , totalBlockDatraType
  , composedStructuralDatraType
  , datraTypeFamily
  , datraCanonicalType
  ) where

-- | Host-provided primitive families exposed through declarations in
-- @libs/std.datra@.  These names are capabilities, not language-level
-- bindings; the standard library remains responsible for publishing them.
data ASTMetaCategory
  = AnyAST
  | ExpressionAST
  | BlockAST
  | IdentifierExpressionAST
  deriving (Eq, Show)

data BuiltinMetaType
  = AnyMetaType
  | OrdinalMetaType
  | ASTMetaType ASTMetaCategory
  | NatRangeMetaType
  | IntRangeMetaType
  | NatValRangeMetaType
  | IntValRangeMetaType
  | TemplateMetaType
  | SyntaxTemplateMetaType
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

composedStructuralDatraType
  :: [DatraType]
  -> DatraType
composedStructuralDatraType components =
  if all (maybe False (const True) . datraCanonicalType) components
    then structuralDatraType
    else makeNonCanonicalDatraType StructuralTypeFamily

functionDatraType :: DatraType
functionDatraType = canonicalTypeAsDatraType (makeCanonicalType FunctionTypeFamily)

builtinMetaDatraType :: BuiltinMetaType -> DatraType
builtinMetaDatraType kind =
  case kind of
    AnyMetaType -> canonicalTypeAsDatraType
      (makeCanonicalType (BuiltinMetaTypeFamily kind))
    OrdinalMetaType -> canonicalTypeAsDatraType
      (makeCanonicalType (BuiltinMetaTypeFamily kind))
    TemplateMetaType -> canonicalTypeAsDatraType
      (makeCanonicalType (BuiltinMetaTypeFamily kind))
    _ -> makeNonCanonicalDatraType (BuiltinMetaTypeFamily kind)

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

datraTypeImplementations :: DatraType -> TypeImplementations
datraTypeImplementations datraType =
  case datraType of
    CanonicalDatraType (CanonicalType implementations) -> implementations
    NonCanonicalDatraType implementations -> implementations
