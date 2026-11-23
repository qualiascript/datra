-- | Canonical names for AST forms which are not ordinary language operators
-- or reserved source words.  Canonical rendering and decoding share this
-- vocabulary so neither side owns stringly node-name dispatch.
module DatraLanguage.AST.CanonicalForm
  ( CanonicalForm (..)
  , canonicalFormName
  ) where

data CanonicalForm
  = ArgumentativeMapForm
  | FunctionForm
  | GenericIntroductionForm
  | InModuleForm
  | GenericPrefixForm
  | BindingsForm
  | IdentifierReferenceForm
  | LineBreakForm
  | UnresolvedSyntaxForm
  | GenericBinderForm
  | WithScopesForm
  deriving (Bounded, Enum, Eq, Show)

canonicalFormName :: CanonicalForm -> String
canonicalFormName ArgumentativeMapForm = "argumentative-map"
canonicalFormName FunctionForm = "fun"
canonicalFormName GenericIntroductionForm = "generic-introduction"
canonicalFormName InModuleForm = "in-module"
canonicalFormName GenericPrefixForm = "generic-prefix"
canonicalFormName BindingsForm = "bindings"
canonicalFormName IdentifierReferenceForm = "ref"
canonicalFormName LineBreakForm = "line-break"
canonicalFormName UnresolvedSyntaxForm = "unresolved-syntax"
canonicalFormName GenericBinderForm = "generic-binder"
canonicalFormName WithScopesForm = "with-scopes"
