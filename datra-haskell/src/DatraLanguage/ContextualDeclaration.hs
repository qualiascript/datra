-- | Ordinary dependent declarations implementing Datra's contextual roles.
module DatraLanguage.ContextualDeclaration
  ( ContextualRole (..)
  , contextualSurfaceName
  , contextualPrivateName
  , contextualIdentifier
  , contextualRoleForIdentifier
  , contextualAccess
  , contextualAccessAt
  , isContextualAccessOf
  , contextualSurfaceDeclaration
  ) where

import DatraLanguage.AST
  ( DependentDeclaration (..)
  , DependentDeclarationHead (..)
  , Expression (..)
  , IdentifierString (..)
  )
import DatraLanguage.ContextualRole
import Numeric.Natural (Natural)

contextualIdentifier :: ContextualRole -> IdentifierString
contextualIdentifier = IdentifierString . contextualPrivateName

contextualRoleForIdentifier :: IdentifierString -> Maybe ContextualRole
contextualRoleForIdentifier identifier = case
    [ role
    | role <- [minBound .. maxBound]
    , contextualIdentifier role == identifier
    ] of
  role : _ -> Just role
  [] -> Nothing

contextualAccess :: ContextualRole -> Expression
contextualAccess role = contextualAccessAt role 0

contextualAccessAt :: ContextualRole -> Natural -> Expression
contextualAccessAt role depth = FunctionApplication
  (IdentifierReference (contextualIdentifier role))
  (EllipsisNatural depth)

isContextualAccessOf :: ContextualRole -> Expression -> Bool
isContextualAccessOf role expression = case expression of
  FunctionApplication (IdentifierReference actual) argument
    | actual == contextualIdentifier role ->
        argument == EllipsisNatural 0 || argument == AtlasMap []
  _ -> False

-- | The surface definition installed beside its private primitive.
-- For example, @def this := _this 0@ is an ordinary singleton declaration;
-- the contextual name is not syntax and does not require template lookup.
contextualSurfaceDeclaration
  :: ContextualRole
  -> DependentDeclaration Expression
contextualSurfaceDeclaration role = DependentDeclaration
  (SimpleIdentifierDeclarationHead
    (IdentifierString (contextualSurfaceName role)))
  False True False
  (contextualAccessAt role 0)
