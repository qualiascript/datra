-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , dependentDeclaration
  , bindingNames
  ) where

import DatraLanguage.AST

data DependentDeclaration = DependentDeclaration
  { dependentDeclarationParts :: [StringTemplatePart Expression]
  , dependentDeclarationIsLet :: Bool
  , dependentDeclarationIsCanonicalValue :: Bool
  , dependentDeclarationImplementation :: Expression
  }

-- A declaration is an inferred assignment in block position. Identifier
-- annotations and dependent identifiers remain expressions until an explicit
-- assignment gives them a value.
dependentDeclaration :: Expression -> Maybe DependentDeclaration
dependentDeclaration = declaration False False
  where
    declaration _ True (Let _) = Nothing
    declaration _ canonical (Let value) = declaration True canonical value
    declaration strict _ (Val value) = declaration strict True value
    declaration strict canonical (In contextual value) = do
      declared <- declaration strict canonical value
      pure declared
        { dependentDeclarationParts =
            map (scopeTemplatePart contextual)
              (dependentDeclarationParts declared)
        , dependentDeclarationImplementation = In contextual
            (dependentDeclarationImplementation declared)
        }
    declaration strict canonical
        (IdentifierOperation (IdentifierString name) annotation (Just given))
      | annotation == given = Just (makeDeclaration
          [StringTemplateLiteral name] strict canonical given)
    declaration strict canonical optional
      | Just (named@IdentifierOperation {}, _) <-
          optionalIdentifierExpression optional =
          declaration strict canonical named
    declaration strict canonical
        (IdentifierTemplateOperation parts annotation (Just given))
      | annotation == given = Just (makeDeclaration
          parts strict canonical given)
    declaration _ _ _ = Nothing

    makeDeclaration parts strict canonical implementation =
      DependentDeclaration parts strict canonical implementation

    scopeTemplatePart _ literal@StringTemplateLiteral {} = literal
    scopeTemplatePart contextual
        (StringTemplateInterpolation expressionValue) =
      StringTemplateInterpolation (In contextual expressionValue)

-- Lexical binders include dependent identifiers and parameters, not only
-- executable declarations. Keep name extraction independent of declaration
-- recognition so those concepts cannot silently widen one another.
bindingNames :: Expression -> [String]
bindingNames expressionValue = case expressionValue of
  IdentifierOperation (IdentifierString name) _ _ -> [name]
  IdentifierTemplateOperation [StringTemplateLiteral name] _ _ -> [name]
  OptionalType inner -> bindingNames inner
  Let inner -> bindingNames inner
  Val inner -> bindingNames inner
  In _ inner -> bindingNames inner
  _ -> []
