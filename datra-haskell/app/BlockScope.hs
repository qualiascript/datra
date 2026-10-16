-- | Declaration and projection rules shared by evaluation, inference and
-- canonical reconstruction. The caller supplies how binding values are read.
module BlockScope
  ( DependentDeclaration (..)
  , blockDeclaration
  , dependentDeclarationStaticName
  , declarationIsLet
  , declarationIsCanonicalValue
  , declarationAnnotation
  , declarationValue
  , isBlockDeclaration
  , isDependentDeclaration
  , dependentDeclaration
  , bindingNames
  ) where

import DatraLanguage.AST
import Data.Maybe (maybeToList)

data DependentDeclaration = DependentDeclaration
  { dependentDeclarationParts :: [StringTemplatePart Expression]
  , dependentDeclarationUsesTemplateSyntax :: Bool
  , dependentDeclarationIsLet :: Bool
  , dependentDeclarationIsCanonicalValue :: Bool
  , dependentDeclarationAnnotation :: Maybe Expression
  , dependentDeclarationImplementation :: Expression
  }

-- A literal declaration is the zero-capture member of the same declaration
-- family used by evaluated string templates. Surface syntax chooses the
-- template; scope construction and export do not choose a second data model.
blockDeclaration :: Expression -> Maybe DependentDeclaration
blockDeclaration expressionValue = do
  declaration <- dependentDeclaration expressionValue
  _ <- dependentDeclarationStaticName declaration
  pure declaration

dependentDeclarationStaticName :: DependentDeclaration -> Maybe String
dependentDeclarationStaticName declaration =
  case dependentDeclarationParts declaration of
    [StringTemplateLiteral name] -> Just name
    _ -> Nothing

declarationIsLet :: DependentDeclaration -> Bool
declarationIsLet = dependentDeclarationIsLet

declarationIsCanonicalValue :: DependentDeclaration -> Bool
declarationIsCanonicalValue = dependentDeclarationIsCanonicalValue

declarationAnnotation :: DependentDeclaration -> Maybe Expression
declarationAnnotation = dependentDeclarationAnnotation

declarationValue :: DependentDeclaration -> Expression
declarationValue = dependentDeclarationImplementation

isBlockDeclaration :: Expression -> Bool
isBlockDeclaration = isDependentDeclaration

isDependentDeclaration :: Expression -> Bool
isDependentDeclaration = maybe False (const True) . dependentDeclaration

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
        , dependentDeclarationAnnotation =
            In contextual <$> dependentDeclarationAnnotation declared
        , dependentDeclarationImplementation = In contextual
            (dependentDeclarationImplementation declared)
        }
    declaration strict canonical
        (IdentifierOperation (IdentifierString name) annotation given) =
      Just (makeDeclaration
        [StringTemplateLiteral name] False strict canonical annotation given)
    declaration strict canonical optional
      | Just (named@IdentifierOperation {}, _) <-
          optionalIdentifierExpression optional =
          declaration strict canonical named
    declaration strict canonical
        (IdentifierTemplateOperation parts annotation (Just given))
      = Just (makeDeclaration
          parts True strict canonical annotation (Just given))
    declaration _ _ _ = Nothing

    makeDeclaration parts usesTemplateSyntax strict canonical annotation given =
      DependentDeclaration
        parts
        usesTemplateSyntax
        strict
        canonical
        (annotationToCheck annotation given)
        (maybe annotation (\value -> if value == annotation then value
          else MapSpecification value annotation) given)

    annotationToCheck annotation (Just implementation)
      | annotation == implementation = Nothing
    annotationToCheck FunctionTypeExpression {} (Just FunctionBody {}) = Nothing
    annotationToCheck SyntaxType {} (Just _) = Nothing
    annotationToCheck annotation _ = Just annotation

    scopeTemplatePart _ literal@StringTemplateLiteral {} = literal
    scopeTemplatePart contextual
        (StringTemplateInterpolation expressionValue) =
      StringTemplateInterpolation (In contextual expressionValue)

bindingNames :: Expression -> [String]
bindingNames expressionValue =
  maybe [] (maybeToList . dependentDeclarationStaticName)
    (dependentDeclaration expressionValue)
