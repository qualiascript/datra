-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , DeclarationModifier (..)
  , dependentDeclarationIsLet
  , dependentDeclarationIsDefinition
  , dependentDeclarationIsCanonicalValue
  , dependentDeclaration
  , dependentDeclarationCandidate
  , applyDeclarationModifier
  , invalidDependentDeclarationModifiers
  , dependentDeclarationNameExpression
  , dependentDeclarationNameFamilyExpression
  , prependDependentDeclarationName
  , dependentDeclarationWithImplementation
  , bindingNames
  ) where

import DatraLanguage.AST
import DatraLanguage.AST.Operator (operatorCanonicalSymbol)

-- A declaration is an inferred assignment in block position. Identifier
-- annotations and dependent arguments remain expressions until an explicit
-- assignment gives them a value.
dependentDeclaration :: Expression -> Maybe (DependentDeclaration Expression)
dependentDeclaration = declaration
  where
    declaration (DeclarationExpression semantic) = Just semantic
    declaration (SyntaxBoundary value) = declaration value
    declaration
        (MapSpecification given (DependentArgument name Nothing)) =
      Just (makeDeclaration name given)
    declaration _ = Nothing

    makeDeclaration headValue implementation =
      DependentDeclaration
        headValue [] implementation

-- | Record one modifier in the right-to-left order in which syntax expansion
-- applies it. Invalid order and repetition remain representable until the
-- declaration reaches its block boundary, where one diagnostic reports both
-- the written and canonical orders.
applyDeclarationModifier
  :: DeclarationModifier
  -> Expression
  -> Maybe Expression
applyDeclarationModifier modifier expressionValue = do
  declaration <- dependentDeclaration expressionValue
  let applications = dependentDeclarationModifierApplications declaration
        <> [modifier]
  pure (DeclarationExpression
    (withModifierApplications applications declaration))

invalidDependentDeclarationModifiers
  :: DependentDeclaration expression
  -> Maybe ([String], [String])
invalidDependentDeclarationModifiers declaration
  | dependentDeclarationIsValid declaration = Nothing
  | otherwise = Just
      ( map modifierName (reverse applications)
      , map modifierName (reverse (canonicalApplications applications))
      )
  where
    applications = dependentDeclarationModifierApplications declaration

withModifierApplications
  :: [DeclarationModifier]
  -> DependentDeclaration expression
  -> DependentDeclaration expression
withModifierApplications applications declaration = declaration
  { dependentDeclarationModifierApplications = applications }

canonicalApplications
  :: [DeclarationModifier]
  -> [DeclarationModifier]
canonicalApplications applications = filter (`elem` applications)
  [DeclarationVal, DeclarationDef, DeclarationLet]

modifierName :: DeclarationModifier -> String
modifierName = operatorCanonicalSymbol . declarationModifierOperator

dependentDeclarationCandidate :: Expression -> Bool
dependentDeclarationCandidate = maybe False (const True) . dependentDeclaration


dependentDeclarationNameExpression
  :: DependentDeclaration Expression
  -> Expression
dependentDeclarationNameExpression declaration =
  identifierExpressionExpression (dependentDeclarationHead declaration)

dependentDeclarationNameFamilyExpression
  :: DependentDeclaration Expression
  -> Expression
dependentDeclarationNameFamilyExpression =
  identifierHeadExpression . dependentDeclarationHead

identifierHeadExpression :: IdentifierExpression Expression -> Expression
identifierHeadExpression = identifierExpressionExpression

-- | Translate a declaration's complete name family by one literal prefix.
-- This is one operation for every dependent declaration: the cases below
-- only preserve the most precise AST encoding available for the translated
-- family.  In particular, prefixing is injective regardless of whether the
-- original family was a singleton identifier or a dependent template.
prependDependentDeclarationName
  :: String
  -> DependentDeclaration Expression
  -> DependentDeclaration Expression
prependDependentDeclarationName prefix declaration = declaration
  { dependentDeclarationHead = prependHead (dependentDeclarationHead declaration)
  }
  where
    prependHead
        (IdentifierExpressionBody
          (AsciiStringLiteral name)) =
      IdentifierExpressionBody (AsciiStringLiteral (prefix <> name))
    prependHead (IdentifierExpressionBody operand) = IdentifierExpressionBody
      (MapConcatenation (AsciiStringLiteral prefix) operand)

dependentDeclarationWithImplementation
  :: Expression
  -> DependentDeclaration Expression
  -> DependentDeclaration Expression
dependentDeclarationWithImplementation implementation declaration = declaration
  { dependentDeclarationImplementation = implementation }

-- Lexical binders include dependent arguments and parameters, not only
-- executable declarations. Keep name extraction independent of declaration
-- recognition so those concepts cannot silently widen one another.
bindingNames :: Expression -> [String]
bindingNames expressionValue = case expressionValue of
  DeclarationExpression declaration -> maybe []
    (pure . simpleIdentifierStringText)
    (literalIdentifierName (dependentDeclarationHead declaration))
  DependentArgument nameExpression _
    | Just (SimpleIdentifierString name) <-
        literalIdentifierName nameExpression -> [name]
  MapSpecification _ target -> bindingNames target
  OptionalType inner -> bindingNames inner
  _ -> []
