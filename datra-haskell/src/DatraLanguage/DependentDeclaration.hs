-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , DeclarationModifier (..)
  , dependentDeclaration
  , dependentDeclarationCandidate
  , applyDeclarationModifier
  , removeDeclarationModifier
  , invalidDependentDeclarationModifiers
  , dependentDeclarationNameExpression
  , dependentDeclarationNameFamilyExpression
  , prependDependentDeclarationName
  , dependentDeclarationWithImplementation
  , dependentDeclarationTemplateBranches
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
      makeDeclaration <$> normalizeHead name <*> pure given
    declaration optional
      | Just (named, _) <-
          optionalIdentifierExpression optional =
          declaration named
    declaration _ = Nothing

    makeDeclaration headValue implementation =
      DependentDeclaration
        headValue False False False [] implementation

    normalizeHead name = case stripBoundaries name of
      IdentifierReference identifier ->
        Just (IdentifierExpressionBody (IdentifierReference identifier))
      IdentifierExpression body -> Just (IdentifierExpressionBody body)
      AtlasIdentifierExpression body ->
        Just (AtlasIdentifierExpressionBody body)
      _ -> Nothing

    stripBoundaries (SyntaxBoundary expressionValue) =
      stripBoundaries expressionValue
    stripBoundaries expressionValue = expressionValue

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

-- | Inverse used by syntax-function reconstruction. Only the outermost
-- application can be removed, preserving exact modifier history.
removeDeclarationModifier
  :: DeclarationModifier
  -> Expression
  -> Maybe [Expression]
removeDeclarationModifier modifier expressionValue = do
  declaration <- dependentDeclaration expressionValue
  case reverse (dependentDeclarationModifierApplications declaration) of
    outermost : remaining
      | outermost == modifier -> pure
          [ DeclarationExpression
              (withModifierApplications (reverse remaining) declaration) ]
    _ -> Nothing

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
  { dependentDeclarationIsLet = DeclarationLet `elem` applications
  , dependentDeclarationIsDefinition = DeclarationDef `elem` applications
  , dependentDeclarationIsCanonicalValue = DeclarationVal `elem` applications
  , dependentDeclarationModifierApplications = applications
  }

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
dependentDeclarationNameExpression =
  identifierHeadBody . dependentDeclarationHead

dependentDeclarationNameFamilyExpression
  :: DependentDeclaration Expression
  -> Expression
dependentDeclarationNameFamilyExpression =
  identifierHeadExpression . dependentDeclarationHead

identifierHeadBody :: IdentifierExpression expression -> expression
identifierHeadBody headValue = case headValue of
  IdentifierExpressionBody body -> body
  AtlasIdentifierExpressionBody body -> body

identifierHeadExpression :: IdentifierExpression Expression -> Expression
identifierHeadExpression headValue = case headValue of
  IdentifierExpressionBody body -> IdentifierExpression body
  AtlasIdentifierExpressionBody body -> AtlasIdentifierExpression body

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
          (IdentifierReference (SimpleIdentifierString name))) =
      IdentifierExpressionBody (AsciiStringLiteral (prefix <> name))
    prependHead (IdentifierExpressionBody operand) = IdentifierExpressionBody
      (MapConcatenation (AsciiStringLiteral prefix) operand)
    prependHead (AtlasIdentifierExpressionBody operand) =
      IdentifierExpressionBody
        (MapConcatenation
          (AsciiStringLiteral prefix)
          (AtlasIdentifierExpression operand))

dependentDeclarationWithImplementation
  :: Expression
  -> DependentDeclaration Expression
  -> DependentDeclaration Expression
dependentDeclarationWithImplementation implementation declaration = declaration
  { dependentDeclarationImplementation = implementation }

-- Explicit alternatives in an evaluated declaration head are still one
-- declaration family.  Each leaf is a complete string template; consumers
-- that operate on syntax structure use these branches while consumers that
-- need the written family expression use 'dependentDeclarationNameExpression'.
dependentDeclarationTemplateBranches
  :: DependentDeclaration Expression
  -> Maybe [[StringTemplateInterpolation Expression]]
dependentDeclarationTemplateBranches declaration = Just $ case
    identifierHeadBody (dependentDeclarationHead declaration) of
  IdentifierReference (SimpleIdentifierString name) ->
    [[stringLiteral name]]
  AsciiStringLiteral name ->
    [[stringLiteral name]]
  body -> identifierBranches body
  where
    -- Within an identifier expression, ordinary sequence, either, and optional
    -- AST nodes describe template structure. Whitespace is structural: every
    -- pair of realized sequence components is separated by one canonical
    -- space, while an absent optional component contributes no stray space.
    identifierBranches (SyntaxBoundary inner) = identifierBranches inner
    identifierBranches (AtlasMap members) = identifierSequence members
    identifierBranches (MapSequence members) = identifierSequence members
    identifierBranches (EitherType left right) =
      identifierBranches left <> identifierBranches right
    identifierBranches (OptionalType present) =
      identifierBranches present <> [[]]
    identifierBranches identifier@(IdentifierExpression expressionValue) =
      case expressionValue of
        IdentifierReference (SimpleIdentifierString literal) ->
          [[stringLiteral literal]]
        AsciiStringLiteral literal ->
          [[stringLiteral literal]]
        _ -> [[StringTemplateInterpolation identifier]]
    identifierBranches identifier@AtlasIdentifierExpression {} =
      [[StringTemplateInterpolation identifier]]
    identifierBranches expressionValue =
      [[StringTemplateInterpolation expressionValue]]

    identifierSequence = foldl combine [[]] . map identifierBranches
    combine prefixes suffixes =
      [ join prefix suffix
      | prefix <- prefixes
      , suffix <- suffixes
      ]
    join [] suffix = suffix
    join prefix [] = prefix
    join prefix suffix =
      prefix <> [stringLiteral " "] <> suffix
    stringLiteral = StringTemplateInterpolation . AsciiStringLiteral

-- Lexical binders include dependent arguments and parameters, not only
-- executable declarations. Keep name extraction independent of declaration
-- recognition so those concepts cannot silently widen one another.
bindingNames :: Expression -> [String]
bindingNames expressionValue = case expressionValue of
  DeclarationExpression declaration -> case dependentDeclarationHead declaration of
    IdentifierExpressionBody (IdentifierReference (SimpleIdentifierString name)) -> [name]
    IdentifierExpressionBody (AsciiStringLiteral name) -> [name]
    _ -> []
  DependentArgument (IdentifierReference (SimpleIdentifierString name)) _ -> [name]
  DependentArgument
      (StringTemplate
        [StringTemplateInterpolation (AsciiStringLiteral name)]) _ -> [name]
  MapSpecification _ target -> bindingNames target
  OptionalType inner -> bindingNames inner
  _ -> []
