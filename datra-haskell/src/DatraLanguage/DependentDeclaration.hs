-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , DependentDeclarationHead (..)
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
      Just (makeDeclaration
        (classifyHead name) given)
    declaration optional
      | Just (named, _) <-
          optionalIdentifierExpression optional =
          declaration named
    declaration _ = Nothing

    makeDeclaration headValue implementation =
      DependentDeclaration
        headValue False False False [] implementation

    classifyHead name = case name of
      IdentifierReference identifier -> SimpleIdentifierDeclarationHead identifier
      StringTemplate parts -> StringTemplateDeclarationHead parts
      expressionValue -> EvaluatedDeclarationHead
        (stripBoundaries expressionValue)

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


-- A syntax boundary on the sole interpolation marks an evaluated declaration
-- head, whether it was written with parentheses or formed by a tighter
-- operator such as an explicit template federation.  Ordinary quoted
-- templates retain their literal/interpolation structure.
dependentDeclarationNameExpression
  :: DependentDeclaration Expression
  -> Expression
dependentDeclarationNameExpression declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) ->
      IdentifierReference (IdentifierString name)
    StringTemplateDeclarationHead parts -> StringTemplate parts
    EvaluatedDeclarationHead expressionValue -> expressionValue

-- The federation of names introduced by a declaration is not always the
-- value of its written head. In particular, evaluating the written head of a
-- simple declaration resolves that identifier's payload. Represent its name
-- as the same singleton string-template family used by every other
-- declaration so overlap validation can uniformly use federation operations.
dependentDeclarationNameFamilyExpression
  :: DependentDeclaration Expression
  -> Expression
dependentDeclarationNameFamilyExpression declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) ->
      StringTemplate [StringTemplateLiteral name]
    StringTemplateDeclarationHead parts -> StringTemplate parts
    EvaluatedDeclarationHead expressionValue -> expressionValue

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
  { dependentDeclarationHead = prependHead
      (dependentDeclarationHead declaration)
  }
  where
    prependHead (SimpleIdentifierDeclarationHead (IdentifierString name)) =
      SimpleIdentifierDeclarationHead (IdentifierString (prefix <> name))
    prependHead headValue = EvaluatedDeclarationHead
      (MapConcatenation
        (AsciiStringLiteral prefix)
        (headExpression headValue))

    headExpression (SimpleIdentifierDeclarationHead (IdentifierString name)) =
      StringTemplate [StringTemplateLiteral name]
    headExpression (StringTemplateDeclarationHead parts) = StringTemplate parts
    headExpression (EvaluatedDeclarationHead expressionValue) =
      greedyName expressionValue

    greedyName value@AsciiStringLiteral {} = value
    greedyName value@StringTemplate {} = value
    greedyName value@GreedyStringTemplate {} = value
    greedyName value = GreedyStringTemplate value

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
  -> Maybe [[StringTemplatePart Expression]]
dependentDeclarationTemplateBranches declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) ->
      Just [[StringTemplateLiteral name]]
    StringTemplateDeclarationHead parts ->
      Just (expandOptionalInterpolations parts)
    EvaluatedDeclarationHead (GreedyStringTemplate operand) ->
      Just (greedyBranches operand)
    EvaluatedDeclarationHead expressionValue ->
      concatMap expandOptionalInterpolations <$> branches expressionValue
  where
    branches (SyntaxBoundary inner) = branches inner
    branches (EitherType left right) =
      (<>) <$> branches left <*> branches right
    branches (AsciiStringLiteral literal) =
      Just [[StringTemplateLiteral literal]]
    branches (StringTemplate parts) = Just [parts]
    branches _ = Nothing

    expandOptionalInterpolations [] = [[]]
    expandOptionalInterpolations (part : remaining) =
      [ selected <> suffix
      | selected <- alternatives part
      , suffix <- expandOptionalInterpolations remaining
      ]
    alternatives
        (StringTemplateInterpolation (OptionalType present)) =
      [ [StringTemplateInterpolation present]
      , []
      ]
    alternatives
        (StringTemplateInterpolation
          (SyntaxBoundary (OptionalType present))) =
      [ [StringTemplateInterpolation (SyntaxBoundary present)]
      , []
      ]
    alternatives part = [[part]]

    -- Within a greedy template, the ordinary sequence, either, and optional
    -- AST nodes describe template structure. Whitespace is structural: every
    -- pair of realized sequence components is separated by one canonical
    -- space, while an absent optional component contributes no stray space.
    greedyBranches (SyntaxBoundary inner) = greedyBranches inner
    greedyBranches (AtlasMap members) = greedySequence members
    greedyBranches (MapSequence members) = greedySequence members
    greedyBranches (EitherType left right) =
      greedyBranches left <> greedyBranches right
    greedyBranches (OptionalType present) = greedyBranches present <> [[]]
    greedyBranches (AsciiStringLiteral literal) =
      [[StringTemplateLiteral literal]]
    greedyBranches expressionValue =
      [[StringTemplateInterpolation expressionValue]]

    greedySequence = foldl combine [[]] . map greedyBranches
    combine prefixes suffixes =
      [ join prefix suffix
      | prefix <- prefixes
      , suffix <- suffixes
      ]
    join [] suffix = suffix
    join prefix [] = prefix
    join prefix suffix =
      prefix <> [StringTemplateLiteral " "] <> suffix

-- Lexical binders include dependent arguments and parameters, not only
-- executable declarations. Keep name extraction independent of declaration
-- recognition so those concepts cannot silently widen one another.
bindingNames :: Expression -> [String]
bindingNames expressionValue = case expressionValue of
  DeclarationExpression declaration -> case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) -> [name]
    StringTemplateDeclarationHead [StringTemplateLiteral name] -> [name]
    _ -> []
  DependentArgument (IdentifierReference (IdentifierString name)) _ -> [name]
  DependentArgument (StringTemplate [StringTemplateLiteral name]) _ -> [name]
  MapSpecification _ target -> bindingNames target
  OptionalType inner -> bindingNames inner
  _ -> []
