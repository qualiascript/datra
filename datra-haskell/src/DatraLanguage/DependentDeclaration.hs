-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , DependentDeclarationHead (..)
  , dependentDeclaration
  , dependentDeclarationCandidate
  , invalidDependentDeclarationModifiers
  , dependentDeclarationNameExpression
  , dependentDeclarationNameFamilyExpression
  , dependentDeclarationTemplateBranches
  , bindingNames
  ) where

import DatraLanguage.AST
import DatraLanguage.AST.Operator
  ( Operator (DefOperator, LetOperator, ValOperator)
  , operatorCanonicalSymbol
  )
import Data.List (nub, sort)

data DependentDeclarationHead
  = SimpleIdentifierDeclarationHead IdentifierString
  | StringTemplateDeclarationHead [StringTemplatePart Expression]
  | EvaluatedDeclarationHead Expression
  deriving (Eq, Show)

data DependentDeclaration = DependentDeclaration
  { dependentDeclarationHead :: DependentDeclarationHead
  , dependentDeclarationIsLet :: Bool
  , dependentDeclarationIsDefinition :: Bool
  , dependentDeclarationIsCanonicalValue :: Bool
  , dependentDeclarationImplementation :: Expression
  }

-- A declaration is an inferred assignment in block position. Identifier
-- annotations and dependent identifiers remain expressions until an explicit
-- assignment gives them a value.
dependentDeclaration :: Expression -> Maybe DependentDeclaration
dependentDeclaration = declaration False False False
  where
    declaration _ definition canonical (Let _)
      | definition || canonical = Nothing
    declaration _ definition canonical (Let value) =
      declaration True definition canonical value
    declaration _ _ canonical (Def _)
      | canonical = Nothing
    declaration strict False canonical (Def value) =
      declaration strict True canonical value
    declaration _ True _ (Def _) = Nothing
    declaration strict definition False (Val value) =
      declaration strict definition True value
    declaration _ _ True (Val _) = Nothing
    declaration strict definition canonical (SyntaxBoundary value) =
      declaration strict definition canonical value
    declaration strict definition canonical
        (IdentifierOperation (IdentifierString name) annotation (Just given))
      | annotation == given = Just (makeDeclaration
          (SimpleIdentifierDeclarationHead (IdentifierString name))
          strict definition canonical given)
    declaration strict definition canonical optional
      | Just (named@IdentifierOperation {}, _) <-
          optionalIdentifierExpression optional =
          declaration strict definition canonical named
    declaration strict definition canonical
        (IdentifierTemplateOperation parts annotation (Just given))
      | annotation == given = Just (makeDeclaration
          (classifyTemplateHead parts) strict definition canonical given)
    declaration _ _ _ _ = Nothing

    makeDeclaration headValue strict definition canonical implementation =
      DependentDeclaration
        headValue strict definition canonical implementation

    -- The parser carries a first-class declaration head through the existing
    -- identifier-template AST node as one explicitly bounded interpolation.
    -- Decode that carrier exactly once. From here on, evaluated heads and
    -- quoted string templates are distinct representations.
    classifyTemplateHead parts = case parts of
      [StringTemplateInterpolation expressionValue]
        | Just evaluated <- boundedHead expressionValue ->
            EvaluatedDeclarationHead evaluated
      _ -> StringTemplateDeclarationHead parts

    boundedHead (SyntaxBoundary expressionValue) =
      Just (stripBoundaries expressionValue)
    boundedHead _ = Nothing

    stripBoundaries (SyntaxBoundary expressionValue) =
      stripBoundaries expressionValue
    stripBoundaries expressionValue = expressionValue

-- Declaration modifiers are an ordered, duplicate-free subset of
-- @let def val@. Return both the written sequence and its unique canonical
-- ordering so every invalid combination can share one actionable diagnostic.
invalidDependentDeclarationModifiers
  :: Expression
  -> Maybe ([String], [String])
invalidDependentDeclarationModifiers expressionValue =
  case collect [] expressionValue of
    ([], _) -> Nothing
    (written, base)
      | written /= canonical
      , Just _ <- dependentDeclaration base -> Just
          (map modifierName written, map modifierName canonical)
      | otherwise -> Nothing
      where
        canonical = nub (sort written)
  where
    collect modifiers (SyntaxBoundary inner) = collect modifiers inner
    collect modifiers (Let inner) = collect (modifiers <> [ModifierLet]) inner
    collect modifiers (Def inner) = collect (modifiers <> [ModifierDef]) inner
    collect modifiers (Val inner) = collect (modifiers <> [ModifierVal]) inner
    collect modifiers base = (modifiers, base)

    modifierName = operatorCanonicalSymbol . modifierOperator
    modifierOperator ModifierLet = LetOperator
    modifierOperator ModifierDef = DefOperator
    modifierOperator ModifierVal = ValOperator

-- Syntax matching admits a declaration-shaped modifier chain before semantic
-- ordering is checked, so malformed chains remain intact for the single
-- modifier diagnostic instead of degrading into an unrelated application.
dependentDeclarationCandidate :: Expression -> Bool
dependentDeclarationCandidate expressionValue =
  maybe False (const True) (dependentDeclaration (stripModifiers expressionValue))
  where
    stripModifiers (SyntaxBoundary inner) = stripModifiers inner
    stripModifiers (Let inner) = stripModifiers inner
    stripModifiers (Def inner) = stripModifiers inner
    stripModifiers (Val inner) = stripModifiers inner
    stripModifiers base = base

data DeclarationModifier
  = ModifierLet
  | ModifierDef
  | ModifierVal
  deriving (Eq, Ord)


-- A syntax boundary on the sole interpolation marks an evaluated declaration
-- head, whether it was written with parentheses or formed by a tighter
-- operator such as an explicit template federation.  Ordinary quoted
-- templates retain their literal/interpolation structure.
dependentDeclarationNameExpression :: DependentDeclaration -> Expression
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
  :: DependentDeclaration
  -> Expression
dependentDeclarationNameFamilyExpression declaration =
  case dependentDeclarationHead declaration of
    SimpleIdentifierDeclarationHead (IdentifierString name) ->
      StringTemplate [StringTemplateLiteral name]
    StringTemplateDeclarationHead parts -> StringTemplate parts
    EvaluatedDeclarationHead expressionValue -> expressionValue

-- Explicit alternatives in an evaluated declaration head are still one
-- declaration family.  Each leaf is a complete string template; consumers
-- that operate on syntax structure use these branches while consumers that
-- need the written family expression use 'dependentDeclarationNameExpression'.
dependentDeclarationTemplateBranches
  :: DependentDeclaration
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

-- Lexical binders include dependent identifiers and parameters, not only
-- executable declarations. Keep name extraction independent of declaration
-- recognition so those concepts cannot silently widen one another.
bindingNames :: Expression -> [String]
bindingNames expressionValue = case expressionValue of
  IdentifierOperation (IdentifierString name) _ _ -> [name]
  IdentifierTemplateOperation [StringTemplateLiteral name] _ _ -> [name]
  OptionalType inner -> bindingNames inner
  Let inner -> bindingNames inner
  Def inner -> bindingNames inner
  Val inner -> bindingNames inner
  _ -> []
