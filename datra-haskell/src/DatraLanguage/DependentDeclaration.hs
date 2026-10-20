-- | The single semantic view of declarations used by syntax rewriting,
-- evaluation, and AST-category capture.
module DatraLanguage.DependentDeclaration
  ( DependentDeclaration (..)
  , DependentDeclarationHead (..)
  , dependentDeclaration
  , dependentDeclarationNameExpression
  , dependentDeclarationTemplateBranches
  , bindingNames
  ) where

import DatraLanguage.AST

data DependentDeclarationHead
  = StringTemplateDeclarationHead [StringTemplatePart Expression]
  | EvaluatedDeclarationHead Expression
  deriving (Eq, Show)

data DependentDeclaration = DependentDeclaration
  { dependentDeclarationHead :: DependentDeclarationHead
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
    declaration strict canonical (SyntaxBoundary value) =
      declaration strict canonical value
    declaration strict canonical
        (IdentifierOperation (IdentifierString name) annotation (Just given))
      | annotation == given = Just (makeDeclaration
          (StringTemplateDeclarationHead [StringTemplateLiteral name])
          strict canonical given)
    declaration strict canonical optional
      | Just (named@IdentifierOperation {}, _) <-
          optionalIdentifierExpression optional =
          declaration strict canonical named
    declaration strict canonical
        (IdentifierTemplateOperation parts annotation (Just given))
      | annotation == given = Just (makeDeclaration
          (classifyTemplateHead parts) strict canonical given)
    declaration _ _ _ = Nothing

    makeDeclaration headValue strict canonical implementation =
      DependentDeclaration headValue strict canonical implementation

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


-- A syntax boundary on the sole interpolation marks an evaluated declaration
-- head, whether it was written with parentheses or formed by a tighter
-- operator such as an explicit template federation.  Ordinary quoted
-- templates retain their literal/interpolation structure.
dependentDeclarationNameExpression :: DependentDeclaration -> Expression
dependentDeclarationNameExpression declaration =
  case dependentDeclarationHead declaration of
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
  Val inner -> bindingNames inner
  _ -> []
