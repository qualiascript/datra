-- | Whole-template validation against the declaration-independent parser and
-- the same structural projection used by runtime syntax rewriting.
module SyntaxTemplateAdmissibility
  ( validateSyntaxTemplate
  , validateStringTemplate
  , syntaxTemplateRefines
  , syntaxTemplatesOverlap
  ) where

import DatraLanguage.AST
  ( Expression (..)
  , StringTemplatePart (..)
  , normalizeExpression
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Diagnostics.Application
  ( SyntaxTemplateAdmissibilityFailure (..)
  )
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import Parsing
  ( neutralExpressionWitnessSources
  , neutralIncompletePrefixOperator
  , parseNeutralPhrase
  )
import SyntaxTemplateProjection (projectSyntaxTemplate)

newtype Witness = Witness
  { witnessSource :: String
  }

validateSyntaxTemplate
  :: SyntaxTemplate Expression
  -> Either SyntaxTemplateAdmissibilityFailure ()
validateSyntaxTemplate template =
  validateSyntaxTemplateWith (renderWitness template) template

-- | Validate a declaration template using the source spelling which actually
-- produced it.  Quoted templates concatenate their literal chunks exactly;
-- greedy templates reach this function after lowering has inserted their
-- canonical single-space separators.  Keeping source rendering here separate
-- from the whitespace-delimited matcher prevents validation from silently
-- changing an exact quoted template with 'unwords'.
validateStringTemplate
  :: [StringTemplatePart Expression]
  -> SyntaxTemplate Expression
  -> Either SyntaxTemplateAdmissibilityFailure ()
validateStringTemplate parts = validateSyntaxTemplateWith (renderParts parts)

validateSyntaxTemplateWith
  :: ([Witness] -> String)
  -> SyntaxTemplate Expression
  -> Either SyntaxTemplateAdmissibilityFailure ()
validateSyntaxTemplateWith render template =
  traverse_ validateWitness (templateWitnesses template)
  where
    validateWitness witnesses = do
      expected <- traverse expectedWitness witnesses
      let source = render witnesses
          capture _ value
            | normalizeExpression value `elem` expected =
                Just (normalizeExpression value)
            | otherwise = Nothing
      parsed <- either
        (const (Left (neutralParseFailure source)))
        Right
        (parseNeutralPhrase source)
      recovered <- case projectSyntaxTemplate capture template parsed of
        Just captures
          | map normalizeExpression captures == expected -> Right expected
          | otherwise -> Left SyntaxTemplateProjectionLoss
        Nothing -> Left SyntaxTemplateProjectionLoss
      let canonical = renderSourceExpression parsed
      reparsed <- either
        (const (Left UnstableSyntaxTemplateProjection))
        Right
        (parseNeutralPhrase canonical)
      case projectSyntaxTemplate capture template reparsed of
        Just second | second == recovered -> Right ()
        _ -> Left UnstableSyntaxTemplateProjection
    expectedWitness witness = either
      (const (Left (neutralParseFailure (witnessSource witness))))
      (Right . normalizeExpression)
      (parseNeutralPhrase (witnessSource witness))
    neutralParseFailure source = case
        neutralIncompletePrefixOperator source of
      Just operator -> IncompleteCoreSyntaxOperator operator
      Nothing -> NeutralSyntaxTemplateParseFailure

renderParts
  :: [StringTemplatePart Expression]
  -> [Witness]
  -> String
renderParts [] _ = ""
renderParts (StringTemplateLiteral literal : remaining) witnesses =
  literal <> renderParts remaining witnesses
renderParts (StringTemplateInterpolation {} : remaining)
    (witness : witnesses) =
  witnessSource witness <> renderParts remaining witnesses
renderParts (StringTemplateInterpolation {} : _) [] = ""

-- | Structural inclusion between two syntax-template federations.  The
-- source template is rendered with the same neutral witnesses used by
-- admissibility, then projected through the target.  A target expression hole
-- may absorb a larger admissible source fragment; aligned holes delegate their
-- value-family relation to the caller.
syntaxTemplateRefines
  :: (SyntaxHoleKind Expression -> SyntaxHoleKind Expression -> Bool)
  -> SyntaxTemplate Expression
  -> SyntaxTemplate Expression
  -> Bool
syntaxTemplateRefines holeRefines source target =
  all refinesWitness (templateWitnesses source)
  where
    sourceKinds =
      [ kind
      | SyntaxHole kind <- syntaxTemplatePieces source
      ]
    refinesWitness witnesses =
      case parseNeutralPhrase (renderWitness source witnesses) of
        Left _ -> False
        Right parsed ->
          case projectSyntaxTemplate
              (capture witnesses)
              target
              parsed of
            Just _ -> True
            Nothing -> False
    capture witnesses targetKind captured =
      case exactSourceHole witnesses captured of
        Just sourceKind
          | holeRefines sourceKind targetKind -> Just captured
          | otherwise -> Nothing
        Nothing -> case targetKind of
          ExpressionSyntaxHole {} -> Just captured
          _ -> Nothing
    exactSourceHole witnesses captured = firstExact
      [ (witness, kind)
      | (witness, kind) <- zip witnesses sourceKinds
      ]
      where
        normalized = normalizeExpression captured
        firstExact [] = Nothing
        firstExact ((witness, kind) : remaining) =
          case parseNeutralPhrase (witnessSource witness) of
            Right expected
              | normalizeExpression expected == normalized -> Just kind
            _ -> firstExact remaining

-- | Whether two syntax-template families have any structural member in
-- common. Witnesses are projected in both directions because either template
-- may provide the literal structure absorbed by an expression hole in the
-- other. Aligned typed holes delegate federation intersection to the caller.
syntaxTemplatesOverlap
  :: (SyntaxHoleKind Expression -> SyntaxHoleKind Expression -> Bool)
  -> SyntaxTemplate Expression
  -> SyntaxTemplate Expression
  -> Bool
syntaxTemplatesOverlap holeOverlaps left right =
  any (projects left right) (templateWitnesses left)
    || any (projects right left) (templateWitnesses right)
  where
    projects source target witnesses =
      case parseNeutralPhrase (renderWitness source witnesses) of
        Left _ -> False
        Right parsed -> case projectSyntaxTemplate
            (capture source witnesses)
            target
            parsed of
          Just _ -> True
          Nothing -> False

    capture source witnesses targetKind captured =
      case exactSourceHole source witnesses captured of
        Just sourceKind ->
          if holeOverlaps sourceKind targetKind
            then Just captured
            else Nothing
        Nothing -> case targetKind of
          ExpressionSyntaxHole {} -> Just captured
          _ -> Nothing

    exactSourceHole source witnesses captured = firstExact
      [ (witness, kind)
      | (witness, kind) <- zip witnesses
          [ kind
          | SyntaxHole kind <- syntaxTemplatePieces source
          ]
      ]
      where
        normalized = normalizeExpression captured
        firstExact [] = Nothing
        firstExact ((witness, kind) : remaining) =
          case parseNeutralPhrase (witnessSource witness) of
            Right expected
              | normalizeExpression expected == normalized -> Just kind
            _ -> firstExact remaining

templateWitnesses :: SyntaxTemplate Expression -> [[Witness]]
templateWitnesses template = atomic : variants
  where
    holeCount = length
      [() | SyntaxHole {} <- syntaxTemplatePieces template]
    holes =
      [ ( kind
        , not (null remaining)
            || any isHole preceding
        )
      | (preceding, SyntaxHole kind, remaining) <- pieceContexts
      ]
    pieceContexts = contexts [] (syntaxTemplatePieces template)
    neutralValues =
      [ EllipsisNatural value
      | value <- [0 ..]
      , EllipsisNatural value `notElem` literalValues
      ]
    markers = take holeCount neutralValues
    auxiliaries = take holeCount (drop holeCount neutralValues)
    bases = zipWith3 atomicWitness holes markers auxiliaries
    atomic = bases
    variants =
      [ replace position witness bases
      | (position, ((kind, needsGrouping), marker, auxiliary)) <-
          zip [0 :: Int ..] (zip3 holes markers auxiliaries)
      , generalExpressionHole kind
      , source <- drop 1
          (neutralExpressionWitnessSources
            (renderSourceExpression marker)
            (renderSourceExpression auxiliary))
      , let embeddedSource
              | needsGrouping = groupedSource source
              | otherwise = source
            witness = Witness embeddedSource
      ]

    atomicWitness _ marker _ = Witness (renderSourceExpression marker)
    groupedSource source = case parseNeutralPhrase source of
      Right expressionValue -> renderSourceExpression
        (MapSequence [expressionValue])
      Left _ -> source
    replace position replacement values =
      take position values <> [replacement] <> drop (position + 1) values
    generalExpressionHole ExpressionSyntaxHole {} = True
    generalExpressionHole _ = False
    isHole SyntaxHole {} = True
    isHole _ = False
    literalValues =
      [ normalizeExpression parsed
      | SyntaxLiteral literal <- syntaxTemplatePieces template
      , Right parsed <- [parseNeutralPhrase literal]
      ]

contexts :: [value] -> [value] -> [([value], value, [value])]
contexts _ [] = []
contexts reversed (value : remaining) =
  (reverse reversed, value, remaining)
    : contexts (value : reversed) remaining

renderWitness :: SyntaxTemplate value -> [Witness] -> String
renderWitness (SyntaxTemplate pieces) witnesses =
  unwords (go pieces witnesses)
  where
    go [] _ = []
    go (SyntaxLiteral literal : remaining) available =
      literal : go remaining available
    go (SyntaxHole {} : remaining) (witness : available) =
      witnessSource witness : go remaining available
    go (SyntaxHole {} : _) [] = []

traverse_ :: (value -> Either failure ()) -> [value] -> Either failure ()
traverse_ _ [] = Right ()
traverse_ action (value : remaining) =
  action value >> traverse_ action remaining
