-- | Whole-template validation against the declaration-independent parser and
-- the same structural projection used by runtime syntax rewriting.
module SyntaxTemplateAdmissibility
  ( validateSyntaxTemplate
  ) where

import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , expressionChildren
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
  ( freshNeutralWitnessIdentifiers
  , neutralExpressionWitnessSources
  , neutralIncompletePrefixOperator
  , parseNeutralPhrase
  )
import SyntaxTemplateProjection (projectSyntaxTemplate)

data Witness = Witness
  { witnessSource :: String
  , witnessMarker :: String
  }

validateSyntaxTemplate
  :: SyntaxTemplate Expression
  -> Either SyntaxTemplateAdmissibilityFailure ()
validateSyntaxTemplate template =
  traverse_ validateWitness (templateWitnesses template)
  where
    validateWitness witnesses = do
      expected <- traverse expectedWitness witnesses
      let source = renderWitness template witnesses
          markers = map witnessMarker witnesses
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
          | otherwise -> Left SyntaxTemplateProjectionOrderMismatch
        Nothing
          | markerOrder markers parsed == markers ->
              Left SyntaxTemplateProjectionLoss
          | otherwise -> Left SyntaxTemplateProjectionOrderMismatch
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
    identifiers = take (holeCount * 2)
      (freshNeutralWitnessIdentifiers literals)
    markers = take holeCount identifiers
    auxiliaries = take holeCount (drop holeCount identifiers)
    bases = zipWith3 atomicWitness holes markers auxiliaries
    atomic = bases
    variants =
      [ replace position witness bases
      | (position, ((kind, needsGrouping), marker, auxiliary)) <-
          zip [0 :: Int ..] (zip3 holes markers auxiliaries)
      , generalExpressionHole kind
      , source <- drop 1
          (neutralExpressionWitnessSources marker auxiliary)
      , let embeddedSource
              | needsGrouping = groupedSource source
              | otherwise = source
            witness = Witness embeddedSource marker
      ]

    atomicWitness (kind, _) marker auxiliary = Witness
      (renderSourceExpression (witnessExpression kind marker auxiliary))
      marker
    witnessExpression kind marker auxiliary = case kind of
      BlockSyntaxHole {} -> AtlasMap
        [identifier auxiliary, identifier marker]
      FunctionBodySyntaxHole {} -> AtlasMap
        [ FunctionBody [identifier auxiliary] (identifier marker)
        , AtlasMap []
        ]
      _ -> identifier marker
    identifier = IdentifierReference . IdentifierString
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
    literals = [literal | SyntaxLiteral literal <- syntaxTemplatePieces template]

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

markerOrder :: [String] -> Expression -> [String]
markerOrder markers = collect
  where
    collect expressionValue = current
      <> concatMap collect (expressionChildren expressionValue)
      where
        current = case expressionValue of
          IdentifierReference (IdentifierString name)
            | name `elem` markers -> [name]
          _ -> []

traverse_ :: (value -> Either failure ()) -> [value] -> Either failure ()
traverse_ _ [] = Right ()
traverse_ action (value : remaining) =
  action value >> traverse_ action remaining
