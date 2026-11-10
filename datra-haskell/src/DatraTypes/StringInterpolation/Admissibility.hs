-- | Whole-template validation against the declaration-independent parser and
-- the same structural projection used by runtime syntax rewriting.
module StringInterpolation.Admissibility
  ( validateStringInterpolation
  , validateStringTemplate
  , stringInterpolationRefines
  , stringInterpolationsOverlap
  ) where

import DatraLanguage.AST
  ( Expression (..)
  , StringTemplatePart (..)
  , normalizeExpression
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Diagnostics.Application
  ( StringInterpolationAdmissibilityFailure (..)
  )
import DatraLanguage.StringExpression
  ( StringExpression (..)
  , StringInterpolationTemplate
  )
import StringInterpolation.Projection
  ( StringInterpolationParser (..)
  , projectStringInterpolation
  )

newtype Witness = Witness
  { witnessSource :: String
  }

validateStringInterpolation
  :: StringInterpolationParser
  -> StringInterpolationTemplate Expression
  -> Either StringInterpolationAdmissibilityFailure ()
validateStringInterpolation parser template =
  validateStringInterpolationWith parser (renderWitness template) template

-- | Validate a declaration template using the source spelling which actually
-- produced it.  Quoted templates concatenate their literal chunks exactly;
-- greedy templates reach this function after lowering has inserted their
-- canonical single-space separators.  Keeping source rendering here separate
-- from the whitespace-delimited matcher prevents validation from silently
-- changing an exact quoted template with 'unwords'.
validateStringTemplate
  :: StringInterpolationParser
  -> [StringTemplatePart Expression]
  -> StringInterpolationTemplate Expression
  -> Either StringInterpolationAdmissibilityFailure ()
validateStringTemplate parser parts =
  validateStringInterpolationWith parser (renderParts parts)

validateStringInterpolationWith
  :: StringInterpolationParser
  -> ([Witness] -> String)
  -> StringInterpolationTemplate Expression
  -> Either StringInterpolationAdmissibilityFailure ()
validateStringInterpolationWith parser render template =
  traverse_ validateWitness (templateWitnesses parser template)
  where
    validateWitness witnesses = do
      expected <- traverse expectedWitness witnesses
      let source = render witnesses
          capture _ value
            | normalizeExpression value `elem` expected =
                Just (normalizeExpression value)
            | otherwise = Nothing
      parsed <- maybe
        (Left (neutralParseFailure source))
        Right
        (parseStringInterpolationExpression parser source)
      recovered <- case
          projectStringInterpolation parser capture template parsed of
        Just captures
          | map normalizeExpression captures == expected -> Right expected
          | otherwise -> Left StringInterpolationProjectionLoss
        Nothing -> Left StringInterpolationProjectionLoss
      let canonical = renderSourceExpression parsed
      reparsed <- maybe
        (Left UnstableStringInterpolationProjection)
        Right
        (parseStringInterpolationExpression parser canonical)
      case projectStringInterpolation parser capture template reparsed of
        Just second | second == recovered -> Right ()
        _ -> Left UnstableStringInterpolationProjection
    expectedWitness witness = maybe
      (Left (neutralParseFailure (witnessSource witness)))
      (Right . normalizeExpression)
      (parseStringInterpolationExpression parser (witnessSource witness))
    neutralParseFailure source = case
        incompleteStringInterpolationPrefixOperator parser source of
      Just operator -> IncompleteCoreSyntaxOperator operator
      Nothing -> NeutralStringInterpolationParseFailure

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

-- | Structural inclusion between two string-interpolation federations.  The
-- source template is rendered with the same neutral witnesses used by
-- admissibility, then projected through the target.  A target expression hole
-- may absorb a larger admissible source fragment; aligned holes delegate their
-- value-family relation to the caller.
stringInterpolationRefines
  :: StringInterpolationParser
  -> (StringExpression Expression -> StringExpression Expression -> Bool)
  -> StringInterpolationTemplate Expression
  -> StringInterpolationTemplate Expression
  -> Bool
stringInterpolationRefines parser holeRefines source target =
  all refinesWitness (templateWitnesses parser source)
  where
    sourceKinds =
      [ kind
      | StringTemplateInterpolation kind <- source
      ]
    refinesWitness witnesses =
      case parseStringInterpolationExpression parser
          (renderWitness source witnesses) of
        Nothing -> False
        Just parsed ->
          case projectStringInterpolation parser
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
          ExpressionString {} -> Just captured
          _ -> Nothing
    exactSourceHole witnesses captured = firstExact
      [ (witness, kind)
      | (witness, kind) <- zip witnesses sourceKinds
      ]
      where
        normalized = normalizeExpression captured
        firstExact [] = Nothing
        firstExact ((witness, kind) : remaining) =
          case parseStringInterpolationExpression parser
              (witnessSource witness) of
            Just expected
              | normalizeExpression expected == normalized -> Just kind
            _ -> firstExact remaining

-- | Whether two string-interpolation families have any structural member in
-- common. Witnesses are projected in both directions because either template
-- may provide the literal structure absorbed by an expression hole in the
-- other. Aligned typed holes delegate federation intersection to the caller.
stringInterpolationsOverlap
  :: StringInterpolationParser
  -> (StringExpression Expression -> StringExpression Expression -> Bool)
  -> StringInterpolationTemplate Expression
  -> StringInterpolationTemplate Expression
  -> Bool
stringInterpolationsOverlap parser holeOverlaps left right =
  any (projects left right) (templateWitnesses parser left)
    || any (projects right left) (templateWitnesses parser right)
  where
    projects source target witnesses =
      case parseStringInterpolationExpression parser
          (renderWitness source witnesses) of
        Nothing -> False
        Just parsed -> case projectStringInterpolation parser
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
          ExpressionString {} -> Just captured
          _ -> Nothing

    exactSourceHole source witnesses captured = firstExact
      [ (witness, kind)
      | (witness, kind) <- zip witnesses
          [ kind
          | StringTemplateInterpolation kind <- source
          ]
      ]
      where
        normalized = normalizeExpression captured
        firstExact [] = Nothing
        firstExact ((witness, kind) : remaining) =
          case parseStringInterpolationExpression parser
              (witnessSource witness) of
            Just expected
              | normalizeExpression expected == normalized -> Just kind
            _ -> firstExact remaining

templateWitnesses
  :: StringInterpolationParser
  -> StringInterpolationTemplate Expression
  -> [[Witness]]
templateWitnesses parser template = atomic : variants
  where
    holeCount = length
      [() | StringTemplateInterpolation {} <- template]
    holes =
      [ ( kind
        , not (null remaining)
            || any isHole preceding
        )
      | (preceding, StringTemplateInterpolation kind, remaining) <- pieceContexts
      ]
    pieceContexts = contexts [] template
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
          (stringInterpolationExpressionWitnesses parser
            (renderSourceExpression marker)
            (renderSourceExpression auxiliary))
      , let embeddedSource
              | needsGrouping = groupedSource source
              | otherwise = source
            witness = Witness embeddedSource
      ]

    atomicWitness _ marker _ = Witness (renderSourceExpression marker)
    groupedSource source = case
        parseStringInterpolationExpression parser source of
      Just expressionValue -> renderSourceExpression
        (MapSequence [expressionValue])
      Nothing -> source
    replace position replacement values =
      take position values <> [replacement] <> drop (position + 1) values
    generalExpressionHole ExpressionString {} = True
    generalExpressionHole _ = False
    isHole StringTemplateInterpolation {} = True
    isHole _ = False
    literalValues =
      [ normalizeExpression parsed
      | StringTemplateLiteral literal <- template
      , Just parsed <- [parseStringInterpolationExpression parser literal]
      ]

contexts :: [value] -> [value] -> [([value], value, [value])]
contexts _ [] = []
contexts reversed (value : remaining) =
  (reverse reversed, value, remaining)
    : contexts (value : reversed) remaining

renderWitness :: StringInterpolationTemplate value -> [Witness] -> String
renderWitness pieces witnesses =
  unwords (go pieces witnesses)
  where
    go [] _ = []
    go (StringTemplateLiteral literal : remaining) available =
      literal : go remaining available
    go (StringTemplateInterpolation {} : remaining) (witness : available) =
      witnessSource witness : go remaining available
    go (StringTemplateInterpolation {} : _) [] = []

traverse_ :: (value -> Either failure ()) -> [value] -> Either failure ()
traverse_ _ [] = Right ()
traverse_ action (value : remaining) =
  action value >> traverse_ action remaining
