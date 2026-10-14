-- | Shared projection from the neutral AST into the application-shaped view
-- consumed by declarative syntax matching. Both runtime rewriting and
-- syntax-template admissibility use this module, so parser boundary behavior
-- cannot drift between them.
module SyntaxTemplateProjection
  ( syntaxProjectionCandidates
  , projectSyntaxTemplate
  , applicationPhrase
  , applicationSpine
  , applicationFrom
  , applicationFromMaybe
  , literalExpression
  , matchesLiteral
  , leftInfixContext
  , rightInfixContext
  , directApplicationSplit
  , stripTrailingLiteralAssignment
  ) where

import Data.Set qualified as Set
import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  , traverseExpressionChildren
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )

type CaptureHole = SyntaxHoleKind Expression -> Expression -> Maybe Expression

-- | Recover a complete template from one neutral expression. The result is
-- the captures in template order; partial application-prefix matches are not
-- accepted at this validation boundary.
projectSyntaxTemplate
  :: CaptureHole
  -> SyntaxTemplate Expression
  -> Expression
  -> Maybe [Expression]
projectSyntaxTemplate capture template expressionValue = firstJust
  [ captures
  | candidate <- syntaxProjectionCandidates True template expressionValue
  , captures <- matchPieces []
      (syntaxTemplatePieces template)
      (applicationPhrase candidate)
  ]
  where
    matchPieces captures [] [] = [reverse captures]
    matchPieces _ [] _ = []
    matchPieces captures (SyntaxLiteral literal : pieces) (value : values)
      | matchesLiteralExpression literal value =
          matchPieces captures pieces values
    matchPieces _ (SyntaxLiteral _ : _) _ = []
    matchPieces captures (SyntaxHole kind : pieces) values =
      [ result
      | count <- reverse [1 .. maximumCaptureLength pieces values]
      , let (captured, remaining) = splitAt count values
      , selected <- maybeToList (capture kind (applicationFrom captured))
      , result <- matchPieces (selected : captures) pieces remaining
      ]

    maximumCaptureLength remaining values =
      max 0 (length values - length remaining)
    firstJust [] = Nothing
    firstJust (value : _) = Just value

syntaxProjectionCandidates
  :: Bool
  -> SyntaxTemplate Expression
  -> Expression
  -> [Expression]
syntaxProjectionCandidates includeConcatenation template value =
  concatenation <> ordinary
  where
    concatenation
      | includeConcatenation =
          concatenationBoundaryCandidates template value
            <> literalConcatenationBoundaryCandidates template value
      | otherwise = []
    (deepSeeds, initialSeen) = uniqueExpressions
      (Set.singleton value)
      (oneDescendantCandidates directCandidates value)
    initial = value : deepSeeds
    ordinary = initial
      <> terminalExpressionBoundaries
      <> contextualClosure initialSeen initial

    -- Function type, syntax type, and concatenation are complete-expression
    -- boundaries. A template whose only hole is its final expression may move
    -- such a boundary into that hole, but the result is already in the exact
    -- application shape the matcher consumes. Feeding it back into the
    -- generic contextual closure creates exponentially many equivalent trees
    -- for nested maps and signatures.
    terminalExpressionBoundaries =
      terminalExpressionBoundaryCandidates template value

    contextualClosure _ [] = []
    contextualClosure seen frontier =
      let (fresh, nextSeen) = uniqueExpressions seen
            (concatMap contextualStep frontier)
      in fresh <> contextualClosure nextSeen fresh

    contextualStep current = directCandidates current
      <> oneChildCandidates directCandidates current
    directCandidates current =
      signedArgumentCandidates template current
        <> declarationBoundaryCandidates current
        <> rightApplicationCandidates current
        <> leftBoundaryCandidates template current
        <> rightBoundaryCandidates current

-- Preserve the candidate priority used by matching while making membership
-- logarithmic. The former @nub@ plus @notElem@ worklist repeatedly compared
-- whole ASTs and became quadratic on even modest nested expressions.
uniqueExpressions
  :: Set.Set Expression
  -> [Expression]
  -> ([Expression], Set.Set Expression)
uniqueExpressions initialSeen values =
  let (reversed, seen) = foldl' include ([], initialSeen) values
  in (reverse reversed, seen)
  where
    include result@(_, seen) value
      | Set.member value seen = result
    include (reversed, seen) value =
      (value : reversed, Set.insert value seen)

data OneChild a = OneChild a [a]

instance Functor OneChild where
  fmap function (OneChild original changed) =
    OneChild (function original) (map function changed)

instance Applicative OneChild where
  pure value = OneChild value []
  OneChild originalFunction changedFunctions
      <*> OneChild originalValue changedValues =
    OneChild
      (originalFunction originalValue)
      (map ($ originalValue) changedFunctions
        <> map originalFunction changedValues)

oneChildCandidates
  :: (Expression -> [Expression])
  -> Expression
  -> [Expression]
oneChildCandidates candidates value = changed
  where
    OneChild _ changed = traverseExpressionChildren
      (\child -> OneChild child (candidates child)) value

oneDescendantCandidates
  :: (Expression -> [Expression])
  -> Expression
  -> [Expression]
oneDescendantCandidates candidates = descend
  where
    descend value = oneChildCandidates
      (\child -> candidates child <> descend child) value

rightApplicationCandidates :: Expression -> [Expression]
rightApplicationCandidates value = case value of
  FunctionApplication function argument@FunctionApplication {} ->
    [applicationFrom
      (applicationPhrase function <> applicationPhrase argument)]
  _ -> []

signedArgumentCandidates
  :: SyntaxTemplate Expression
  -> Expression
  -> [Expression]
signedArgumentCandidates template value = binarySign <> embeddedSigns
  where
    binarySign = case value of
      Addition left right -> withSign Plus left right
      Subtraction left right -> withSign Minus left right
      _ -> []
    withSign sign left right
      | length (applicationPhrase left) < templateArity =
          case applicationPhrase right of
            first : remaining ->
              [applicationFrom
                (applicationPhrase left <> (sign first : remaining))]
            [] -> []
      | otherwise = []
    templateArity = length (syntaxTemplatePieces template)
    phrase = applicationPhrase value
    embeddedSigns =
      [ applicationFrom (before <> (sign first : rest) <> after)
      | (before, current, after) <- contexts phrase
      , (sign, operand) <- case current of
          Plus inner -> [(Plus, inner)]
          Minus inner -> [(Minus, inner)]
          _ -> []
      , first : rest <- [applicationPhrase operand]
      , not (null rest)
      ]
    contexts [] = []
    contexts (current : after) = ([], current, after) :
      [ (current : before, nested, remaining)
      | (before, nested, remaining) <- contexts after
      ]

declarationBoundaryCandidates :: Expression -> [Expression]
declarationBoundaryCandidates value = case value of
  IdentifierOperation name annotation Nothing ->
    [ IdentifierOperation name rewritten (Just given)
    | (rewritten, given) <- stripTrailingLiteralAssignment annotation
    ]
  IdentifierTemplateOperation parts annotation Nothing ->
    [ IdentifierTemplateOperation parts rewritten (Just given)
    | (rewritten, given) <- stripTrailingLiteralAssignment annotation
    ]
  _ -> []

stripTrailingLiteralAssignment
  :: Expression
  -> [(Expression, Expression)]
stripTrailingLiteralAssignment value = case value of
  FunctionApplication function
      (IdentifierOperation name annotation (Just given))
    | annotation == given ->
        [(FunctionApplication function (IdentifierReference name), given)]
  _ -> []

leftBoundaryCandidates
  :: SyntaxTemplate Expression
  -> Expression
  -> [Expression]
leftBoundaryCandidates template = descend id
  where
    descend _ MaybeThen {} | literalLed = []
    descend wrap current = case projectionLeftContext current of
      Just (left, rebuild) ->
        reassociate (wrap . rebuild) left
          <> descend (wrap . rebuild) left
      Nothing -> []
    reassociate wrap current =
      [ applicationFrom (prefix <> [wrap (applicationFrom suffix)])
      | position <- [1 .. length phrase - 1]
      , let (prefix, suffix) = splitAt position phrase
      ]
      where
        phrase = applicationPhrase current
    literalLed = case syntaxTemplatePieces template of
      SyntaxLiteral {} : _ -> True
      _ -> False
    projectionLeftContext = leftInfixContext

-- These outer parser layers are deliberately not part of
-- 'leftInfixContext': adding them to the recursive closure makes every map or
-- signature boundary combine with every other local rewrite. They are needed
-- only for a literal prefix followed by one general-expression hole, for
-- which a direct reassociation is complete.
terminalExpressionBoundaryCandidates
  :: SyntaxTemplate Expression
  -> Expression
  -> [Expression]
terminalExpressionBoundaryCandidates template
  | simpleExpressionPrefix = descend id
  | otherwise = const []
  where
    descend wrap current = case terminalLeftContext current of
      Just (left, rebuild) ->
        reassociate (wrap . rebuild) left
          <> descend (wrap . rebuild) left
      Nothing -> []
    reassociate wrap current =
      [ applicationFrom (prefix <> [wrap (applicationFrom suffix)])
      | position <- [1 .. length phrase - 1]
      , let (prefix, suffix) = splitAt position phrase
      ]
      where
        phrase = applicationPhrase current
    terminalLeftContext current = case current of
      FunctionTypeExpression generics left right ->
        Just (left,
          (\newLeft -> FunctionTypeExpression generics newLeft right))
      SyntaxType left right -> Just (left, (`SyntaxType` right))
      MapConcatenation left right -> Just (left, (`MapConcatenation` right))
      _ -> Nothing
    simpleExpressionPrefix = case reverse (syntaxTemplatePieces template) of
      SyntaxHole ExpressionSyntaxHole {} : reversedPrefix ->
        all literalPiece reversedPrefix
      _ -> False
    literalPiece SyntaxLiteral {} = True
    literalPiece _ = False

rightBoundaryCandidates :: Expression -> [Expression]
rightBoundaryCandidates = descend id
  where
    descend wrap current = case rightInfixContext current of
      Just (right, rebuild) ->
        reassociate (wrap . rebuild) right
          <> descend (wrap . rebuild) right
      Nothing -> []
    reassociate wrap current =
      [ applicationFrom (wrap (applicationFrom prefix) : suffix)
      | position <- [1 .. length phrase - 1]
      , let (prefix, suffix) = splitAt position phrase
      ]
      where
        phrase = applicationPhrase current

-- Hole-led word syntax can straddle concatenation structure. This is the same
-- boundary presentation used by runtime rewriting.
concatenationBoundaryCandidates
  :: SyntaxTemplate Expression
  -> Expression
  -> [Expression]
concatenationBoundaryCandidates template value = do
  SyntaxHole {} : _ <- pure (syntaxTemplatePieces template)
  literal <- case
      [text | SyntaxLiteral text <- syntaxTemplatePieces template] of
    first : _ -> [first]
    [] -> []
  (beforeComponents, component, afterComponents) <-
    componentContexts (flattenConcatenation value)
  (beforeLiteral, afterLiteral) <-
    maybeToList (directApplicationSplit literal component)
  left <- maybeToList (concatenationFrom
    (beforeComponents <> maybe [] (: []) beforeLiteral))
  right <- maybeToList (concatenationFrom
    (maybe [] (: []) (applicationFromMaybe afterLiteral)
      <> afterComponents))
  pure (applicationFrom [left, literalExpression literal, right])

-- A literal such as @take,@ is retained by the neutral parser as a postfix
-- concatenation boundary on the left component of @take, value@. Reify that
-- lossless boundary as one application member, without naming the comma token.
literalConcatenationBoundaryCandidates
  :: SyntaxTemplate Expression
  -> Expression
  -> [Expression]
literalConcatenationBoundaryCandidates template value = do
  firstLiteral <- case syntaxTemplatePieces template of
    SyntaxLiteral literal : _ -> [literal]
    _ -> []
  let components = flattenConcatenation value
  position <- [1 .. length components - 1]
  left <- maybeToList (concatenationFrom (take position components))
  right <- maybeToList (concatenationFrom (drop position components))
  let boundary = MapConcatenation left (AtlasMap [])
  if matchesLiteralExpression firstLiteral boundary
    then pure (applicationFrom [boundary, right])
    else []

flattenConcatenation :: Expression -> [Expression]
flattenConcatenation (MapConcatenation left right) =
  flattenConcatenation left <> flattenConcatenation right
flattenConcatenation expressionValue = [expressionValue]

componentContexts
  :: [value]
  -> [([value], value, [value])]
componentContexts [] = []
componentContexts (component : remaining) =
  ([], component, remaining) :
    [ (component : before, selected, after)
    | (before, selected, after) <- componentContexts remaining
    ]

concatenationFrom :: [Expression] -> Maybe Expression
concatenationFrom [] = Nothing
concatenationFrom (first : remaining) =
  Just (foldl MapConcatenation first remaining)

maybeToList :: Maybe value -> [value]
maybeToList Nothing = []
maybeToList (Just value) = [value]

leftInfixContext
  :: Expression
  -> Maybe (Expression, Expression -> Expression)
leftInfixContext value = case value of
  EitherType left right -> Just (left, (`EitherType` right))
  MaybeThen left right -> Just (left, (`MaybeThen` right))
  Addition left right -> Just (left, (`Addition` right))
  Subtraction left right -> Just (left, (`Subtraction` right))
  Equality left right -> Just (left, (`Equality` right))
  Inequality left right -> Just (left, (`Inequality` right))
  LessThan left right -> Just (left, (`LessThan` right))
  LessThanOrEqual left right -> Just (left, (`LessThanOrEqual` right))
  GreaterThan left right -> Just (left, (`GreaterThan` right))
  GreaterThanOrEqual left right -> Just (left, (`GreaterThanOrEqual` right))
  Multiplication left right -> Just (left, (`Multiplication` right))
  Exponentiation left right -> Just (left, (`Exponentiation` right))
  MapAccess left right -> Just (left, (`MapAccess` right))
  MapSpecification left right -> Just (left, (`MapSpecification` right))
  Overload left right -> Just (left, (`Overload` right))
  SafeOverload left right -> Just (left, (`SafeOverload` right))
  ReverseMapSpecification left right ->
    Just (left, (`ReverseMapSpecification` right))
  ReverseOverload left right -> Just (left, (`ReverseOverload` right))
  ReverseSafeOverload left right ->
    Just (left, (`ReverseSafeOverload` right))
  SuperEllipsisRange left right -> Just (left, (`SuperEllipsisRange` right))
  _ -> Nothing

rightInfixContext
  :: Expression
  -> Maybe (Expression, Expression -> Expression)
rightInfixContext value = case value of
  EitherType left right -> Just (right, EitherType left)
  Addition left right -> Just (right, Addition left)
  Subtraction left right -> Just (right, Subtraction left)
  Equality left right -> Just (right, Equality left)
  Inequality left right -> Just (right, Inequality left)
  LessThan left right -> Just (right, LessThan left)
  LessThanOrEqual left right -> Just (right, LessThanOrEqual left)
  GreaterThan left right -> Just (right, GreaterThan left)
  GreaterThanOrEqual left right -> Just (right, GreaterThanOrEqual left)
  Multiplication left right -> Just (right, Multiplication left)
  Exponentiation left right -> Just (right, Exponentiation left)
  MapAccess left right -> Just (right, MapAccess left)
  MapSpecification left right -> Just (right, MapSpecification left)
  Overload left right -> Just (right, Overload left)
  SafeOverload left right -> Just (right, SafeOverload left)
  ReverseMapSpecification left right ->
    Just (right, ReverseMapSpecification left)
  ReverseOverload left right -> Just (right, ReverseOverload left)
  ReverseSafeOverload left right ->
    Just (right, ReverseSafeOverload left)
  SuperEllipsisRange left right -> Just (right, SuperEllipsisRange left)
  _ -> Nothing

applicationPhrase :: Expression -> [Expression]
applicationPhrase value = case applicationSpine value of
  (function, arguments) -> function : arguments

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining

applicationFromMaybe :: [Expression] -> Maybe Expression
applicationFromMaybe [] = Nothing
applicationFromMaybe values = Just (applicationFrom values)

literalExpression :: String -> Expression
literalExpression = IdentifierReference . IdentifierString

matchesLiteral :: String -> Expression -> Bool
matchesLiteral literal (IdentifierReference (IdentifierString value)) =
  literal == value
matchesLiteral _ _ = False

matchesLiteralExpression :: String -> Expression -> Bool
matchesLiteralExpression literal expressionValue = case expressionValue of
  IdentifierReference (IdentifierString value) -> value == literal
  _ -> renderSourceExpression expressionValue == literal

directApplicationSplit
  :: String
  -> Expression
  -> Maybe (Maybe Expression, [Expression])
directApplicationSplit literal value =
  case break (matchesLiteral literal) (applicationPhrase value) of
    (_, []) -> Nothing
    (before, _ : after) -> Just (applicationFromMaybe before, after)
