-- | Lower declarative templates through the neutral parser, then match their
-- AST structure. Core operators therefore keep their ordinary AST meaning:
-- @~name@ is 'Lookup name' and @left, right@ is 'MapConcatenation left right'.
-- This module never manufactures identifier spellings for operators.
module SyntaxTemplateProjection
  ( structuralTemplateCaptures
  , projectSyntaxTemplate
  , applicationPhrase
  , applicationSpine
  , applicationFrom
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import DatraLanguage.AST
  ( Expression (..)
  , expressionChildren
  , mapExpressionChildren
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import Parsing (parseNeutralPhrase)

data LoweredTemplate = LoweredTemplate
  { loweredTemplateExpression :: Expression
  , loweredTemplateHoles :: [(Expression, SyntaxHoleKind Expression)]
  }

-- | Lower literal text and holes together. Because the same neutral parser
-- reads templates and programs, precedence and operator ownership are defined
-- exactly once.
lowerTemplate :: SyntaxTemplate Expression -> Maybe LoweredTemplate
lowerTemplate (SyntaxTemplate pieces) = firstValid [0 ..]
  where
    kinds = [kind | SyntaxHole kind <- pieces]
    firstValid [] = Nothing
    firstValid (base : remaining) =
      let markers = zipWith (\offset kind ->
            (EllipsisNatural (base + fromIntegral offset), kind))
            [0 :: Int ..] kinds
          source = unwords (render pieces (map fst markers))
      in case parseNeutralPhrase source of
          Right expressionValue
            | all ((== 1) . markerOccurrences expressionValue . fst) markers ->
                Just LoweredTemplate
                  { loweredTemplateExpression = expressionValue
                  , loweredTemplateHoles = markers
                  }
          _ -> firstValid remaining
    render [] _ = []
    render (SyntaxLiteral literal : remaining) markers =
      literal : render remaining markers
    render (SyntaxHole {} : remaining) (marker : markers) =
      renderSourceExpression marker : render remaining markers
    render (SyntaxHole {} : _) [] = []

markerOccurrences :: Expression -> Expression -> Int
markerOccurrences source marker = length
  [ ()
  | value <- expressionClosure source
  , value == marker
  ]

expressionClosure :: Expression -> [Expression]
expressionClosure value = value : concatMap expressionClosure
  (expressionChildren value)

-- | Enumerate structural captures in template order. A hole occupying one
-- application position may greedily absorb several application members;
-- elsewhere it captures the exact AST subtree selected by the parser.
structuralTemplateCaptures
  :: SyntaxTemplate Expression
  -> Expression
  -> [[(SyntaxHoleKind Expression, Expression)]]
structuralTemplateCaptures template source = case lowerTemplate template of
  Nothing -> []
  Just lowered ->
    [ zip (map snd holes)
        [ selected
        | (marker, _) <- holes
        , Just selected <- [Map.lookup marker captures]
        ]
    | captures <- matchExpression markerSet
        (loweredTemplateExpression lowered) source Map.empty
    , all (`Map.member` captures) (map fst holes)
    ]
    where
      holes = loweredTemplateHoles lowered
      markerSet = Map.fromList [(marker, ()) | (marker, _) <- holes]

type Captures = Map Expression Expression
type MarkerSet = Map Expression ()

matchExpression
  :: MarkerSet
  -> Expression
  -> Expression
  -> Captures
  -> [Captures]
matchExpression markers patternValue source captures =
  case patternMarker markers patternValue of
    Just marker -> bindMarker marker source captures
    Nothing -> case patternValue of
      FunctionApplication {} -> matchApplication
        markers patternValue source captures
      _
        | expressionShape patternValue /= expressionShape source -> []
        | otherwise -> matchChildren markers
            (expressionChildren patternValue)
            (expressionChildren source)
            captures

matchApplication
  :: MarkerSet
  -> Expression
  -> Expression
  -> Captures
  -> [Captures]
matchApplication markers patternValue source =
  matchApplicationMembers markers
    (applicationPhrase patternValue)
    (applicationPhrase source)

matchApplicationMembers
  :: MarkerSet
  -> [Expression]
  -> [Expression]
  -> Captures
  -> [Captures]
matchApplicationMembers _ [] [] captures = [captures]
matchApplicationMembers _ [] _ _ = []
matchApplicationMembers markers (patternValue : patterns) values captures =
  case patternMarker markers patternValue of
    Just marker ->
      [ result
      | count <- reverse [1 .. length values - length patterns]
      , let (selected, remaining) = splitAt count values
      , not (null selected)
      , bound <- bindMarker marker (applicationFrom selected) captures
      , result <- matchApplicationMembers markers patterns remaining bound
      ]
    Nothing -> case values of
      [] -> []
      value : remaining ->
        [ result
        | matched <- matchExpression markers patternValue value captures
        , result <- matchApplicationMembers markers patterns remaining matched
        ]

matchChildren
  :: MarkerSet
  -> [Expression]
  -> [Expression]
  -> Captures
  -> [Captures]
matchChildren _ [] [] captures = [captures]
matchChildren markers (patternValue : patterns) (value : values) captures =
  [ result
  | matched <- matchExpression markers patternValue value captures
  , result <- matchChildren markers patterns values matched
  ]
matchChildren _ _ _ _ = []

bindMarker :: Expression -> Expression -> Captures -> [Captures]
bindMarker marker selected captures = case Map.lookup marker captures of
  Nothing -> [Map.insert marker selected captures]
  Just previous
    | previous == selected -> [captures]
    | otherwise -> []

patternMarker :: MarkerSet -> Expression -> Maybe Expression
patternMarker markers expressionValue
  | Map.member expressionValue markers = Just expressionValue
  | otherwise = Nothing

expressionShape :: Expression -> Expression
expressionShape = mapExpressionChildren (const shapeChild)
  where
    shapeChild = EllipsisLiteral

type CaptureHole = SyntaxHoleKind Expression -> Expression -> Maybe Expression

projectSyntaxTemplate
  :: CaptureHole
  -> SyntaxTemplate Expression
  -> Expression
  -> Maybe [Expression]
projectSyntaxTemplate capture template expressionValue = firstJust
  [ traverseCaptures structural
  | structural <- structuralTemplateCaptures template expressionValue
  ]
  where
    traverseCaptures [] = Just []
    traverseCaptures ((kind, selected) : remaining) = do
      captured <- capture kind selected
      (captured :) <$> traverseCaptures remaining
    firstJust [] = Nothing
    firstJust (Nothing : remaining) = firstJust remaining
    firstJust (Just value : _) = Just value

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
