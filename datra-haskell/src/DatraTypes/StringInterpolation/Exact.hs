-- | Representation-independent matching for exact string concatenations.
-- Callers retain ownership of their segment and capture representations; this
-- module only supplies the shared, terminating boundary search.
module StringInterpolation.Exact
  ( matchExactSegments
  ) where

import Data.List (isPrefixOf)

-- | Match a sequence of literal and capture segments against the complete
-- input.  A segment is viewed as either @Right literal@ or @Left capture@.
-- Capture candidates are supplied by the caller's existing inverse codec.
matchExactSegments
  :: Monad operation
  => (segment -> Either capture String)
  -> (capture -> String -> operation [selected])
  -> [segment]
  -> String
  -> operation [[selected]]
matchExactSegments view decode = match
  where
    match [] remaining = pure [[] | null remaining]
    match (segment : remaining) text = case view segment of
      Right literal -> case stripLiteral literal text of
        Nothing -> pure []
        Just suffix -> match remaining suffix
      Left capture -> do
        alternatives <- traverse (attempt capture remaining text)
          (captureBoundaries remaining text)
        pure (concat alternatives)

    attempt capture remaining text boundary = do
      let (captured, suffix) = splitAt boundary text
      selected <- decode capture captured
      tails <- match remaining suffix
      pure [value : tailValues | value <- selected, tailValues <- tails]

    captureBoundaries (next : _) text = case view next of
      Right literal ->
        [ boundary
        | boundary <- [0 .. length text]
        , literal `isPrefixOf` drop boundary text
        ]
      Left _ -> [0 .. length text]
    captureBoundaries [] text = [0 .. length text]

    stripLiteral literal text
      | literal `isPrefixOf` text = Just (drop (length literal) text)
      | otherwise = Nothing
