{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}

-- | Source localization and structured diagnostics shared by the parser,
-- type checker, and interpreter.
module DatraLanguage.Diagnostics
  ( SourcePosition (..)
  , SourceSpan (..)
  , Located (..)
  , DatraError (..)
  , LocalizedMessage (..)
  , atSourceSpan
  , withoutSourceSpan
  , renderDatraErrorWith
  ) where

import Numeric.Natural (Natural)

-- | A zero-based source offset paired with one-based line and column numbers.
data SourcePosition = SourcePosition
  { sourceOffset :: Natural
  , sourceLine :: Natural
  , sourceColumn :: Natural
  }
  deriving (Eq, Ord, Show)

-- | A half-open source interval. Both positions refer to 'sourceName'.
data SourceSpan = SourceSpan
  { sourceName :: FilePath
  , sourceStart :: SourcePosition
  , sourceEnd :: SourcePosition
  }
  deriving (Eq, Ord, Show)

-- | A value paired with the source interval that produced it.
data Located value = Located
  { locatedSpan :: SourceSpan
  , locatedValue :: value
  }
  deriving (Eq, Foldable, Functor, Show, Traversable)

-- | A domain-specific error with an optional source location. DatraTypes
-- constructs the reason; a compiler or interpreter adds the relevant span.
data DatraError reason = DatraError
  { datraErrorSpan :: Maybe SourceSpan
  , datraErrorReason :: reason
  }
  deriving (Eq, Foldable, Functor, Show, Traversable)

data LocalizedMessage = LocalizedMessage
  { localizedSummary :: String
  , localizedDetails :: [String]
  }
  deriving (Eq, Show)

atSourceSpan :: SourceSpan -> reason -> DatraError reason
atSourceSpan sourceSpan reason = DatraError (Just sourceSpan) reason

withoutSourceSpan :: reason -> DatraError reason
withoutSourceSpan = DatraError Nothing

renderDatraErrorWith
  :: (reason -> LocalizedMessage)
  -> DatraError reason
  -> String
renderDatraErrorWith localize valueError =
  locationPrefix
    <> localizedSummary message
    <> concatMap ("\n  " <>) (localizedDetails message)
  where
    reason = datraErrorReason valueError
    message = localize reason
    locationPrefix =
      case datraErrorSpan valueError of
        Nothing -> ""
        Just sourceSpan ->
          let position = sourceStart sourceSpan
          in sourceName sourceSpan
              <> ":"
              <> show (sourceLine position)
              <> ":"
              <> show (sourceColumn position)
              <> ": "
