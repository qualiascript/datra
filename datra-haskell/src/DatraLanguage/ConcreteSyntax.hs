-- | Concrete non-operator source spellings. Operator tokens live in
-- 'DatraLanguage.AST.Operator'; this module owns delimiters and string/comment
-- markers so parser control flow never redispatches raw symbolic literals.
module DatraLanguage.ConcreteSyntax
  ( StructuralDelimiter (..)
  , delimiterCharacter
  , delimiterText
  , closingDelimiters
  , commentCharacter
  , stringQuoteCharacter
  , escapeCharacter
  , interpolationCharacter
  , sourceSpaceCharacter
  , sourceHorizontalTabCharacter
  , sourceCarriageReturnCharacter
  , sourceLineFeedCharacter
  , lineFeedEscapeCharacter
  , sourceSpace
  , sourceLineFeed
  , isSourcePresentationCharacter
  , isSourceHorizontalPresentationCharacter
  , isSourceLineBreakCharacter
  , isSymbolicSourceCharacter
  ) where

import Data.Char (isSpace)
import DatraLanguage.Identifier
  ( isAsciiCharacter
  , isIdentifierCharacter
  )

data StructuralDelimiter
  = OpenParenthesis
  | CloseParenthesis
  | OpenBrace
  | CloseBrace
  | OpenBracket
  | CloseBracket
  deriving (Bounded, Enum, Eq, Show)

delimiterCharacter :: StructuralDelimiter -> Char
delimiterCharacter OpenParenthesis = '('
delimiterCharacter CloseParenthesis = ')'
delimiterCharacter OpenBrace = '{'
delimiterCharacter CloseBrace = '}'
delimiterCharacter OpenBracket = '['
delimiterCharacter CloseBracket = ']'

delimiterText :: StructuralDelimiter -> String
delimiterText = pure . delimiterCharacter

closingDelimiters :: [StructuralDelimiter]
closingDelimiters = [CloseParenthesis, CloseBrace, CloseBracket]

commentCharacter :: Char
commentCharacter = '#'

stringQuoteCharacter :: Char
stringQuoteCharacter = '"'

escapeCharacter :: Char
escapeCharacter = '\\'

interpolationCharacter :: Char
interpolationCharacter = '%'

sourceSpaceCharacter :: Char
sourceSpaceCharacter = ' '

sourceHorizontalTabCharacter :: Char
sourceHorizontalTabCharacter = '\t'

sourceCarriageReturnCharacter :: Char
sourceCarriageReturnCharacter = '\r'

sourceLineFeedCharacter :: Char
sourceLineFeedCharacter = '\n'

lineFeedEscapeCharacter :: Char
lineFeedEscapeCharacter = 'n'

sourceSpace :: String
sourceSpace = [sourceSpaceCharacter]

sourceLineFeed :: String
sourceLineFeed = [sourceLineFeedCharacter]

isSourcePresentationCharacter :: Char -> Bool
isSourcePresentationCharacter character =
  isSourceHorizontalPresentationCharacter character
    || isSourceLineBreakCharacter character

isSourceHorizontalPresentationCharacter :: Char -> Bool
isSourceHorizontalPresentationCharacter character =
  character == sourceSpaceCharacter
    || character == sourceHorizontalTabCharacter

isSourceLineBreakCharacter :: Char -> Bool
isSourceLineBreakCharacter character =
  character == sourceCarriageReturnCharacter
    || character == sourceLineFeedCharacter

isSymbolicSourceCharacter :: Char -> Bool
isSymbolicSourceCharacter character =
  isAsciiCharacter character
    && not (isIdentifierCharacter character)
    && not (isSpace character)
    && character `notElem`
      ( map delimiterCharacter [minBound .. maxBound]
          <> [stringQuoteCharacter, escapeCharacter]
      )
