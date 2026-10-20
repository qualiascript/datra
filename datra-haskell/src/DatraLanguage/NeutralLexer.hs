-- | Lexical policy shared by the declaration-independent source reader.
-- Whether a complete syntax template is admissible is deliberately not a
-- character-level decision; this predicate only recognizes one opaque
-- symbolic token while parsing source.
module DatraLanguage.NeutralLexer
  ( isSymbolicSyntaxCharacter
  , isOpaqueSymbolicSyntaxLiteral
  ) where

import Data.List (isPrefixOf)
import DatraLanguage.AST.Operator qualified as AST
import DatraLanguage.Identifier
  ( isAsciiCharacter
  , isIdentifierCharacter
  )

isSymbolicSyntaxCharacter :: Char -> Bool
isSymbolicSyntaxCharacter character =
  isAsciiCharacter character
    && not (isIdentifierCharacter character)
    && character `notElem` (" \t\r\n(){}[];.\"#$\\" :: String)

isOpaqueSymbolicSyntaxLiteral :: String -> Bool
isOpaqueSymbolicSyntaxLiteral literal =
  not (null literal)
    && all isSymbolicSyntaxCharacter literal
    && literal `notElem` reservedRuns
    && all (not . (`isPrefixOf` literal)) reservedPrefixes
  where
    coreTokens = "&" : AST.ellipsisSymbol : "<~" :
      [ source
      | operator <- [minBound .. maxBound]
      , Just source <- [AST.operatorSourceSymbol operator]
      ]
    compactPrefixSkips =
      [ prefix <> AST.skipSourceSymbol
      | operator <-
          [ AST.AdditionOperator
          , AST.MinusOperator
          , AST.CoalizationOperator
          ]
      , Just prefix <- [AST.operatorSourceSymbol operator]
      ]
    reservedRuns = coreTokens <> compactPrefixSkips
    reservedPrefixes =
      [ source
      | operator <- [AST.ConcatenationOperator]
      , Just source <- [AST.operatorSourceSymbol operator]
      ]
