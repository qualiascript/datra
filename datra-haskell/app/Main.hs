module Main (main) where

import DatraLanguage.AST (renderExpression)
import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Localization
  ( Locale (English)
  , renderDatraError
  )
import Interpreting (interpretLocatedExpression)
import Parsing (parseDatraLocatedWithSourceName)
import Rendering (renderInterpretedValue)

main :: IO ()
main = do
  let inputPath = "resources/input.datra"
  source <- readFile inputPath
  case parseDatraLocatedWithSourceName inputPath source of
    Left message -> ioError (userError message)
    Right locatedExpression -> do
      writeFile
        "resources/output.datra.ast"
        (renderExpression (locatedValue locatedExpression) <> "\n")
      case interpretLocatedExpression locatedExpression of
        Left valueError ->
          ioError (userError (renderDatraError English valueError))
        Right value ->
          writeFile
            "resources/output.datra"
            (renderInterpretedValue value <> "\n")
