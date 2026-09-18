module Main (main) where

import Datra.AST (renderExpression)
import Datra.Interpreting (interpretLocatedExpression)
import Datra.Parsing (parseDatraLocatedWithSourceName)
import Datra.Rendering (renderInterpretedValue)
import Diagnostics (Located (locatedValue))
import Diagnostics.Localization
  ( Locale (English)
  , renderDatraError
  )

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
