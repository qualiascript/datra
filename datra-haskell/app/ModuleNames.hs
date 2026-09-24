module ModuleNames (moduleIdentifier, isPrivateIdentifier) where
import Data.Char (toUpper, isAlphaNum)
import DatraLanguage.Identifier (isPrivateIdentifier)
import System.FilePath (takeBaseName)

-- library_one.datra -> LibraryOne; hyphens and spaces are also boundaries.
moduleIdentifier :: FilePath -> String
moduleIdentifier = concatMap capitalize . splitWords . takeBaseName
  where
    capitalize [] = []
    capitalize (first:rest) = toUpper first : rest
    splitWords input = case dropWhile (not . isAlphaNum) input of
      [] -> []
      remaining -> let (word,rest) = span isAlphaNum remaining in word : splitWords rest
