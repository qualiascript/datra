-- | Declarative AST templates. External AST adapters preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxPiece (..), declarationRules, expandSyntax, declarationLiterals ) where
import Data.List (isPrefixOf)
import DatraLanguage.AST
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure (..))

data SyntaxPiece = SyntaxLiteral String | SyntaxHole String deriving (Eq,Show)
data SyntaxRule = SyntaxRule
  { syntaxName :: String, syntaxPieces :: [SyntaxPiece]
  , syntaxOrdinary :: Bool, syntaxSignature :: Expression
  , syntaxModule :: Maybe String
  , syntaxImplementation :: Expression
  } deriving (Eq,Show)

declarationRules :: Expression -> [SyntaxRule]
declarationRules (Let value) = declarationRules value
declarationRules (IdentifierOperation (IdentifierString name) annotation (Just implementation)) =
  collect name (if annotation == implementation then implementation else MapSpecification implementation annotation)
  where
    collect key (EitherType a b) = collect key a <> collect key b
    collect key (MapSpecification body (SyntaxType patternText ordinary signature)) =
      [SyntaxRule key (map piece (words patternText)) ordinary signature Nothing body]
    collect _ _ = []
    piece ('$':kind) = SyntaxHole kind
    piece literal = SyntaxLiteral literal
declarationRules _ = []

expandSyntax
  :: SyntaxRule
  -> [Expression]
  -> Either SyntaxExpansionFailure Expression
expandSyntax rule captures = case externalSymbol (syntaxImplementation rule) of
  Just name | "datra.syntax." `isPrefixOf` name -> control name captures
  _ -> Right (FunctionApplication
    (scoped (MapSpecification (syntaxImplementation rule) (syntaxSignature rule)))
    (case checkedCaptures of [value] -> value; _ -> AtlasMap checkedCaptures))
  where
    scoped value = maybe value (`InModule` value) (syntaxModule rule)
    checkedCaptures = zipWith checkCapture [kind | SyntaxHole kind <- syntaxPieces rule] captures
    checkCapture kind value
      | kind `elem` ["Expr", "Block", "Pages", "_AST"] = value
      | otherwise = MapSpecification value (scoped (IdentifierReference (IdentifierString kind)))
    block (AtlasMap entries) = entries
    block value = [value]
    control name values =
      case controlArity name of
        Nothing -> Left (UnknownSyntaxControlAdapter name)
        Just expected
          | length values /= expected ->
              Left
                (InvalidSyntaxControlCaptures
                  name expected (length values))
          | otherwise -> controlWithValidCaptures name values
    controlArity "datra.syntax.if" = Just 3
    controlArity "datra.syntax.ifThen" = Just 2
    controlArity "datra.syntax.begin" = Just 2
    controlArity "datra.syntax.do" = Just 2
    controlArity "datra.syntax.let" = Just 1
    controlArity "datra.syntax.eval" = Just 2
    controlArity _ = Nothing
    controlWithValidCaptures "datra.syntax.if" [condition, yes, no] =
      Right (Conditional condition yes no)
    controlWithValidCaptures "datra.syntax.ifThen" [condition, yes] =
      Right (Conditional condition yes (AtlasMap []))
    controlWithValidCaptures "datra.syntax.begin" [entries,result] =
      Right (Begin (block entries) result)
    controlWithValidCaptures "datra.syntax.do" [entries,result] =
      Right (FunctionBody (block entries) result)
    controlWithValidCaptures "datra.syntax.let" [entry] = Right (Let entry)
    controlWithValidCaptures "datra.syntax.eval" [source,target] =
      Right (Eval source target)
    controlWithValidCaptures name _ = Left (UnknownSyntaxControlAdapter name)

externalSymbol :: Expression -> Maybe String
externalSymbol (External (AsciiStringLiteral symbol)) = Just symbol
externalSymbol (External descriptor) = findSymbol descriptor
  where
    findSymbol (IdentifierOperation (IdentifierString "symbol") (AsciiStringLiteral value) _) = Just value
    findSymbol (AtlasMap members) = first (map findSymbol members)
    findSymbol (MapConcatenation a b) = first [findSymbol a,findSymbol b]
    findSymbol _ = Nothing
    first [] = Nothing
    first (Just value:_) = Just value
    first (_:rest) = first rest
externalSymbol _ = Nothing

-- Literal alternatives of a named type can be spelled as keywords in an AST
-- pattern, while ordinary application keeps their $identifier value spelling.
declarationLiterals :: [Expression] -> String -> [String]
declarationLiterals declarations typeName = concatMap declaration declarations
  where
    declaration (Let value) = declaration value
    declaration (IdentifierOperation (IdentifierString name) annotation given)
      | name == typeName = literals (maybe annotation id given)
    declaration _ = []
    literals (AsciiStringLiteral text) = [text]
    literals (EitherType a b) = literals a <> literals b
    literals _ = []
