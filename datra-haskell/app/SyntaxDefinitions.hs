-- | Declarative AST templates. External AST adapters preserve control semantics
-- without evaluating their captures or interpolating source strings.
module SyntaxDefinitions
  ( SyntaxRule (..), SyntaxPiece (..), declarationRules, expandSyntax
  , declarationLiterals, absorbFunSequence
  ) where
import Data.List (isPrefixOf)
import DatraLanguage.AST
import IdentifierValueType (isIdentifierValue)
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
      | kind `elem` ["_Expr", "_Block", "_Pages", "_IdenExp", "_AST"] = value
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
    controlArity "datra.syntax.fun" = Just 1
    controlArity "datra.syntax.with" = Just 2
    controlArity "datra.syntax.for" = Just 2
    controlArity "datra.syntax.withIn" = Just 3
    controlArity "datra.syntax.forIn" = Just 3
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
    controlWithValidCaptures "datra.syntax.let" [entry] =
      Right (Let (absorbAssignedConcatenation entry))
    controlWithValidCaptures "datra.syntax.fun" [entry] =
      Right (Fun (absorbFunSequence entry))
    controlWithValidCaptures "datra.syntax.with" [name,bound] =
      dependentBinder "with" WithBinding name bound
    controlWithValidCaptures "datra.syntax.for" [name,bound] =
      dependentBinder "for" ForBinding name bound
    controlWithValidCaptures "datra.syntax.withIn" [name,bound,body] =
      localDependentFamily "with" WithBinding name bound body
    controlWithValidCaptures "datra.syntax.forIn" [name,bound,body] =
      localDependentFamily "for" ForBinding name bound body
    controlWithValidCaptures "datra.syntax.eval" [source,target] =
      Right (Eval source target)
    controlWithValidCaptures name _ = Left (UnknownSyntaxControlAdapter name)

    dependentBinder name constructor binder bound =
      case binder of
        IdentifierReference identifier ->
          Right (constructor identifier False bound)
        OptionalType (IdentifierReference identifier) ->
          Right (constructor identifier True bound)
        AsciiStringLiteral identifier
          | isIdentifierValue identifier ->
              Right (constructor (IdentifierString identifier) False bound)
        _ -> Left (InvalidDependentBinder name)

    -- The witness is deliberately optional in the lowered representation:
    -- projection discards page zero, so the source spelling needs only the
    -- local identifier rather than the public argument-map binder form.
    localDependentFamily name constructor binder bound body = do
      dependent <- dependentBinder name constructor binder bound
      Right (MapAccess (AtlasMap [makeOptional dependent, body])
        (EllipsisNatural 1))
      where
        makeOptional (WithBinding identifier _ value) =
          WithBinding identifier True value
        makeOptional (ForBinding identifier _ value) =
          ForBinding identifier True value
        makeOptional value = value

    -- @:=@ normally stops before a comma so declarations remain map members.
    -- Inside @let@ the whole captured expression is one early binding, so a
    -- following concatenation belongs to the assigned value.
    absorbAssignedConcatenation value = case value of
      MapConcatenation
          (IdentifierOperation name annotation (Just given)) right
        | annotation == given ->
            let assignedValue = MapConcatenation given right
            in IdentifierOperation name assignedValue (Just assignedValue)
      _ -> value

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

-- Within @fun@, the canonical recursive-list spelling associates a following
-- sequence with the nonempty branch: @() | T; this@ means
-- @() | (T; this)@.  This keeps @;@ available for nested element types.
absorbFunSequence :: Expression -> Expression
absorbFunSequence expressionValue =
  case expressionValue of
    MapSequence (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , last remaining == This ->
          EitherType (AtlasMap []) (MapSequence (headValue : remaining))
    AtlasMap (EitherType (AtlasMap []) headValue : remaining)
      | not (null remaining)
      , last remaining == This ->
          EitherType (AtlasMap []) (AtlasMap (headValue : remaining))
    _ -> expressionValue

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
