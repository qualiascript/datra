# Identifier Expressions and String Interpolation

## Scope

This design defines the `$` expression, dependent-declaration heads,
structural syntax capture, the internal representation of string
interpolation, and the `_StrExpr`/`_show` boundary for quoted interpolation.

`$` is the only standalone identifier-expression prefix operator. `%` is
reserved for interpolation inside quoted strings and has no standalone
expression form.

The internal name is `IdentifierExpression`. The public Datra name is:

```datra
_IdentifierExpr := datra.IdentifierExpr
```

## Identifier expressions

The source forms have these meanings:

| Source | AST meaning |
| --- | --- |
| `name` | Resolve the simple identifier `name`. |
| `$name` | Construct an identifier expression for the written name. |
| `$"any string"` | Construct an identifier expression whose name is the quoted payload. |
| `$(expression)` | Construct an identifier expression from an ordinary expression. |
| `$($do; _Block; $yield; _Expr)` | Construct a structural identifier expression. |
| `"text %(value)"` | Parse quoted-string interpolation. |

`SimpleIdentifierString` is the payload of a lexical identifier reference.
Identifier expressions may denote names containing any string, while a simple
identifier must satisfy the bare identifier grammar.

Every `$` form uses one AST family:

```haskell
newtype IdentifierExpression expression = IdentifierExpressionBody
  { identifierExpressionBody :: expression
  }

data Expression
  = ...
  | IdentifierReference SimpleIdentifierString
  | IdentifierExpression (IdentifierExpression Expression)
```

The operand remains ordinary expression structure. Bare, quoted, dynamic, and
sequential operands are not separate identifier-expression variants.
Canonical source rendering selects `$name`, `$"..."`, or `$(...)` from the
operand structure. Canonical operator rendering uses
`IdentifierExpressionOperator`.

## Dependent declarations

Every dependent declaration stores an identifier expression as its head:

```haskell
data DependentDeclaration expression = DependentDeclaration
  { dependentDeclarationHead :: IdentifierExpression expression
  , ...
  }
```

A bare declaration such as `a := 123` is parsed with the same head as
`$a := 123`. The normalized head value is `$a`; the left-hand side is not
evaluated as a lexical reference.

Declaration-head validity is structural. Parenthesized expressions and
general string templates are not alternate head paths, and prefixing a valid
head is total. No `Maybe`, sentinel value, or runtime `error` represents an
invalid declaration head.

Declaration rules compile directly from the identifier-expression body. A
singleton simple reference or string contributes literal syntax. Structural
members contribute literal or capture positions according to their AST role.
Modifier application order, block insertion, source-order priority, and
rejection diagnostics operate on this representation.

## Structural syntax capture

A structural identifier expression contains ordinary expression fields. A
semicolon separates adjacent fields and requires a source gap:

```datra
$($do; _Block; $yield; _Expr)
```

`$do` and `$yield` are literal positions. `_Block` and `_Expr` are capture
targets. Structural matching compares neutral AST structure; it does not
derive behavior from canonical rendering.

Capture is target-directed. Each capture position retains its ordinary target
expression. Evaluation of the target determines whether the selected source
is an identifier expression, a string expression, a block, or another value.

## String interpolation representation

The shared representation is a source-order concatenation of literal strings
and typed string expressions:

```haskell
data StringExpression value
  = ExpressionString value
  | BlockString value
  | FunctionBodyString value
  | DeclarationString value
  | DependentArgumentString value
  | IdentifierExpressionString value
  | StringLiteralString value
  | ValueString value

type StringInterpolationTemplate value =
  [StringTemplatePart (StringExpression value)]
```

`StringInterpolationTemplate` is a type alias for the concatenation itself.
It has no wrapper constructor and no parallel template AST. Literal chunks
use `StringTemplateLiteral`; interpolations use
`StringTemplateInterpolation` with a `StringExpression`.

Every evaluated `StringExpression` payload is a subfederation of `String`.
The source expression determines the capture category, while the stored
evaluated payload is the corresponding string federation. Conversion is total:

- string-producing values are retained;
- total non-string values become their canonical string;
- non-total values become a pointwise string federation.

Attaching declaration syntax is therefore pure. Its type cannot return an
interpolation-conversion error:

```haskell
attachDeclarationSyntax
  :: Maybe [Expression]
  -> EvaluatedStringTemplate
  -> InterpretedValue
  -> InterpretedValue
```

## Module boundary

String-interpolation representation, admissibility, projection, matching, and
evaluation live in DatraTypes. Application parsing remains in `app/Parsing`.
DatraTypes declares the parser capability it needs, and the application
supplies that capability:

```haskell
data StringInterpolationParser = StringInterpolationParser
  { parseStringInterpolationExpression :: String -> Maybe Expression
  , stringInterpolationExpressionWitnesses :: String -> String -> [String]
  , incompleteStringInterpolationPrefixOperator :: String -> Maybe String
  }
```

This dependency direction matches the canonical-string codec: semantic code
owns the protocol, while the application owns concrete parsing and rendering.
Projection parses a template and its witnesses through this capability, then
matching proceeds structurally over the resulting AST.

## `_StrExpr` and `_show` boundary

The surface boundary for a string-producing expression of source type `T` is:

```datra
let val _StrExpr := &T? do yield datra.StrExpr T
```

`_StrExpr T` participates in ordinary specification and subfederation.
Dynamic `$(expression)` uses this boundary; static and structural `$` operands
do not.

Quoted interpolation lowers before syntax rewriting to ordinary string
literals, `_show` application, and concatenation. For example:

```datra
"%(left) and %(right)"
```

lowers to the equivalent of:

```datra
(_show left), " and ", (_show right)
```

The lowering addresses the host `_show` binding by identity so source
shadowing cannot change interpolation semantics. Zero parts lower to `""`;
one part lowers directly; adjacent literal chunks may be coalesced. `%(` is
only quoted-string parser syntax.

The internal string-interpolation representation does not require a surface
`_StrExpr`, `_show`, or Datra host hook. Those bindings are introduced only
when the quoted-interpolation lowering boundary is enabled.

## Required invariants

1. The internal term is `IdentifierExpression`; the public term is
   `IdentifierExpr`.
2. `$` is the only standalone identifier-expression prefix operator.
3. `%` exists only inside quoted-string interpolation.
4. `SimpleIdentifierString` describes only bare lexical identifiers.
5. Identifier expressions may denote names containing any string.
6. A dependent declaration always has an `IdentifierExpression` head.
7. A bare left-hand identifier normalizes to the corresponding `$` head.
8. Structural syntax remains ordinary expression structure.
9. Declaration matching does not render and reparse identifier expressions.
10. Invalid declaration heads are unrepresentable.
11. `StringInterpolationTemplate` is a concatenation, not an AST wrapper.
12. Every evaluated `StringExpression` is a subfederation of `String`.
13. `attachDeclarationSyntax` is total and pure.
14. Parsing remains application-owned behind the DatraTypes parser capability.
15. `_StrExpr` uses exactly
    `let val _StrExpr := &T? do yield datra.StrExpr T`.
16. Quoted interpolation lowers to ordinary `_show` application and
    concatenation.

## Verification

1. Build the executable and affected suites with `-f-liquid -j1`.
2. Reject standalone `%` expressions while accepting `%(` inside strings.
3. Verify canonical and source round trips for every `$` operand shape.
4. Verify `a := value` and `$a := value` produce the same typed declaration
   head.
5. Verify specification, reverse specification, and subfederation for concrete
   and structural identifier expressions.
6. Verify every evaluated string-expression category produces only strings.
7. Verify interpolation projection and matching use the application parser
   capability without introducing a second parser in DatraTypes.
8. Verify interpolation with zero, one, and multiple holes when `_show`
   lowering is enabled.
