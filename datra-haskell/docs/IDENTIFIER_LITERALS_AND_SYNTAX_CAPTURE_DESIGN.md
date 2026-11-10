# Identifier Expressions and Structural Syntax Capture

## Scope

This design covers the unified `$` expression, dependent-declaration heads,
structural syntax capture, and quoted-string interpolation through the `_show`
migration.

`$` is the only standalone prefix operator in this design. `%` is reserved for
interpolation inside quoted strings and has no standalone expression form.

The internal name is `IdentifierExpression`. The public Datra names are:

```datra
_IdentifierExpr := datra.IdentifierExpr
let val _StrExpr := &T? do yield datra.StrExpr T
```

## Identifier expressions

The source forms are structurally distinct:

| Source | AST meaning |
| --- | --- |
| `name` | Resolve the simple identifier `name`. |
| `$name` | Construct an identifier expression for the written name. |
| `$"any string"` | Construct an identifier expression whose name is the quoted payload. |
| `$(expression)` | Construct an identifier expression from an ordinary expression. |
| `$($do; _Block; $yield; _Expr)` | Construct a structural identifier expression. |
| `"text %(value)"` | Parse quoted-string interpolation; `%` has no meaning outside the string. |

`SimpleIdentifierString` is the payload of a lexical identifier reference. Its
name deliberately states its restriction: identifier expressions may denote
names containing any string, while a simple identifier must satisfy the bare
identifier grammar.

There is one source AST family for every `$` form:

```haskell
newtype IdentifierExpression expression = IdentifierExpressionBody
  { identifierExpressionBody :: expression
  }

data Expression
  = ...
  | IdentifierReference SimpleIdentifierString
  | IdentifierExpression (IdentifierExpression Expression)
```

The operand remains ordinary expression structure. Static bare and quoted
operands are not separate AST variants. A sequential operand remains ordinary
expression structure as well.

Canonical source rendering uses `$name`, `$"..."`, or `$(...)` according to
the operand. Canonical operator rendering uses the single
`IdentifierExpressionOperator`.

## Dependent declarations

Every `DependentDeclaration` stores an `IdentifierExpression` as its head:

```haskell
data DependentDeclaration expression = DependentDeclaration
  { dependentDeclarationHead :: IdentifierExpression expression
  , ...
  }
```

A bare declaration:

```datra
a := 123
```

is normalized while parsing to the same declaration head as:

```datra
$a := 123
```

The normalized value is `$a`; the left-hand side is not evaluated as a lexical
reference. Parenthesized expressions and general string templates are not
alternate declaration-head paths. Prefixing a declaration head must be total
for its type: there is no fallback `error` branch for an invalid head.

Structural declaration heads compile from their `IdentifierExpression` body.
A singleton simple reference or string contributes a literal syntax token;
ordinary structural references contribute capture positions. This distinction
is derived from the head's position and expression structure.

## Structural syntax capture

A structural identifier expression contains ordinary expression fields. A
semicolon separates adjacent fields and requires a source gap:

```datra
$($do; _Block; $yield; _Expr)
```

`$do` and `$yield` are literal identifier-expression positions. `_Block` and
`_Expr` are capture targets. Matching operates on neutral AST structure and
never renders and reparses either side.

The declared `IdentifierExpression` is the syntax pattern. Quoted-string
interpolation may use parser-local parts before it lowers to ordinary
expressions; declaration matching and evaluation use ordinary expression
structure.

Capture is target-directed. A capture position carries its ordinary target
expression; evaluation of that target determines whether the selected source
is an identifier expression, string expression, block, or another value.

## Current checkpoint

The executable builds and standard-library loading reaches this exact error:

```text
module imports could not be scanned
  module: <command-line>
  syntax environment could not be constructed
  ModuleEvaluationFailed (StandardLibraryParseFailure "std.datra" "operation has no effect inside block\n  expression: yield ((^n? :: Nat) do yield (slots[0 .. n]))")
```

Reproduce it with:

```sh
cabal run datra-haskell -- build --source '()' \
  --ast-output /tmp/datra-identifier-expr.ast \
  --output /tmp/datra-identifier-expr.out
```

## Remaining implementation order

### 1. Compile declaration heads directly

Compile each declaration rule directly from its `IdentifierExpression` body.

The direct compiler must preserve:

- literal singleton `$name` and `$"..."` heads;
- structural sequences and required gaps;
- identifier-expression capture positions;
- modifier application order for `let`, `def`, and `val`;
- insertion of a dependent declaration into `begin` and `do` blocks;
- source-order rule priority and rejection diagnostics.

Only the direct expression representation participates in rule compilation,
matching, and diagnostics.

### 2. Complete identifier-expression capture semantics

`datra.IdentifierExpr` must accept the full identifier-expression value, not
only an `IdentifierReference`. Complete the value-form, semantics,
specification, reverse-specification, subfederation, access, result-contract,
and rendering cases so every dispatch is exhaustive.

Structural matching must return selected source expressions and capture them
against the evaluated target. It must not infer behavior from rendered names
or special-case standard-library operators.

The declared expression and evaluated capture target are the only authorities
for structural selection and capture behavior.

### 3. Introduce `_StrExpr`

Add the host type constructor and the exact standard-library declaration:

```datra
let val _StrExpr := &T? do yield datra.StrExpr T
```

`_StrExpr T` is the typed boundary for an expression that produces a string
from a value of source type `T`. Its string result participates in ordinary
specification and subfederation. Dynamic `$(expression)` uses this boundary;
static and structural `$` operands do not.

### 4. Migrate quoted interpolation to `_show`

Define a generic `_show` binding whose result is `_StrExpr T`. Lower every
quoted template before syntax rewriting to ordinary string literals, function
application, and concatenation:

```datra
"%(left) and %(right)"
```

becomes the equivalent of:

```datra
(_show left), " and ", (_show right)
```

The lowering must address the host binding by identity so source shadowing of
`_show` cannot change interpolation semantics. Zero parts lower to `""`; one
part lowers directly; adjacent literal chunks may be coalesced.

The general AST and runtime contain only the lowered form. `%(` remains only
quoted-string parser syntax.

## Verification

At each step:

1. Build the executable and affected suites with `-f-liquid -j1`.
2. Keep the exact standard-library checkpoint above until the code intentionally
   advances beyond it.
3. Reject standalone `%` expressions while accepting `%(` inside strings.
4. Verify canonical and source round trips for every `$` operand shape.
5. Verify `a := value` and `$a := value` produce the same typed declaration
   head.
6. Verify specification, reverse specification, and subfederation for concrete
   and structural identifier expressions.
7. Verify interpolation with zero, one, and multiple holes after `_show`
   lowering.

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
9. Matching never renders, reparses, or re-lexes expressions.
10. No invalid declaration-head state is represented with `Nothing` or a
    runtime `error` fallback.
11. `_StrExpr` uses exactly
    `let val _StrExpr := &T? do yield datra.StrExpr T`.
12. Interpolation lowers to ordinary `_show` application and concatenation.
13. Declaration matching and string evaluation operate on ordinary expression
    structure.
