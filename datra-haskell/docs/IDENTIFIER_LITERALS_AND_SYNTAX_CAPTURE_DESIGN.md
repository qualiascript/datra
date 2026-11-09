# Identifier Literals and Structural Syntax Capture

## Purpose

This design defines identifier literals, the `$` operator, string
interpolation, and declared-syntax capture around one shared expression model.
Identifier values and strings are distinct. String interpolation lowers to
ordinary function application and concatenation. Declared syntax is stored as
ordinary expression structure rather than a parallel template language.

## Identifier model

Datra has three distinct source forms:

| Source | Expression meaning | Evaluation |
| --- | --- | --- |
| `name` | `IdentifierReference "name"` | Resolve `name` in lexical scope. |
| `$name` | `IdentifierLiteral "name"` | Produce the identifier named `name`. |
| `"name"` | `AsciiStringLiteral "name"` | Produce a list of characters. |

`IdentifierString` is the validated name payload shared by references and
identifier literals. It is not an expression and is not a string value.

The identifier rules have one owner, `DatraLanguage.Identifier`. That module
defines identifier spelling validation, valid identifier characters, private
name detection, and the `IdentifierString` boundary. Parsing, rendering, and
evaluation use those definitions directly.

The semantic invariants are:

1. Identifier references, identifier literals, and string literals are
   different expression forms.
2. `$name` does not resolve `name` in lexical scope.
3. Identifier literals do not inhabit `Str`.
4. String literals do not inhabit `datra.IdentifierLiteral`.
5. Identifier-literal equality compares validated identifier names.
6. Specification and subfederation treat identifier literals as identifier
   values without string coercion.
7. A dependent declaration whose complete left-hand side is an identifier
   reference normalizes through the equivalent static identifier literal.

## The `$` operator

`$` is the identifier-literal prefix operator. It accepts either a bare
identifier operand or an expression whose evaluated value is a string:

```datra
$abc
$(nameExpression)
$"abc"
```

`$abc` is the static form. Parsing validates `abc` and constructs an
`IdentifierLiteral` expression directly. It does not construct an
`IdentifierReference` or an `AsciiStringLiteral` as an intermediate semantic
form.

The expression form evaluates its operand, requires one string value, validates
that value with the ordinary identifier grammar, and produces the corresponding
identifier literal. A literal operand may be folded eagerly:

```datra
$abc = $("abc")
```

Parentheses retain their ordinary grouping meaning. `$abc` quotes the written
name, while `$(abc)` evaluates the lexical reference `abc` and converts the
resulting string to an identifier. A non-string operand or invalid identifier
spelling fails at the first point where it is known.

`$` is represented by the ordinary operator AST and participates in ordinary
traversal, lowering, rendering, specification, and subfederation. Syntax
rewriting never recognizes it through source-string comparison.

## Dependent declaration names

A dependent declaration accepts exactly two kinds of left-hand side:

1. An identifier reference, which is piped through the corresponding static
   identifier literal before the declaration is assembled.
2. An expression that subtypes `datra.IdentifierLiteral`.

For the first case:

```datra
abc := 1234
```

is exactly equivalent to:

```datra
$abc := 1234
```

This is a declaration-head normalization rule. It does not perform lexical
lookup, and it does not make `abc` and `$abc` equivalent in an ordinary
expression position. The normalized declaration stores the validated
`IdentifierString` through the same identifier-literal path as the explicit
form, so implicit and explicit declaration names cannot acquire different
binding semantics.

The greedy `SyntaxTemplate` expression subtypes `datra.IdentifierLiteral`.
This permits a declaration head to describe an identifier through a more
abstract identifier-literal expression while preserving one declaration-name
domain.

`Str` does not subtype `datra.IdentifierLiteral`, so a string expression cannot
serve directly as a dependent-declaration head. A string must pass through `$`
and identifier validation explicitly before it can name a declaration. Thus
dependent declarations consume identifier literals, including their abstract
subtypes, but never consume strings as names.

## AST and evaluated representation

The source AST represents both static and dynamic identifier-literal operands:

```haskell
data IdentifierLiteralOperand expression
  = StaticIdentifier IdentifierString
  | EvaluatedIdentifier expression

data Expression
  = ...
  | IdentifierReference IdentifierString
  | IdentifierLiteral (IdentifierLiteralOperand Expression)
```

The operator and lowered representations retain the distinction between
lexical references and identifier literals:

```haskell
IdentifierReferenceValue IdentifierString
IdentifierLiteralValue IdentifierString
```

Evaluation produces a dedicated identifier value:

```haskell
IdentifierLiteralForm IdentifierString
```

Generic expression operations cover identifier literals, including child
traversal, normalization, source rendering, source-to-operator lowering,
canonical rendering, diagnostics, generators, shrinkers, and round trips.

Optional names remain a binder property. They do not turn an identifier
literal into a binder or make identifier values optional implicitly.

## Canonical rendering

Strings always use quoted canonical syntax:

```datra
"abc"
```

Identifier literals use `$` syntax:

```datra
$abc
$("operator spelling")
```

The renderer chooses the bare `$name` form only when the payload is valid bare
identifier syntax. Other payloads use an explicitly quoted operand. Canonical
strings never use `$` as a compact spelling.

## String interpolation lowering

`StringTemplatePart` is a parser-local representation. Before an expression
enters syntax rewriting or evaluation, every quoted string template lowers to
ordinary expressions.

Interpolation holes become calls to the host `to_string` function. Literal
chunks remain string literals. Multiple parts are joined with the ordinary
`,` concatenation AST:

```datra
"%(value1)%(value2)"
```

lowers to:

```datra
(to_string value1), (to_string value2)
```

and:

```datra
"%(value1) and %(value2)"
```

lowers to:

```datra
(to_string value1), " and ", (to_string value2)
```

An empty template lowers to `""`. A single part lowers directly to that part.
Adjacent literal chunks may be coalesced. Lowering refers to the host binding
by binding identity, so source shadowing of `to_string` cannot change parsed
interpolation semantics.

There is no post-parser string-template expression, interpolation-hole kind,
or template evaluator. Function application, concatenation, evaluation, and
ordinary specification own the lowered expression.

## `to_string`

The host provides one total function:

```datra
datra.to_string : Any -> Str
```

The standard library exposes it as `to_string` with the same domain and
codomain. It returns the canonical string presentation used by interpolation:

```datra
to_string "abc" = "\"abc\""
to_string $abc = "abc"
```

Consequently:

```datra
"abc" =/= "%("abc")"
"%("abc")" = "\"abc\""
"%($abc)" = "abc"
$abc = $("%($abc)")
"%($abc)-%($def)" = "abc-def"
$abcdef = $("%($abc)%($def)")
```

Every identifier-literal interpolation contributes its `IdentifierString`
payload independently. This follows from ordinary `to_string` application and
works for any number of holes; it is not a singleton-template rule.

## Declared syntax representation

A declared syntax pattern is an ordinary `Expression`. For example:

```datra
%($do; _Block; $yield; _Expr)
```

contains ordinary `IdentifierLiteral` nodes at the `$do` and `$yield` literal
positions and ordinary target expressions at `_Block` and `_Expr`. Compilation
records the pattern expression and the locations of its targets.

Function syntax, candidate matching, admissibility, priority, syntax
equivalence, and expansion all consume this structural representation. Rule
metadata may refer to positions in the pattern, but it does not duplicate the
pattern as a template-piece tree.

`SyntaxTemplate` is the sole `%` expression construct across the source AST,
operator AST, evaluated plan, parser, renderer, and diagnostics. It denotes
ordinary greedy `%` application and subtypes `datra.IdentifierLiteral`. A
syntax declaration stores that expression structure and its target locations
directly; it does not introduce a second template-piece representation or a
host-visible template type.

## Structural matching and capture

Structural selection operates on the declared pattern and the neutral source
expression:

```haskell
structuralCaptures
  :: Expression
  -> Expression
  -> [[(Expression, Expression)]]
```

Each result pair is a declared target expression and the selected neutral
source expression. Literal identifier positions compare validated
`IdentifierString` values. Matching does not compare rendered source text.

Application spines, prefix operators, infix operators, optional structure,
and arbitrary arity are matched through neutral AST constructors. Projection
provides only structural AST views that cannot be expressed by declarations in
`std.datra`. Standard-library operations such as `let`, `def`, `val`, `do`,
`yield`, lookup, and comma have no operation-specific projection behavior.

After structural selection, the evaluator captures each source expression
against its evaluated target:

1. Syntax-category targets preserve and validate AST structure.
2. `datra.IdentifierLiteral` accepts a valid bare identifier source token.
3. `Str` accepts explicit string syntax and rejects bare identifiers and
   identifier literals.
4. Lists of syntax categories recursively capture their members.
5. Other targets use ordinary evaluation, specification, and subfederation.

The evaluator also owns target-directed normalization. For example, `_Block`
may normalize an application-shaped selection into an `AtlasMap`. The rewrite
stack stores the target, selected source, and completed evidence without
switching on target types.

Admissibility checks structural invariants directly. Neither admissibility nor
matching renders, reparses, or re-lexes a pattern.

## Lexical ownership

- `DatraLanguage.Identifier` owns identifier characters and valid identifier
  spellings.
- `DatraLanguage.AST.Operator` owns built-in operator spellings.
- The source parser owns mechanical token boundaries.
- Rendering uses the AST form and its owning spelling rules.

Declared syntax remains structural throughout matching. Token spelling is
therefore never reconstructed from rendered expressions.

## Standard-library surface

The standard library exposes the concepts source programs use:

```datra
_IdentifierLiteral := datra.IdentifierLiteral
let val to_string := (Any -> Str) datra.to_string
```

Syntax tokens such as `$let`, `$do`, `$yield`, `$or`, and `$to` are identifier
literals. Holes intended to accept bare source identifiers target
`_IdentifierLiteral`. Holes intended to accept character data target `Str` and
require quoted source.

## Required tests

Parser and AST tests cover:

- `abc`, `$abc`, and `"abc"` as distinct AST forms;
- identical dependent-declaration structure for `abc := value` and
  `$abc := value`;
- acceptance of identifier-literal subtypes and rejection of direct `Str`
  expressions as dependent-declaration heads;
- static and dynamic identifier-literal operands;
- identifier validation and eager invalid-operand failures;
- traversal, lowering, source rendering, and canonical round trips;
- interpolation lowering to string literals, `to_string`, and concatenation;
- any number of identifier-literal interpolation holes;
- canonical quoted strings.

Interpreter and type tests cover:

- `$abc = $("abc")`;
- the quoted-string and identifier interpolation equalities above;
- `to_string : Any -> Str` through host and standard-library bindings;
- equivalence between interpolation and its lowered concatenation expression;
- identifier/string membership distinctions;
- specification, reverse specification, and subfederation of identifier
  literals;
- optional binder names independently of optional identifier values.

Declared-syntax tests cover:

- identifier literals at syntax-token positions;
- target-directed `Str` and `_IdentifierLiteral` captures;
- prefix, infix, and multi-piece patterns at arbitrary arity;
- generic matching of `do`/`yield`, `if`/`then`/`else`,
  `let`/`def`/`val`, lookup, and comma;
- stable declaration-order candidate selection and rejection ordering;
- absence of render/reparse behavior.

## Required invariants

1. `$abc`, `abc`, and `"abc"` are distinct source, AST, and value categories.
2. Static identifier payloads are validated `IdentifierString` values.
3. Identifier literals neither perform lexical lookup nor use string storage.
4. Canonical strings and string reference payloads are quoted.
5. Every interpolation lowers before syntax rewriting.
6. `to_string : Any -> Str` is the sole interpolation conversion.
7. Declared syntax is stored as ordinary expression structure.
8. Literal syntax positions are `IdentifierLiteral` expression nodes.
9. Every capture position carries one ordinary target expression.
10. The evaluated target is the sole authority for capture behavior.
11. The rewrite stack contains no target-specific capture dispatch.
12. Structural matching does not render, parse, or re-lex expressions.
13. Standard-library operations are not re-encoded as projection cases.
14. Identifier spelling has one owner in `DatraLanguage.Identifier`.
15. Built-in operator spelling has one owner in the operator AST.
16. Declared patterns remain ordinary expressions throughout compilation and
    matching.
17. `SyntaxTemplate` names the greedy `%` expression exclusively.
18. `abc := value` and `$abc := value` assemble the same dependent declaration.
19. Every other dependent-declaration head subtypes
    `datra.IdentifierLiteral`; `Str` is not a declaration-name domain.
20. `SyntaxTemplate` subtypes `datra.IdentifierLiteral`.
