# Identifier Literals and Structural Syntax Capture

## Purpose

This design defines identifier literals, the unified `$` prefix operator,
string interpolation, and declared-syntax capture around one shared expression
model. Identifier values and strings are distinct. String interpolation lowers
to generic `_show` application and ordinary concatenation. `_StrExpr` provides
the shared typed string-expression boundary used by interpolation and dynamic
identifier construction. Declared syntax is stored as ordinary expression
structure rather than a parallel template language.

`$` is the only prefix operator for constructing identifier-literal
expressions. Its behavior is determined by the structure of its operand. Bare
identifiers, strings, and ordinary evaluated expressions produce identifier
values. A sequential `AtlasMap` operand produces a greedy structural syntax
pattern. `%` is reserved for interpolation inside quoted strings and is not a
standalone expression operator.

## Identifier model

Datra has three distinct source forms:

| Source | Expression meaning | Evaluation |
| --- | --- | --- |
| `name` | `IdentifierReference "name"` | Resolve `name` in lexical scope. |
| `$name` | `IdentifierLiteral "name"` | Produce the identifier named `name`. |
| `"name"` | `AsciiStringLiteral "name"` | Produce a list of characters. |

`IdentifierString` is the identifier payload shared by references and
identifier literals. It is not an expression and is not a string value. A bare
identifier spelling must satisfy the compact identifier grammar. A quoted
identifier spelling may contain any contents admitted by a Datra string, so
`$"Hello, world!"` is a valid identifier literal even though its payload cannot
be written as a bare identifier.

The identifier rules have one owner, `DatraLanguage.Identifier`. That module
defines bare-identifier characters, private-name detection, quoted identifier
spelling, and the `IdentifierString` boundary. Parsing, rendering, and
evaluation use those definitions directly.

The semantic invariants are:

1. Identifier references, identifier literals, and string literals are
   different expression forms.
2. `$name` does not resolve `name` in lexical scope.
3. Identifier literals do not inhabit `Str`.
4. String literals do not inhabit `datra.IdentifierLiteral`.
5. Identifier-literal equality compares identifier payloads.
6. Specification and subfederation treat identifier literals as identifier
   values without string coercion.
7. A dependent declaration whose complete left-hand side is an identifier
   reference normalizes through the equivalent static identifier literal.

## The unified `$` operator

`$` accepts four source shapes:

```datra
$hello
$"Hello, world!"
$(nameExpression)
$($do; _Block; $yield; _Expr)
```

The first form is static. Parsing validates the bare spelling and constructs an
`IdentifierLiteral` directly. It does not construct an
`IdentifierReference` or an `AsciiStringLiteral` as an intermediate semantic
form.

The second form constructs an identifier literal from the quoted payload. The
quotes select the full-string spelling and are not part of the payload.

The third form is dynamic. Parentheses retain their ordinary grouping meaning.
The operand is captured against `_StrExpr _T`, with `_T` inferred from the
operand, and the result is evaluated as a subfederation of `Str`. The resulting
single string becomes the identifier payload. A literal operand may be folded
eagerly:

```datra
$hello = $("hello")
```

Consequently `$hello` quotes the written name, while `$(hello)` resolves the
lexical reference `hello` and evaluates its string-expression result to
construct an identifier. An operand that cannot satisfy `_StrExpr _T` fails at
the first point where its type is known. Forms such as `$(Nat)` use this same
ordinary dynamic-expression path; grouping does not create a special
identifier-reference rule.

The fourth form uses the same operator on a sequential `AtlasMap`. `$` does not
evaluate that map as a string. It retains the map's fields as a greedy
structural syntax pattern. This use is unambiguous because ordinary identifier
construction has no value-level conversion from an `AtlasMap`.

Operand classification is structural and occurs before evaluation:

1. A bare identifier token becomes a static identifier operand.
2. A quoted string becomes a static full-string identifier operand.
3. An ordinary grouped expression becomes a dynamic `_StrExpr _T` identifier
   operand.
4. A grouped sequential `AtlasMap` becomes a structural syntax operand.

There is one `$` operator in the operator vocabulary and one corresponding
source AST family. Traversal, normalization, lowering, rendering,
specification, subfederation, and diagnostics handle it through ordinary AST
dispatch. Syntax rewriting never identifies `$` through rendered source text.

## Sequential syntax fields and gaps

A structural syntax operand consists of one or more ordinary expression
fields. In source, `;` separates adjacent fields and denotes a required
whitespace gap:

```datra
$($do; _Block; $yield; _Expr)
```

Each gap requires one or more whitespace characters between the corresponding
fields. The parser retains the field boundary, not the particular amount or
spelling of the whitespace. When a pattern is matched or materialized as an
identifier, the gap's canonical value is one ASCII space. In the source
spelling of the structural operand, the canonical separator is `;` followed by
that one space:

```datra
$($do; _Block; $yield; _Expr)
```

The neutral source parser establishes the same field boundaries in a candidate
phrase. Structural matching therefore checks application and sequence
structure without rendering or re-lexing either expression. Comments and
layout are handled by the source parser's ordinary whitespace rules; they do
not become syntax-pattern payloads.

A sequential syntax operand may contain prefix, infix, postfix, optional, and
nested expressions. Literal positions are ordinary identifier literals such as
`$do` and `$yield`; capture positions are ordinary target expressions such as
`_Block` and `_Expr`.

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
expression position. The normalized declaration stores the same
`IdentifierString` as the explicit form, so implicit and explicit declaration
names cannot acquire different binding semantics.

A structural `$` expression subtypes `datra.IdentifierLiteral`. This permits a
declaration head to describe a family of identifiers through an abstract
identifier-literal expression while preserving one declaration-name domain.

`Str` does not subtype `datra.IdentifierLiteral`, so a string expression cannot
serve directly as a dependent-declaration head. A string must pass through `$`
explicitly before it can name a declaration. Dependent declarations therefore
consume identifier literals, including structural subtypes, but never consume
strings as names.

## AST and evaluated representation

The source AST represents both static and expression operands:

```haskell
data IdentifierLiteralOperand expression
  = StaticIdentifier IdentifierString
  | IdentifierExpression expression

data Expression
  = ...
  | IdentifierReference IdentifierString
  | IdentifierLiteral (IdentifierLiteralOperand Expression)
```

`IdentifierExpression` preserves its operand as ordinary expression structure.
If that operand is a sequential `AtlasMap`, compilation interprets its members
as syntax fields and records their capture locations. Every other operand is
captured against `_StrExpr _T` and evaluated through its `Str` subfederation
before identifier construction. There is no separate `GreedyStringTemplate`
or `%` expression constructor.

The operator and lowered representations retain the distinction between
lexical references and identifier literals:

```haskell
IdentifierReferenceValue IdentifierString
IdentifierLiteralValue (IdentifierLiteralOperand OperatorExpression)
```

Evaluation of a concrete identifier produces a dedicated identifier value:

```haskell
IdentifierLiteralForm IdentifierString
```

A structural operand carries an evaluated syntax plan derived from its
ordinary fields. That plan is evaluation metadata for the `$` expression; it
does not replace the declared expression with a second template-piece AST.

Generic expression operations cover all `$` forms, including child traversal,
normalization, source rendering, source-to-operator lowering, canonical
rendering, diagnostics, generators, shrinkers, and round trips.

Optional names remain a binder property. They do not turn an identifier
literal into a binder or make identifier values optional implicitly.

## Canonical rendering

Strings always use quoted canonical syntax:

```datra
"abc"
```

Identifier literals always use `$` syntax:

```datra
$abc
$"Hello, world!"
$(nameExpression)
$($do; _Block; $yield; _Expr)
```

The renderer chooses `$name` only when the payload satisfies bare identifier
syntax. Other concrete payloads use a quoted operand. Dynamic operands retain
parentheses. Structural operands render their fields in source order with one
canonical space after every `;`. Canonical strings never use `$` as a compact
spelling.

`%` has no canonical standalone expression form. It appears only as the
interpolation marker within a quoted string.

## String interpolation lowering

`StringTemplatePart` is a parser-local representation. Before an expression
enters syntax rewriting or evaluation, every quoted string template lowers to
ordinary expressions.

Interpolation holes become calls to the generic host-backed `_show` function.
For a value of type `_T`, `_show` returns `_StrExpr _T`; that result is evaluated
as a subfederation of `Str`. Literal chunks remain string literals. Multiple
parts are joined with the ordinary `,` concatenation AST:

```datra
"%(value1)%(value2)"
```

lowers to:

```datra
(_show value1), (_show value2)
```

and:

```datra
"%(value1) and %(value2)"
```

lowers to:

```datra
(_show value1), " and ", (_show value2)
```

An empty template lowers to `""`. A single part lowers directly to that part.
Adjacent literal chunks may be coalesced. Lowering refers to the host binding
by binding identity, so source shadowing of `_show` cannot change parsed
interpolation semantics.

The lowered tree consists only of ordinary function application,
concatenation, and string literals. `_StrExpr _T` is an ordinary evaluated
target, and its evaluation selects a `Str` subfederation without any
string-specific syntax-hole classification.

## `_StrExpr` and `_show`

The standard library defines the typed string-expression boundary and the
generic conversion function as:

```datra
let val _StrExpr := &T? do yield datra.StrExpr_body
_show := (&_T :: Any; _value :: _T -> _StrExpr _T) datra.show
```

`_StrExpr T` records the source type `T` of a string-producing expression. For
every `T`, evaluation of `_StrExpr T` is evaluation as a subfederation of
`Str`; the type index never changes the resulting string domain. `datra.show`
returns the canonical string presentation used by interpolation while
preserving that source type in the result:

```datra
_show "abc" = "\"abc\""
_show $abc = "abc"
_show $"Hello, world!" = "Hello, world!"
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
payload independently. This follows from ordinary `_show` application and
works for any number of holes; it is not a singleton-template rule.

## Declared syntax representation

A declared syntax pattern is an ordinary `$` expression. For example:

```datra
$($do; _Block; $yield; _Expr)
```

contains ordinary `IdentifierLiteral` nodes at the `$do` and `$yield` literal
positions and ordinary target expressions at `_Block` and `_Expr`. Compilation
records the pattern expression and the locations of its targets.

Function syntax, candidate matching, admissibility, priority, syntax
equivalence, and expansion all consume this structural representation. Rule
metadata may refer to positions in the pattern, but it does not duplicate the
pattern as a template-piece tree.

The outer and inner `$` forms are the same expression family. Their distinct
behavior follows only from operand structure: the outer operand is a sequential
`AtlasMap`, while `$do` and `$yield` have static identifier operands. No
`SyntaxTemplate`, `GreedyStringTemplate`, or host-visible template value is a
second expression construct.

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
source expression. Literal identifier positions compare `IdentifierString`
values. Matching does not compare rendered source text.

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
   identifier literals. `_StrExpr _T` is evaluated through its `Str`
   subfederation for every `_T`.
4. Lists of syntax categories recursively capture their members.
5. Other targets use ordinary evaluation, specification, and subfederation.

The evaluator also owns target-directed normalization. For example, `_Block`
may normalize an application-shaped selection into an `AtlasMap`. The rewrite
stack stores the target, selected source, and completed evidence without
switching on target types.

Admissibility checks structural invariants directly. Neither admissibility nor
matching renders, reparses, or re-lexes a pattern.

## Lexical ownership

- `DatraLanguage.Identifier` owns identifier payloads, bare identifier
  characters, and quoted identifier spelling.
- `DatraLanguage.AST.Operator` owns `$` and the other built-in operator
  spellings.
- The quoted-string parser owns `%(` interpolation syntax.
- The source parser owns mechanical token boundaries and whitespace gaps.
- Rendering uses the AST form and its owning spelling rules.

Declared syntax remains structural throughout matching. Token spelling is
therefore never reconstructed from rendered expressions.

## Migration order

The unified `$` operator changes land first. This phase establishes the
identifier-literal AST and value representation, structural operand
classification, dependent-declaration behavior, canonical rendering, and
structural syntax matching.

The `_StrExpr` and `_show` migration follows only after that `$` foundation is
complete. This second phase adds `datra.StrExpr_body`, defines the generic
`_show` binding, moves interpolation and dynamic `$` onto the shared
`_StrExpr _T` evaluation boundary, and makes every syntax capture carry only
its ordinary target expression. The evaluator then derives capture behavior
from that target; the rewrite pipeline has no separate hole-kind model.

## Standard-library and test surface

The standard library exposes the concepts source programs use:

```datra
_IdentifierLiteral := datra.IdentifierLiteral
let val _StrExpr := &T? do yield datra.StrExpr_body
_show := (&_T :: Any; _value :: _T -> _StrExpr _T) datra.show
```

All greedy syntax declarations in the standard library use `$` with a
sequential operand:

```datra
$($let; _DependentDeclaration) := ...
$($do; _Block; $yield; _Expr) := ...
$(Bool; $or; Bool) := ...
```

Syntax tokens such as `$let`, `$do`, `$yield`, `$or`, and `$to` are identifier
literals. Holes intended to accept bare source identifiers target
`_IdentifierLiteral`. Holes intended to accept character data target `Str` and
require quoted source.

Standard-library declarations, source fixtures, parser expectations,
interpreter cases, and canonical-rendering assertions use the `$(` form for
greedy structural syntax. No standalone `%` prefix compatibility form is
accepted. Quoted interpolation continues to use `%(...)` unchanged.

## Required tests

Parser and AST tests cover:

- `abc`, `$abc`, and `"abc"` as distinct AST forms;
- `$"Hello, world!"` as a quoted identifier literal;
- `$(expression)` as a dynamic identifier expression;
- `$($do; _Block; $yield; _Expr)` as a structural `$` expression;
- rejection of standalone `%` prefix expressions;
- required whitespace at every `;` syntax gap and canonical one-space
  rendering;
- identical dependent-declaration structure for `abc := value` and
  `$abc := value`;
- acceptance of identifier-literal subtypes and rejection of direct `Str`
  expressions as dependent-declaration heads;
- traversal, lowering, source rendering, and canonical round trips for every
  `$` operand shape;
- interpolation lowering to string literals, generic `_show`, and
  concatenation;
- any number of identifier-literal interpolation holes;
- canonical quoted strings.

Interpreter and type tests cover:

- `$abc = $("abc")`;
- quoted identifier payloads that are not valid bare spellings;
- rejection of dynamic identifier operands that cannot satisfy
  `_StrExpr _T`;
- the quoted-string and identifier interpolation equalities above;
- the generic `_show` signature and `_StrExpr _T` result type;
- evaluation of `_StrExpr T` as a subfederation of `Str` for every `T`;
- equivalence between interpolation and its lowered concatenation expression;
- identifier/string membership distinctions;
- specification, reverse specification, and subfederation of concrete and
  structural identifier literals;
- optional binder names independently of optional identifier values.

Declared-syntax tests cover:

- identifier literals at syntax-token positions;
- target-directed `Str` and `_IdentifierLiteral` captures;
- prefix, infix, and multi-field patterns at arbitrary arity;
- one-or-more-whitespace gap matching and canonical one-space rendering;
- generic matching of `do`/`yield`, `if`/`then`/`else`,
  `let`/`def`/`val`, lookup, and comma;
- stable declaration-order candidate selection and rejection ordering;
- absence of render/reparse behavior;
- use of `$(` throughout the standard library, fixtures, and test sources.

## Required invariants

1. `$abc`, `abc`, and `"abc"` are distinct source, AST, and value categories.
2. Bare and quoted identifier spellings produce the same identifier-value
   domain.
3. Identifier literals neither perform lexical lookup nor use string storage.
4. Canonical strings and string reference payloads are quoted.
5. `$` has exactly one prefix-operator spelling and `%` is not a standalone
   expression operator.
6. A sequential `AtlasMap` operand is the sole structural-syntax form of `$`.
7. Every structural `;` gap requires one or more whitespace characters and
   canonically renders with one space.
8. Every interpolation lowers before syntax rewriting.
9. `_show := (&_T :: Any; _value :: _T -> _StrExpr _T) datra.show` is the
   sole interpolation conversion.
10. Declared syntax is stored as ordinary expression structure.
11. Literal syntax positions are `IdentifierLiteral` expression nodes.
12. Every capture position carries one ordinary target expression.
13. The evaluated target is the sole authority for capture behavior.
14. The rewrite stack contains no target-specific capture dispatch.
15. Structural matching does not render, parse, or re-lex expressions.
16. Standard-library operations are not re-encoded as projection cases.
17. Identifier spelling has one owner in `DatraLanguage.Identifier`.
18. Built-in operator spelling has one owner in the operator AST.
19. Declared patterns remain ordinary expressions throughout compilation and
    matching.
20. `abc := value` and `$abc := value` assemble the same dependent declaration.
21. Every other dependent-declaration head subtypes
    `datra.IdentifierLiteral`; `Str` is not a declaration-name domain.
22. Structural `$` expressions subtype `datra.IdentifierLiteral`.
23. Standard-library and test syntax declarations use `$(`; quoted string
    interpolation uses `%(`.
24. `_StrExpr T` is evaluated as a subfederation of `Str` for every `T` and is
    the dynamic string-expression target of `$`.
