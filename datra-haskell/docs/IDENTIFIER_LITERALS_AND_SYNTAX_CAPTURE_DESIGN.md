# Identifier Literals and Syntax Capture

## Purpose

This design separates identifier values from strings and makes declared-syntax
capture depend on the declared target type. It defines the `$` operator, the
AST and evaluated representation of identifier literals, canonical rendering,
syntax-template literals, hole capture, standard-library migration, and the
required regression coverage.

String interpolation has one uniform internal lowering: literal chunks remain
strings, interpolation holes become calls to the ordinary `to_string` function,
and the resulting strings are joined by ordinary `,` concatenation. There is
no singleton-hole normalization rule and no internal string-template capture
machine.

## Semantic distinctions

Datra has three distinct concepts:

| Source | AST meaning | Evaluation |
| --- | --- | --- |
| `name` | `IdentifierReference "name"` | Resolve `name` in the lexical scope. |
| `$name` | `IdentifierLiteral "name"` | Produce the identifier named `name` as a value. |
| `"name"` | `AsciiStringLiteral "name"` | Produce a list of characters. |

`IdentifierString` is the validated name payload shared by references and
identifier literals. It is not an expression and is never used as a substitute
for a string value.

The following are language invariants:

1. An identifier reference and an identifier literal are different AST nodes.
2. An identifier literal and a string literal are different values.
3. `$name` does not resolve `name` in the lexical scope.
4. `$name` does not inhabit `Str` merely because its payload can be printed as
   characters.
5. `"name"` does not inhabit `datra.IdentifierLiteral` merely because its
   contents are a valid identifier spelling.
6. Identifier-literal equality compares validated identifier names.
7. Identifier literals participate in ordinary specification and
   subfederation operations as identifier values, not through a string
   compatibility path.

## The `$` operator

`$` is the identifier-literal prefix operator. It is not an alternate spelling
for a string and is not implemented by the string-literal parser.

The operator accepts either a bare identifier operand or an expression whose
evaluated value is a string:

```datra
$abc
$(nameExpression)
$"abc"
```

`$abc` is the static form. The parser validates `abc` and constructs an
`IdentifierLiteral` directly. It must never construct an
`IdentifierReference` or an `AsciiStringLiteral` as an intermediate semantic
representation.

The expression form evaluates its operand, requires one string value, validates
that string with the ordinary identifier grammar, and produces the same
identifier value as the equivalent static form. A literal operand may be
validated and folded during parsing or AST normalization:

```datra
$abc = $("abc")
```

An operand which is not a string, or a resulting string which is not a valid
identifier, is rejected at the first point where that fact is known. There is
no fallthrough to lookup, string conversion, or failed syntax matching.

Parentheses retain their ordinary grouping meaning. The distinction between
`$abc` and `$(abc)` is therefore semantic: the first quotes the written name
`abc`; the second evaluates the reference `abc` and converts its resulting
string to an identifier.

`$` must be added to the operator vocabulary and handled by the ordinary AST
operator traversal, normalization, lowering, rendering, and parsing paths. It
must not be recognized with string comparisons in syntax rewriting.

## Uniform string-interpolation lowering

`StringTemplatePart` is a parser-level representation only. Before an
expression enters syntax rewriting or evaluation, every quoted string template
is lowered to ordinary expressions:

```datra
"%(value1)%(value2)"
```

lowers to the equivalent of:

```datra
(to_string value1), (to_string value2)
```

Literal chunks participate in the same concatenation:

```datra
"%(value1) and %(value2)"
```

lowers to:

```datra
(to_string value1), " and ", (to_string value2)
```

The spaces belong to the literal middle chunk and are preserved exactly.

The lowering rules are structural:

```haskell
lowerPart (StringTemplateLiteral text) = AsciiStringLiteral text
lowerPart (StringTemplateInterpolation value) =
  FunctionApplication datraToStringFunction value
```

Multiple lowered parts are combined with `MapConcatenation`, the AST form of
`,` concatenation. An empty template lowers to `AsciiStringLiteral ""`; a
single part lowers to that part without inventing an empty operand. Adjacent
literal chunks may be coalesced, but no behavior depends on the number of
interpolation holes.

`datraToStringFunction` above is an AST reference to the host binding,
constructed from
the host binding identity rather than recognized by rendered source text. The
lowering cannot be affected by a source declaration which shadows the public
name `to_string`.

No post-parser `StringTemplate`, `StringTemplatePart`, interpolation-hole kind,
or template evaluator remains. Concatenation, function application, ordinary
evaluation, and ordinary specification own the resulting expression.

## Identifier literals in string interpolation

The `to_string` call generated for a string interpolation preserves the explicit
canonical representation of an interpolated string literal. Its quote
characters therefore become part of the resulting string:

```datra
"abc" =/= "%("abc")"
"%("abc")" = "\"abc\""
```

This follows from the requirement that string captures have explicit quotes.
The generated `to_string` call converts the quoted string expression to its
canonical presentation; it does not unwrap that expression into its character
payload.

Quoted string interpolation has a different boundary. When the value in an
interpolation hole is an identifier literal, the interpolation contributes the
literal's `IdentifierString` contents:

```datra
"%($abc)" = "abc"
$abc = $("%($abc)")
"%($abc)-%($def)" = "abc-def"
$abcdef = $("%($abc)%($def)")
```

The second equality is ordinary composition: the inner string interpolation
produces `"abc"`, and the outer `$` converts that string to the identifier
literal `$abc`. It is not a special `$` rewrite and does not equate identifier
literals with strings.

The rule applies independently to every identifier-literal interpolation hole,
including templates with multiple holes and surrounding literal chunks.
Lowering first produces `to_string` applications and `,` concatenation like
every other interpolation. Ordinary constant reduction may then replace
`to_string $abc` with `"abc"` and coalesce adjacent literal operands. Dynamic
identifier literals follow the same path once their names are known. No
singleton-template special case is involved, and other interpolation values
retain their ordinary canonical string conversion.

## The ordinary `to_string` function

The Datra host provides one total function:

```datra
datra.to_string : Any -> Str
```

The standard library exposes it as `to_string` with the same domain and
codomain. String-interpolation lowering calls the host binding directly;
ordinary programs call the standard-library name.

`to_string` returns the canonical string presentation used by interpolation.
In particular:

```datra
to_string "abc" = "\"abc\""
to_string $abc = "abc"
```

The identifier-literal case returns the validated `IdentifierString` payload,
without `$`. This is ordinary function semantics and is why any number of
identifier-literal interpolation holes lower uniformly. Existing internal
string conversion code is consolidated behind this host function; a separate
identity conversion for string-producing values would violate the explicit
quote rule and is removed.

## AST and evaluated representation

The source AST needs an explicit identifier-literal form. Its payload must
distinguish a validated static name from an unevaluated dynamic operand without
encoding either case as a string literal:

```haskell
data IdentifierLiteralOperand expression
  = StaticIdentifier IdentifierString
  | EvaluatedIdentifier expression

data Expression
  = ...
  | IdentifierReference IdentifierString
  | IdentifierLiteral (IdentifierLiteralOperand Expression)
```

The exact constructor names may follow the surrounding module conventions, but
the static `$abc` form must be represented by the `IdentifierLiteral` branch.

`OperatorExpression` keeps the same semantic split. The existing
`IdentifierReferenceValue` remains the lowered lexical-reference node; it must
not be renamed to `IdentifierLiteral` or reused by `$`. The new source node has
its own lowered form:

```haskell
IdentifierReferenceValue IdentifierString
IdentifierLiteralValue IdentifierString
```

Evaluation of `IdentifierLiteralValue` produces a dedicated value form
containing `IdentifierString`; it does not produce an ASCII string and does not
retain a lexical reference:

```haskell
IdentifierLiteralForm IdentifierString
```

Every generic AST operation must cover the new node:

- normalization and child traversal;
- source and canonical rendering;
- source-to-operator lowering;
- evaluation and canonical semantics;
- equality, specification, and subfederation;
- diagnostic rendering and source spans;
- generators, shrinkers, and round-trip tests.

The post-parser expression AST does not need `StringTemplate` or
`StringTemplatePart`: their information has already been expressed with
`AsciiStringLiteral`, `FunctionApplication`, and `MapConcatenation`.

Optional-name syntax remains a property of binders and dependent arguments.
It does not turn an identifier literal into a binder. Specification (`~>` and
`<~`) and subfederation (`of`) treat an identifier literal as an ordinary
first-class value. At minimum, the following distinctions must hold:

```datra
$abc of datra.IdentifierLiteral
"abc" of Str
```

are true, while the cross-category cases are false.

## Canonical rendering

Canonical strings always use the quoted form. `renderAsciiStringLiteral` must
never select `$` as a compact representation:

```datra
"abc"
```

Identifier literals use `$` in source rendering. A static literal uses the
compact form when its validated payload allows it:

```datra
$abc
```

Canonical AST notation renders name fields as quoted payloads. In particular,
an identifier reference is rendered as:

```text
(ref "abc")
```

and never `(ref $abc)`, because `$abc` is now an expression with different
semantics. The identifier-literal AST form likewise has its own canonical
constructor form with a quoted name payload. Parsing canonical AST notation
must reconstruct the same constructor rather than relying on a source-level
`$` token.

`renderIdentifierString` remains appropriate for rendering a bare source
reference. It must not be reused to render string values or canonical AST
fields.

## Declared syntax literals

An identifier literal inside a greedy syntax declaration denotes a literal
identifier token:

```datra
%($do; _Block; $yield; _Expr)
%(Bool; $or; Bool)
```

The literal pieces are `do`, `yield`, and `or`. `_Block`, `_Expr`, and `Bool`
are hole targets. `$do` is therefore not a string-valued interpolation, and
`Bool` is not inferred to be a literal from its spelling.

The syntax-template representation reflects this distinction directly:

```haskell
data SyntaxPiece target
  = SyntaxLiteral IdentifierString
  | SyntaxHole target
```

`SyntaxLiteral String` is replaced by the validated `IdentifierString`
payload. An explicit syntax-template literal is compiled only from an
`IdentifierLiteral` AST node. The implicit application rule for a simple
declaration uses the declaration's already validated head `IdentifierString`.
An ordinary `IdentifierReference` in an explicit template remains a hole
target. A quoted `AsciiStringLiteral` remains a string value and is never
silently promoted to an identifier token.

The syntax declaration compiler must consume the structured greedy-template
AST. It must not translate the declaration through `StringTemplatePart`,
rendered source text, or compact string spellings. Optional and alternative
template structure remains AST structure until syntax branches are compiled.

`_IdentifierLiteral := datra.IdentifierLiteral` is the standard-library
name for the identifier syntax/value category. A hole with that target accepts
a valid bare identifier source form. A hole with target `Str` accepts a quoted
string source form; it does not accept a bare identifier or an identifier
literal.

## One target-directed hole abstraction

A syntax hole carries its declared target expression and nothing else. The
following constructor family is removed:

- `ExpressionSyntaxHole`;
- `BlockSyntaxHole`;
- `FunctionBodySyntaxHole`;
- `DeclarationSyntaxHole`;
- `DependentArgumentSyntaxHole`;
- `IdentifierLiteralSyntaxHole`;
- `StringLiteralSyntaxHole`;
- `ValueSyntaxHole`.

There is no `SyntaxHoleKind`, `specializeSyntaxHoleKind`, or parallel
classification pass. There is also no `StringLiteralSyntaxHole`,
`valueProducesStrings`-based hole specialization, or `canonicalValueCapture`
branch dedicated to interpolation. These representations duplicate ordinary
function application, concatenation, and target information while allowing
parser concerns to leak into the rewrite stack.

The stack retains only the target expression, the structurally selected source
expression, and completed capture evidence. It asks the evaluator to capture
that source against the target. The evaluator evaluates the target in the exact
candidate context and applies one target-directed operation:

1. Syntax-category targets preserve and validate AST structure.
2. `datra.IdentifierLiteral` accepts the bare `IdentifierReference` source
   form and rejects strings and identifier-literal expressions as source-token
   captures.
3. String-producing syntax captures operate on the already lowered quoted
   expression and use ordinary evaluation and selection; they do not install a
   string-hole kind.
4. Lists of syntax categories recursively capture their members.
5. Every other target evaluates the selected expression and applies ordinary
   specification/subfederation selection.

The evaluator also owns target-specific normalization. For example, `_Block`
may normalize a selected application phrase into `AtlasMap`, while `_Expr`
returns the selected subtree unchanged. The stack neither switches on target
types nor knows which AST constructors implement a category.

Literal-token matching does not use the hole path. A compiled
`SyntaxLiteral name` structurally matches the neutral source token
`IdentifierReference name`. This is name comparison over `IdentifierString`,
not rendered-source comparison and not string-value equality.

Completion requires deleting the ad-hoc syntax-hole matching pipeline rather
than retaining it behind a generic constructor. Structural matching selects an
AST region, ordinary rewriting rewrites it, and the evaluator applies the
declared target. String interpolation has already become ordinary `to_string`
applications and concatenation before this boundary.

## Minimal syntax projection

`SyntaxTemplateProjection` handles only neutral AST structure that cannot be
expressed by declarations in `std.datra`. It is not a second parser and does
not reconstruct source text.

The module must not contain:

- `renderSourceExpression` followed by neutral reparsing;
- identifier or operator recognition by `String` comparison;
- `splitAtLiteral`, `expressionFacts`, `ruleLiteralsPresent`, or
  `literalBoundaryCandidate`-style indexing;
- special candidates for `let`, `def`, `val`, `do`, `yield`, lookup, comma, or
  any other named standard-library operation;
- `lookupLiteralCandidates` or `literalConcatenationBoundaryCandidates`;
- a separate `GreedyStringTemplate` mode in the rewrite stack;
- post-parser `StringTemplate` inspection or interpolation-hole dispatch;
- marker identifiers such as `_datra_syntax_hole` or
  `_datra_syntax_shape_child`.

Application spines, prefix operators, infix operators, optional structure, and
arbitrary arity are matched through their neutral AST constructors. `~` is the
ordinary lookup prefix operator and `,` is the ordinary concatenation infix
operator. Neither is recovered from spelling heuristics. Helpers such as
`applicationFrom` and `applicationPhrase` belong in a neutral AST utility only
if the generic structural algorithm still needs them; they do not justify
literal-specific projection paths.

Admissibility validation operates on the compiled structural template. It does
not prove stability by rendering witnesses, parsing them, and projecting them
back. Diagnostics such as `NeutralSyntaxTemplateParseFailure`,
`SyntaxTemplateProjectionLoss`, and `UnstableSyntaxTemplateProjection` should
be removed when their render/reparse mechanism is removed; any remaining
admissibility failures must state a structural invariant directly.

## Standard-library migration

The standard library exposes only concepts used by source programs:

```datra
_IdentifierLiteral := datra.IdentifierLiteral
let val to_string := (Any -> Str) datra.to_string
```

`IdenStr`, the public `Template` alias, and an unused `_SyntaxTemplate` alias
are absent. The host may retain an internal syntax-template representation, but
the standard library does not use it as a user-level string type.

### `IdenStr` migration

`IdenStr` was the federation of strings accepted by the compact `$name`
spelling. That model is obsolete because `$name` now produces an identifier
literal rather than a string. The following legacy representations remain
deleted and must not be restored as compatibility aliases:

- `IdentifierValueType`;
- `IdentifierValueTypeValue`;
- `IdentifierValueTypeForm`;
- `IdentifierValueTypeAtlasMapFederation`;
- `makeIdentifierValueType`;
- the reserved `IdenStr` spelling and `datra.IdenStr` host binding.

Source and tests which used `IdenStr` are migrated by intended meaning:

- a `$name` value becomes an identifier literal and belongs to
  `datra.IdentifierLiteral`;
- a declared-syntax hole intended to accept a bare identifier uses
  `_IdentifierLiteral`;
- conversion of an identifier literal to characters uses `to_string` and
  produces the identifier payload without `$`;
- actual character data uses `Str` and explicit quotes;
- template-injectivity tests use the ordinary `to_string` plus `,`
  concatenation lowering instead of an `IdenStr`-specific codec.

The stale `IdenStr` cluster in parsing, interpreting, standard-library, and
Datra-type-law tests is migrated as one semantic unit. In particular, a direct
test reference to the removed `IdentifierValueType` constructor is evidence of
an unmigrated `IdenStr` test, not a reason to reintroduce that constructor.

Every existing `$` occurrence must be classified by meaning rather than
replaced mechanically:

- syntax tokens such as `$let`, `$do`, `$yield`, `$or`, and `$to` remain
  identifier literals in syntax declarations;
- identifier-valued tags such as `$up`, `$down`, `$Complement`, `$def`, and
  `$val` remain identifier literals when their domains are identifier-valued;
- paths, messages, names used as character data, and other actual strings move
  to quoted literals;
- holes intended to accept bare source identifiers use
  `_IdentifierLiteral`, never `Str`;
- holes intended to accept string values use `Str` and require quoted source.

Host bindings and primitive names use AST constructors and primitive values,
not comparisons against rendered names such as `"datra.IdentifierLiteral"`.
There is no `BuiltinMetaType`; syntax categories are ordinary primitive target
values interpreted by the evaluator.

The host owns the implementation of `datra.to_string : Any -> Str`. The stdlib
binding publishes its ordinary typed interface. Interpolation lowering refers
to the host binding directly so bootstrap order and user shadowing cannot alter
the meaning of a parsed string.

## Test migration and regressions

Tests are migrated according to the same semantic categories as the standard
library. A passing test which relied on `$name` as a compact string spelling is
stale and must be rewritten, not preserved through compatibility behavior.

No test source, generator vocabulary, canonical expectation, or direct AST
construction retains `IdenStr` or an `IdentifierValueType` constructor after
the migration.

Parser and AST tests cover:

- `abc` produces `IdentifierReference`;
- `$abc` produces the static `IdentifierLiteral` AST branch;
- `"abc"` produces `AsciiStringLiteral`;
- `$(abc)` retains a dynamic identifier-literal operand;
- identifier literals participate in traversal, normalization, lowering, and
  canonical AST round trips;
- every static identifier literal inside string interpolation lowers to its
  name payload without `$` or quote characters, including templates with
  multiple identifier-literal holes;
- every parsed string template lowers to `AsciiStringLiteral`, host
  `to_string` applications, and `MapConcatenation`, with no post-parser
  `StringTemplate` node;
- strings always render with quotes;
- canonical references use quoted payloads;
- invalid static identifier spellings fail during parsing.

Interpreter and type tests cover:

- `$abc = $("abc")`;
- `"abc" =/= "%("abc")"` and `"%("abc")" = "\"abc\""`;
- `"%($abc)" = "abc"` and `$abc = $("%($abc)")`;
- `"%($abc)-%($def)" = "abc-def"` and
  `$abcdef = $("%($abc)%($def)")`;
- `to_string` has domain `Any`, codomain `Str`, and is exposed by both the host
  and standard library;
- `"%(value1)%(value2)"` behaves exactly like
  `(to_string value1), (to_string value2)`;
- `"%(value1) and %(value2)"` behaves exactly like
  `(to_string value1), " and ", (to_string value2)`;
- `$abc` is a member of `datra.IdentifierLiteral` and not `Str`;
- `"abc"` is a member of `Str` and not `datra.IdentifierLiteral`;
- a dynamic non-string operand fails eagerly;
- a dynamic string with invalid identifier spelling fails eagerly;
- identifier literals interact with specification, reverse specification, and
  subfederation without string coercion;
- optional binder names remain distinct from optional identifier values.

Declared-syntax tests cover:

- `$or` compiles as a literal identifier token;
- `Bool` and `Str` compile as target holes;
- a `Str` hole accepts quoted string syntax and rejects both a bare identifier
  and `$identifier`;
- an `_IdentifierLiteral` hole accepts a valid bare identifier and rejects a
  quoted string;
- prefix, infix, and multi-piece templates match arbitrary arity without
  operation-specific candidates;
- `do`/`yield`, `if`/`then`/`else`, `let`/`def`/`val`, lookup, and comma pass
  through the generic structural matcher;
- declaration-order candidate selection and rejection ordering remain stable.

Fixtures and expected diagnostics are updated with canonical quoted strings
and references. Tests for removed aliases or hole constructors are deleted only
when the behavior itself is obsolete; tests for retained behavior are migrated
to the target-directed capture path.

## Implementation order

1. Add the identifier-literal AST/operator/value representation and complete
   its traversal, lowering, evaluation, equality, specification, and
   subfederation behavior.
2. Add `datra.to_string : Any -> Str`, expose it from the standard library, and
   consolidate canonical value-to-string semantics behind it.
3. Parse `$` into identifier-literal forms and lower all quoted string
   templates to string literals, host `to_string` applications, and `,`
   concatenation.
4. Change syntax literals from `String` to `IdentifierString` and compile them
   from `IdentifierLiteral` nodes.
5. Remove `SyntaxHoleKind` and the specialized capture/classification pipeline;
   structural selection carries only the declared target and selected AST.
6. Reduce `SyntaxTemplateProjection` and admissibility to structural AST
   operations; delete render/reparse and named-operation branches.
7. Migrate the standard library by semantic `$` category.
8. Migrate focused parser, AST, evaluator, syntax, and stdlib tests.
9. Resume the syntax-rewrite failure documented in
   `SYNTAX_REWRITE_ALGORITHM_DESIGN.md`, then stop at and report the next
   distinct failing issue.

## Required invariants

1. `$abc`, `abc`, and `"abc"` are three distinct source and AST forms.
2. Static identifier payloads are validated `IdentifierString` values.
3. No identifier literal is represented as an ASCII string.
4. No identifier literal performs lexical lookup.
5. Canonical strings are always quoted.
6. Canonical reference payloads are always quoted.
7. Syntax literals carry `IdentifierString`, not `String`.
8. Every syntax hole carries exactly one target expression.
9. The evaluated target is the sole authority for capture behavior.
10. The rewrite stack contains no target-specific or constructor-specific hole
    dispatch.
11. Syntax projection neither renders nor reparses source.
12. Standard-library operations are not re-encoded as projection cases.
13. Every quoted string template lowers to ordinary literals, `to_string`
    applications, and `,` concatenation before syntax rewriting.
14. `to_string` is the sole canonical value-to-string operation used by
    interpolation and has type `Any -> Str`.
15. Every identifier-literal interpolation hole lowers independently through
    `to_string` to its identifier payload.
16. No ad-hoc syntax-hole matching or interpolation-hole evaluator remains.
