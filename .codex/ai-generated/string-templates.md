# String templates and internal `toString`

Status: AI-generated implementation specification.

## Surface grammar

A quoted string is a string template. A template with no interpolation is the
ordinary ASCII string literal that already exists.

```text
StringTemplate  ::= '"' TemplatePart* '"'
TemplatePart    ::= LiteralCharacter | Escape | StringComment | Interpolation
Interpolation   ::= '%' '!'? SimpleExpression '?'?
                  | '%' '!'? '(' Expression ')'
```

`SimpleExpression` is one atomic Datra expression. It includes numeric values,
atomic reserved symbols/types, compact `$string` values, and another quoted
string template. An unreserved alphabetic name is not a simple interpolation:
`"%abc"` is invalid, while `"%String"` and `"%$abc"` are valid. Operators and
other compound expressions must use the parenthesized form. In particular,
`"%(-10)"` is valid and `"%-10"` is not. The optional postfix composes with a
simple interpolation, so `"%Int?"` interpolates the optional integer type. To
place literal question-mark text immediately after a compact interpolation,
escape it: `"%Int\?"` interpolates
`Int` and then appends `?`.

The ordinary `%` form requires the internal `toString` conversion to be
injective. `%!` requests `weakToString`, which also permits a non-injective
conversion. If the ordinary proof exists, `%!x` is definitionally equal to
`%x` and canonicalizes to `%x`; the `!` remains in canonical output only when
the weak form actually widens the accepted conversion.

Examples:

```text
"example%(2 + 2)"
"example%4"
"hello, %"world"!"
"%Nat:%Nat"
```

`%` never denotes literal text directly. A literal percent is written `\%`.
`$` remains literal template text and continues to introduce compact strings
inside interpolations, as in `"%$name"`.
`\?` writes a literal question mark and disambiguates it from the optional
postfix after a compact interpolation. The existing escapes for quote,
backslash, hash, newline, and hexadecimal ASCII bytes retain their meaning.

Compact `$string` spelling permits a leading underscore and single separating
underscores. Consecutive or trailing underscores are invalid: `$_abc` and
`$abc_def` are valid; `$abc__def`, `$abc_`, and `$__abc` are invalid. Strings
with those contents remain available through quoted spelling.

## Comments and delimiters

In template text, an unescaped `#` begins a string comment. It consumes text up
to a newline or the closing quote. A terminating newline remains literal
template text. Interpolation markers inside that comment are ignored. `\#`
writes a literal hash.

Inside `%(` ... `)`, `#` is an expression comment. It ends at a newline or at a
closing `)`. The `)` is not consumed by the comment: it closes the current
parenthesized expression or the interpolation. Comment text and its terminating
newline do not become template output.

Nested quoted templates own their quotes, comments, and interpolation
delimiters. Text produced by an interpolation is never parsed again.

## AST and lowering

The parser produces a `StringTemplate` only when at least one interpolation is
present. A template without interpolation remains `AsciiStringLiteral`.
Adjacent literal characters are stored as one literal part; empty literal parts
are omitted.

Evaluation lowers each part as follows:

```text
literal text  -> ASCII string value
interpolation -> internal toString(interpolated value)
template      -> ordinary comma concatenation of the lowered parts
```

Empty leading and trailing literal parts are identities and are not added as
concat operands. `toString` is an evaluator operation and has no callable
surface-language name. Canonical AST rendering represents the template itself,
not a surface `toString` call.

## `toString` semantics

For a total Atlas map, `toString` returns one ASCII string containing the
canonical source rendering of that value. If the input is already an ASCII
string, only its characters are used: the compact leading `$` or enclosing
quotes are not included.

For a non-total Atlas-map federation, `toString` acts pointwise and preserves
totality:

- every source member is converted independently;
- a total input produces a total string;
- a non-total input produces a non-total string federation;
- `String` maps identically to `String`;
- conversion must be injective over distinguishable federation members.

If injectivity cannot be proved, evaluation fails rather than silently merging
members. A successful conversion carries an injectivity certificate containing
the rendered language facts and its partial inverse. String specification uses
that inverse generically instead of reimplementing canonical parsing for each
type.

`weakToString` uses the same conversion when that certificate can be built. If
it cannot, it constructs a separate weak string federation without an inverse.
Such a value can be rendered and composed where ordinary federation operations
permit it, but specification into it is explicitly rejected rather than
guessing which source member produced a string.

The evaluator currently uses the canonical-AST-only `UnsafeEither` constructor
to exercise this non-injective path in tests. Once Datra functions exist, a
non-injective function should replace that fixture and `UnsafeEither` should be
removed from the AST. Ordinary `|` cannot construct the fixture because it
only accepts alternatives proved to be distinct Atlas maps.

## Template totality and concatenation

A successfully constructed template is total exactly when every interpolation
is total. Its literal components are always total.

Each boundary uses the ordinary Atlas federation concatenation proof. A
template fails if any boundary is colliding or undecidable. In particular:

```text
"%Nat%Nat"       # fails: the split is ambiguous
"%String%String" # fails: the split is ambiguous
"%Nat:%Nat"      # succeeds
"%Bool%Bool"     # succeeds: the finite spellings have unique splits
```

The separated natural template succeeds because `:` cannot occur in the
canonical rendering of a natural. The concatenation proof may use a fixed,
nonempty delimiter when the adjacent string federation is proved not to contain
that delimiter. This also permits repeated separated fields such as
`"%Nat:%Nat:%Nat"`. No such proof is available for `"%String:%String"`, because
an arbitrary string can itself contain `:`.

Finite rendered languages may instead prove a boundary by enumerating all
concatenations and checking that every source pair has a distinct result. This
is why adjacent booleans are valid even without a delimiter: the four strings
`falsefalse`, `falsetrue`, `truefalse`, and `truetrue` uniquely identify their
two components.

String specification inverts the same canonical conversion. For example,
`"true" ~> "%Bool"`, `"falsetrue" ~> "%Bool%Bool"`, and
`"nothing" ~> "%Int?"` select the corresponding Boolean and optional members.

## Required failures

Parsing fails for an unescaped literal `%`, a missing simple expression after
`%`, an empty `%()`, an unterminated interpolation, or an unterminated template.
Evaluation failures from the interpolated expression propagate unchanged.
Failure to prove `toString` injectivity or any template concatenation boundary
produces the dedicated `AmbiguousStringTemplate` interpreter error.
Failure to prove an individual ordinary interpolation injective instead
produces `NonInjectiveStringInterpolation`; `%!` is the explicit opt-in for
that case.
