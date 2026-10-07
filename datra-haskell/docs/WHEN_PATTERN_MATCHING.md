# `when` Pattern Matching

Status: design proposal.

## Motivation

Datra currently has a dedicated `if` conditional whose surface syntax lowers
to a conditional AST node. This gives Boolean conditions a separate control
mechanism even though Datra already has the ingredients for a more general
one: federations, specification, structural products, named values, and
declarative syntax templates.

`when` should become the language's fundamental conditional and pattern-
matching expression. It supports both ordinary Boolean conditions and
structural pattern tests, evaluates them in source order, and sends every
successful test to an explicit result branch. The existing `if` spelling can
then be removed temporarily and later reintroduced as syntax sugar for
`when`, without retaining a separate conditional evaluator.

The immediate design target is to express `Numbers.max` without `if`:

```datra
max := {Args IntLimit,} -> IntLimit? do
  yield it !? fun {candidate? : IntLimit; remaining? : List IntLimit} -> IntLimit do
    yield when it
      in Infinity; *
      in *; ()
      candidate >= (next := this remaining[0; 1..])
        then candidate
      else next
```

This example combines two structural matches and one Boolean condition. The
three tests share `then candidate`: they are alternatives, evaluated from top
to bottom, and the first successful test selects that result. If all three
fail, `else next` is evaluated.

## General grammar

Conceptually, the grammar is:

```text
when-expression := "when" expression arm+ terminal
arm             := test+ "then" expression
test            := "in" pattern
                 | expression
terminal        := "else" expression
                 | "end"
```

Parentheses around the expression following `when` are ordinary expression
grouping, not mandatory punctuation.

Each arm contains one or more tests followed by exactly one `then` result.
All tests since the previous `then`, or since the beginning of the `when`,
belong to that result. Consequently:

- `then` cannot appear before at least one regular or `in` test;
- multiple tests preceding one `then` are alternatives, not conjunctions;
- every nonterminal group of tests must be followed by `then`;
- the last branch before `else` or `end` must be a `then` branch;
- `else` and `end` are mutually exclusive terminal forms; and
- no branch follows the terminal form.

The scrutinee is evaluated once. As with a function body, its complete value
is bound to `it`, and statically known named members are made available in the
`when` body. For example, a scrutinee with the structure
`{a : Int; b : Int}` makes `it`, `a`, and `b` available. Name extraction must
preserve the existing distinction between an optional name (`a? : T`) and an
optional value (`T?`).

Arms and their tests are considered in source order. A successful test
evaluates its arm's `then` expression and completes the `when`; later tests and
arms are not evaluated. A failed test proceeds to the next test. Reaching
`else` means every preceding test failed.

Regular tests are conditional branches. Their expressions must evaluate to
`Bool`, and they succeed only when the result is `true`. Names introduced
while evaluating a regular test follow the existing condition-local binding
rules. In particular, a name is available only on paths on which its defining
test was evaluated. This permits `next` in the `max` example to be used by the
`else` result: reaching `else` proves that the comparison which defines
`next` was evaluated.

When multiple tests share a `then`, that result may use only names available
on every successful path to it. A name introduced by the final test is not
available when an earlier test can select the same result without evaluating
that definition.

## `in` branches

An `in` test implicitly matches the `when` scrutinee:

```datra
when value
  in Pattern
    then result
  else fallback
```

reads as "when `value` is in `Pattern`." Its semantics should reuse Datra's
ordinary specification and subfederation machinery, but pattern matching must
retain the distinction between a refuted relation and an undecidable one:

- a proved match selects the corresponding `then` branch;
- a refuted match proceeds to the next test; and
- an undecidable match produces a pattern-matching diagnostic rather than
  silently behaving as `false`.

Collapsing undecidability into failure would make control flow change when a
new decision procedure is added. Pattern matching therefore cannot be
implemented merely by evaluating the current Boolean `of` expression.

Patterns preserve Datra's structural distinctions. In particular, sequencing
with `;` is not interchangeable with concatenation using `,`. In the `max`
example, `it` is a two-position sequence, so:

```datra
in Infinity; *
```

matches a sequence whose first position is `Infinity`, while:

```datra
in *; ()
```

matches a sequence whose second position is the empty list. Pattern arity and
product structure must agree with the scrutinee.

The initial design does not require `in` patterns to introduce new lexical
names. The scrutinee binding supplies `it` and its statically known named
members. A successful match may refine the type or specification of `it`
inside the selected arm; pattern capture syntax can be considered separately
if a later use case requires it.

## Wildcard `*`

Outside a pattern, `*` remains Datra's existing positional skip value and
multiplication symbol. Inside an `in` pattern, a bare `*` is a wildcard for
exactly one structural position.

The wildcard:

- accepts any value in that position;
- does not introduce a binding;
- preserves the surrounding sequence or concatenation shape;
- does not consume a variable number of positions; and
- exists only in pattern context.

This should be represented explicitly in the pattern grammar rather than by
globally reinterpreting the skip value or lowering every wildcard to `Any`.
An explicit pattern node keeps ordinary skip semantics intact and lets the
coverage checker reason about wildcard positions. A future spelling for
matching the literal skip value inside a pattern can be designed separately;
ordinary equality remains available in the meantime.

## Default and exhaustive forms

A `when` expression has one of two terminal forms.

### Default branch

```datra
when value
  in Pattern
    then result
  else fallback
```

`else` is the ordered default. It is evaluated only when every regular and
`in` test fails, and it requires no exhaustiveness proof.

### Exhaustive termination

```datra
when value
  in false
    then falseResult
  in true
    then trueResult
end
```

`end` supplies no fallback expression. The compiler must prove at compile
time that the preceding patterns cover every value admitted by the static
type of the scrutinee. If coverage is refuted or undecidable, compilation
fails and the programmer must add a missing pattern or use `else`.

Coverage is pattern-specific. Ordered patterns may overlap, so the compiler
must not assume that their union is an ordinary distinct Datra federation.
The first implementation may be conservative and prove only cases supported
by the available decision procedures, including whole-input wildcards,
finite alternatives such as `Bool`, structural products, and an ordinary
proved inclusion in a single pattern.

Arbitrary regular Boolean tests generally do not contribute to exhaustive
coverage. Proving that program predicates collectively cover a type would
require a general theorem prover. The compiler may recognize a literal
`true` test or similarly elementary tautologies, but otherwise an exhaustive
`when` should rely on `in` patterns.

All reachable `then` expressions, and the `else` expression when present,
must satisfy the expected result type of the `when`. With `end`, the proven
absence of an unmatched path means there is no implicit unit-valued result.

## String-template grammar integration

The declarative syntax system compiles flat templates from a direct string or
from a compile-time-materializable inhabited total map of strings supplied to
`~%`. Every string is checked for literal characters that the neutral parser
cannot retain before the syntax rules are installed. Each template becomes a
linear sequence of literals and holes. That representation is sufficient for
fixed-arity forms such as:

```datra
if condition then consequent else alternative
```

but a `when` contains any positive number of tests and arms. It should be a
design target for expanding `~%` from "compile these flat strings" to "compile
the syntax language represented by this federation of strings."

Abstractly, the `when` syntax language contains recursive choice and
sequencing:

```text
Test     = InTest | RegularTest
Arm      = Test+ ThenResult
Terminal = ElseResult | End
When     = WhenHead Arm+ Terminal
```

A richer compiled template representation therefore needs at least literal,
hole, sequence, choice, and repetition or recursion. The current flat
`SyntaxTemplate [SyntaxPiece]` is the special case containing only sequence.
A string federation should retain this grammar structure rather than being
eagerly expanded into templates for one branch, two branches, three branches,
and so on.

Matching a recursive grammar also produces structured captures rather than a
flat argument list. A successful `when` syntax match should conceptually
produce:

```text
{
  scrutinee;
  arms: List {
    tests: InhabitedList Test;
    result: Expression
  };
  terminal: Else Expression | End
}
```

The `when` syntax implementation can lower this capture value to the core
matching AST. The grammar is responsible for placement rules such as requiring
tests before `then` and a final `else` or `end`; semantic checking remains
responsible for Boolean types, valid patterns, name scope, result types, and
exhaustiveness.

Although this language originates in string federations, matching should
continue against the neutral AST rather than flattening source back into raw
text. AST-aware matching preserves expression boundaries, nested `when`
ownership, comments, and the distinction between a delimiter and the same
word inside a nested expression.

Template compilation must also preserve deterministic inversion. If two
grammar paths can consume the same phrase but produce different captures,
the grammar should be rejected as overlapping or undecidable unless an
explicit ordered-choice rule resolves the ambiguity. Literal-prefixed forms
such as `in Pattern` should be distinguishable from the general regular-test
form before an unrestricted expression hole is allowed to consume them.

Syntax declarations are needed before ordinary evaluation rewrites their
containing scope. Consequently, federation-valued template expressions must
be compile-time discoverable rather than arbitrary runtime `Str` values. The
precise set of admissible federation constructors and recursive definitions
is left to the string-template parser design.

## Refactoring `if`

Once `when` is operational, the existing surface `if` syntax and its direct
conditional lowering should be removed while library code and tests migrate
to `when`. `if` can then return as declarative sugar over a regular `when`
test with the unit value as an otherwise irrelevant scrutinee:

```datra
if condition then consequent else alternative
```

is conceptually:

```datra
when ()
  condition
    then consequent
  else alternative
```

The two-branch form therefore uses the same ordered matching evaluator as all
other conditional control flow. The existing form without an explicit
`else` can lower with `else ()`:

```datra
if condition then consequent
```

becomes conceptually:

```datra
when ()
  condition
    then consequent
  else ()
```

This desugaring should be hygienic. A source-level `when ()` normally binds
its unit scrutinee to `it`, but introducing that binding while expanding `if`
must not unexpectedly hide an enclosing function body's `it`. The lowering
may therefore use a compiler-private scrutinee binding while otherwise
constructing exactly the same core matching form.

The intended end state has one core control-flow mechanism: `when`. `if` is a
standard-library spelling that constructs it, not a parallel AST node with an
independent inference and evaluation path.

## Initial implementation boundaries

The first implementation should prioritize the behavior exercised by the
`max` design target:

- one scrutinee evaluated once;
- function-body-style `it` and named-member binding;
- ordered regular and `in` tests;
- several tests sharing one `then`;
- positional `*` wildcards in sequential patterns;
- a final `else` result;
- condition-local bindings such as `next`; and
- result checking against the surrounding function codomain.

Exhaustive `end`, richer coverage proofs, branch-local type refinement, and
the recursive string-federation grammar should follow the same semantic model
even if they are delivered incrementally.
