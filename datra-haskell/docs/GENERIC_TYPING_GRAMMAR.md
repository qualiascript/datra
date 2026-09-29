# Generic Typing Grammar

Status: implementation plan. This document specifies the first implementation
of `::` and `&` generic typing syntax and records the intended later inference
and erasure semantics. The first implementation should not add inference,
erasure, mixed dependent containers, or existential escape.

## Purpose

Generic typing syntax introduces a dependent type binder at the point where
the bound identifier is used. It avoids manually placing a `for` or `with`
binder at the front of a containing type expression.

The two forms have different polarity:

```datra
T :: Bound
&T :: Bound
```

- `T :: Bound` introduces a dependent product binder corresponding to
  `for T of Bound`.
- `&T :: Bound` introduces a dependent sum binder corresponding to
  `with T of Bound`.

The identifier occurrence itself becomes an ordinary reference to the newly
introduced binder.

For example:

```datra
{value? : (T :: Any)} -> T
```

has the phase-one behavior of:

```datra
{for T of Any; value? : T} -> T
```

Similarly:

```datra
SomeValue := {value? : (&T :: Any)}
```

has the phase-one behavior of:

```datra
SomeValue := {with T of Any; value? : T}
```

The term **generic typing grammar** refers to both `::` and `&...::`.

## Surface grammar

Conceptually:

```text
generic-typing-expression := generic-product | generic-sum
generic-product           := generic-name "::" generic-bound?
generic-sum               := "&" generic-name "::" generic-bound?
generic-name              := private-name | required-public-name | optional-public-name
generic-bound             := expression
```

The identifier reuses the existing dependent-binder name handling. There are
three modes:

```datra
_T :: Any   # private and required
T :: Any    # public and required
T? :: Any   # public and optional
```

The same distinction applies to generic sums:

```datra
&_T :: Any
&T :: Any
&T? :: Any
```

This maps directly onto the existing dependent-binder optional-name flag:

- `_T` produces a private required binder;
- `T` produces a public required binder;
- `T?` produces a public optional-name binder.

Private optional `_T?` is not part of this three-way grammar. It should be
rejected rather than acquiring container-dependent behavior.

### Default bound

The bound may be omitted. A postfix `::` means `:: Any`:

```datra
T ::    # T :: Any
&T ::   # &T :: Any
```

The postfix form is recognized when `::` is followed by the end of its
enclosing expression or by a delimiter such as `)`, `}`, `,`, `;`, or `->`.
A line break alone should not be used as the only disambiguator when the next
line can continue an expression.

### Precedence and grouping

The left side of `::` is only the binder identifier, not an arbitrary
expression. Consequently:

```datra
Args (T :: IntLimit)
```

binds `T`, while this must not be interpreted as binding `Args T`:

```datra
Args T :: IntLimit
```

Parentheses should be required when a generic typing expression is used as a
function argument, as in the intended standard-library spelling:

```datra
max := {Args (T :: IntLimit),} -> T do
  # body
```

The right-hand bound should consume the same expression class accepted after
`of` in an explicit dependent binder. Parentheses remain available when the
bound would otherwise meet an enclosing delimiter ambiguously.

## Public and private names

A name without a leading underscore or trailing `?` is public and required:

```datra
T :: IntLimit
&T :: Any
```

During phase one, callers or value constructors provide a public witness
explicitly. For a product binder in an unordered function domain, this means a
required named assignment rather than the optional behavior of `T?`:

```datra
identity := {value? : (T :: Any)} -> T do yield value

yield identity {T := Nat; value := 5}
```

Omitting `T` must fail function matching, just as it does for an explicit
required `for T of Any` binder.

The `T?` spelling is public but optionally named, matching existing dependent
binder behavior. It accepts either its named assignment form or the
corresponding positional witness:

```datra
identity := {value? : (T? :: Any)} -> T do yield value

yield identity (Nat; 5)
yield identity {T := Nat; value := 5}
```

A leading underscore creates a private generic binder:

```datra
_T :: IntLimit
&_T :: Any
```

The intended final behavior is that a private generic witness cannot be
matched explicitly by a caller. It will become useful when generic witness
inference is implemented. Since inference is not part of phase one, successful
runtime examples should use public identifiers. Phase-one tests should still
cover parsing, lowering, privacy preservation, and the expected failure to
call a private generic interface without inference.

## Binder placement and scope

The parser must preserve a generic introduction long enough to hoist its
binder into a containing dependent type container. At the original occurrence,
the expression is replaced with an identifier reference.

For example:

```datra
{Args (T :: IntLimit),}
```

introduces the equivalent container shape:

```datra
{for T of IntLimit; Args T,}
```

The generated binder is placed before the ordinary payload members of its
host container. Multiple generated binders are placed in first-occurrence
order:

```datra
{pair? : Pair (T :: Any) (U :: T)}
```

corresponds to:

```datra
{for T of Any; for U of T; pair? : Pair T U}
```

This order is semantically significant: later generic bounds may reference
earlier generic names. Forward references remain invalid.

### Host container

The nearest enclosing type container owns the generated binders:

- an argument map;
- an ordered Atlas map;
- a map sequence; or
- a function domain.

Grouping parentheses around the generic typing expression do not create a new
host. A genuinely nested map does create a new host, so its binders do not
escape into an outer map.

If a generic typing expression appears in a function domain that has no
existing map container, lowering should synthesize an argument-map domain so
the generated witness and the original domain are both function arguments.
For example:

```datra
Args (T :: Any) -> T
```

has the effective domain:

```datra
{for T of Any; Args T,} -> T
```

If no enclosing function domain or map exists, lowering synthesizes an ordered
dependent container around the enclosing expression:

```datra
List (T :: Any)
```

corresponds to the dependent product family:

```datra
(for T of Any; List T)
```

and:

```datra
Value (&T :: Any)
```

corresponds to:

```datra
(with T of Any; Value T)
```

### Function arrows

A binder introduced in a function domain scopes across `->` into the
codomain, matching the existing behavior of an explicit dependent product:

```datra
{value? : (T :: Any)} -> T
```

The codomain may therefore reference `T`.

A binder introduced only inside a codomain does not scope backward into the
domain. It constructs a dependent type inside that codomain instead.

## AST representation

Do not immediately erase the distinction between generic typing syntax and an
explicit `for` or `with` binder. Later inference and body erasure require the
runtime/compiler to know which binders came from `::`.

Add dedicated AST representation, for example:

```haskell
data GenericBindingKind
  = GenericProductBinding
  | GenericSumBinding

data Expression
  = ...
  | GenericBinding
      GenericBindingKind
      IdentifierString
      Bool -- optional public name
      Expression
```

The exact constructor names may follow existing project conventions. The
important properties are:

1. product versus sum remains explicit;
2. the identifier and bound remain available;
3. required versus optional public naming remains available;
4. the node is distinguishable from explicit `ForBinding`/`WithBinding`;
5. canonical AST rendering and parsing round-trip it;
6. generic occurrences are replaced by `IdentifierReference` nodes after
   their binders have been collected into the host container.

Phase-one semantic helpers may treat a generic product like `ForBinding` and a
generic sum like `WithBinding`, but that equivalence should be implemented
through shared binder inspection functions rather than by discarding origin
metadata.

The following existing logic will need to recognize generic binders:

- dependent-container classification;
- function free-identifier analysis;
- static dependent-domain substitution;
- dependent-sum static conversion and validation;
- dependent-product creation;
- function parameter compilation and dependent validation;
- expression traversal, normalization, rendering, and canonical parsing;
- closure dependency collection;
- optional-name/public-name validation where applicable.

Prefer one shared dependent-binder view over adding parallel constructor cases
independently throughout the interpreter.

## Phase-one semantics

Phase one implements syntax, hoisting, all three identifier modes, and current
dependent-type behavior.

It does **not** implement:

- inference of private generic witnesses;
- removal of generic witnesses from the function body's `it` value;
- removal of generic names from the function body's named scope;
- creation of a specialized internal closure;
- existential witness erasure;
- escape analysis for a private generic sum witness;
- mixed dependent sum/product containers.

Until body erasure is implemented, a generated public product binder may be
visible to the body in the same places as an explicit binder. Retaining the AST
origin marker is what allows the later implementation to change only generic
binders without changing explicit `for`/`with` behavior.

## Mixed products and sums

Generic product and sum introductions may both parse and lower, but a single
host container containing both remains unsupported:

```datra
{left? : (T :: Any); right? : (&U :: Any)}
```

It must fail with the existing structured error:

```text
dependent sums and products cannot be mixed in one type container
```

The result must not depend on which binder occurs first. Supporting alternating
dependent sums and products is a separate type-system implementation.

## Generic sums in phase one

`&T :: Bound` should work anywhere the equivalent explicit required `with T of
Bound` currently works. The primary phase-one integration case is a dependent
sum type whose public witness is supplied explicitly:

```datra
SomeValue := {value? : (&T :: Any)}

assert {T := Nat; value := 5} of SomeValue
```

If an inline generic sum is used in a function-domain form that the existing
function parameter compiler does not support, it may retain the existing
structured rejection for that explicit form. Do not add mixed-quantifier or
existential-function semantics merely to make the syntax succeed in every
position. A named dependent-sum type can still be used as an ordinary function
parameter annotation.

## Future interface-only semantics

The intended follow-up behavior distinguishes generic typing binders from
explicit dependent binders.

For a generic product interface:

```datra
max := {Args (_T :: IntLimit),} -> _T do
  # body
```

the eventual invocation model is:

1. the external function infers or matches `_T`;
2. it validates the remaining arguments using the instantiated `_T`;
3. it removes `_T` from the argument value passed to the body;
4. `_T` is absent from the body's named scope and `it` value;
5. an internal specialized closure evaluates the body;
6. the external function validates the result against `_T`.

Explicit `for`/`with` binders remain body-visible. This is why the AST must
retain generic origin metadata.

The existing separation between the external `ArgumentSchema`,
`argumentSchemaBodyDomain`/`argumentSchemaBodyValues`, and the function's
`prepare`/`invoke` hooks should be reused. A physical second public function
value is not necessarily required; `invoke` can implement the conceptual
outer-wrapper/inner-closure boundary.

For a private generic sum (`&_T`), later work must also prevent `_T` from
escaping as a naked result type. A hidden existential may escape only through
an existential package or another representation that preserves its hiding.

## Parser and lowering plan

1. Add tokens/parsing for `::` and prefix `&` in generic typing position.
2. Parse the left side with the shared three-way dependent-identifier rule:
   private required, public required, or public optional.
3. Parse an omitted bound as `Any` using delimiter-aware lookahead.
4. Produce a generic product/sum marker rather than an ordinary binder.
5. Traverse each generic host expression left-to-right:
   - collect generic markers in first-occurrence order;
   - replace marker occurrences with identifier references;
   - reject duplicate generic declarations in one host;
   - prepend generated binders to the host payload.
6. For a function domain without a map, synthesize an argument map.
7. For a non-function expression without a map, synthesize an ordered map.
8. Preserve function-domain binder scope across the codomain.
9. Extend canonical AST parsing/rendering and generic AST traversal.
10. Ensure no unhosted generic marker can reach evaluation.

Hoisting should be a named normalization pass with focused tests, not a set of
special cases embedded across unrelated parser precedence functions.

## Semantic implementation plan

1. Introduce a shared dependent-binder descriptor exposing:
   - sum or product polarity;
   - explicit or generic origin;
   - identifier;
   - required/optional status;
   - bound expression.
2. Refactor existing binder consumers to use the descriptor where doing so
   removes duplicate `ForBinding`/`WithBinding` case logic.
3. Preserve the parsed required/optional mode in parameter and sum schemas.
4. Preserve public/private identifier rules.
5. Include generic binders in the existing homogeneous/mixed container
   classifier so mixed containers produce `MixedDependentBinders`.
6. Use existing specification and subfederation paths after constructing the
   appropriate dependent product or sum.
7. Leave inference and body erasure explicitly unimplemented.

## Regression test plan

### Parsing and canonical AST

- `_T :: Any`, `T :: Any`, and `T? :: Any` produce private-required,
  public-required, and public-optional generic product binders respectively.
- `&_T :: Any`, `&T :: Any`, and `&T? :: Any` produce the corresponding
  generic sum binders.
- Each of those forms supports postfix `::` with an implicit `Any` bound.
- `_T? :: Any` and `&_T? :: Any` are rejected.
- An arbitrary expression cannot appear to the left of `::`.
- `Args (T :: IntLimit)` replaces the occurrence with `Args T`.
- Multiple binders are hoisted in first-occurrence order.
- A later bound may reference an earlier generic name.
- A forward reference remains rejected.
- A nested map owns its own generic binders.
- A function-domain binder scopes the codomain.
- A scalar function domain is converted into an argument-map domain.
- A top-level scalar generic type is converted into an ordered dependent
  container.
- Canonical AST rendering and parsing round-trip generic-origin metadata.

### Products

- A public generic product witness can be supplied explicitly by name.
- The public witness is required; omitting it fails function matching.
- A `T?` product witness accepts both named and positional forms.
- The dependent argument is validated against the selected witness.
- The dependent result is checked against the selected witness.
- Multiple public generic product witnesses bind in order.
- A private generic product interface cannot be called explicitly and remains
  unavailable until inference is implemented.
- Existing explicit `for T?`, `for T`, and private explicit binders retain
  their behavior.

### Sums

- A public generic sum witness can be supplied explicitly when constructing a
  value.
- Omitting a required public sum witness is rejected.
- A `T?` sum witness accepts both named and positional forms.
- Later fields are validated against the selected witness.
- Multiple generic sum witnesses bind in order.
- Existing explicit `with T?`, `with T`, and private explicit binders retain
  their behavior.

### Required language interactions

Per the repository language-development requirements, cover both generic
products and generic sums with:

- forward specification using `~>`;
- reverse specification using `<~`;
- subfederation using `of`;
- named and positional value forms where the required binder permits them;
- optional names on dependent payload fields, while keeping those distinct
  from required and optionally named generic binders.

### Rejections

- A generic sum and product in either order produce
  `MixedDependentBinders`.
- Mixing a generic binder with an explicit binder of the opposite polarity
  produces the same error.
- Duplicate generated names are rejected structurally.
- A generic marker without a valid host cannot reach the interpreter.
- Invalid private/public matching produces a structured evaluation failure,
  not parser backtracking or silent candidate loss.

## Completion criteria for phase one

Phase one is complete when:

1. product and sum forms parse for `_T`, `T`, and `T?`, with explicit and
   implicit-`Any` bounds;
2. generated binders preserve private-required, public-required, or
   public-optional mode and retain generic-origin metadata;
3. binders hoist and scope according to this document;
4. public product and sum examples work with explicit witnesses;
5. private spellings are represented but do not pretend to have inference;
6. mixed containers fail with `MixedDependentBinders` independent of order;
7. specification, reverse specification, and subfederation regressions pass;
8. existing explicit dependent binder behavior remains unchanged;
9. focused parser/interpreter tests pass;
10. the full non-Liquid test suite passes once, serially, as final validation.
