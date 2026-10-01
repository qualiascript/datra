# Parser bootstrap: remaining work

This document tracks only the work that remains before the parser bootstrap is
complete. Delete it when the completion criteria at the end are satisfied.

## Current verified baseline

The full non-Liquid suite has four green suites:

```sh
cabal test all
```

- `datra-core-test`: 35 passed, 0 failed
- `datra-cli-test`: 10 passed, 0 failed
- `datra-parsing-test`: 4 passed, 0 failed
- `datra-types-test`: 32 passed, 0 failed

The interpreter suite currently has 48 failures:

```sh
cabal test datra-interpreting-test \
  --test-show-details=direct \
  --test-options='--hide-successes'
```

- `datra-interpreting-test`: 528 passed, 48 failed

Overall: 609 passed and 48 failed out of 657 tests.

This is a failure inventory, not a count of confirmed implementation defects.
The parser refactor changed which source forms are valid and where declarative
syntax establishes expression boundaries. Some tests may still encode the old
grammar or old canonical form. Each failure therefore remains untriaged until
its expected behavior has been checked against the current architecture.

No compiler warnings were emitted by these runs.

## Architectural constraints

- Expressions and syntax declared in `libs/std.datra` must use the same parser,
  rewriting, evaluation, and typing paths as user declarations. Do not add
  special handling for a standard-library expression or identifier.
- Do not touch any other document in `docs/`.
- A newline is a separator only when the expression before it is complete.
  Continuation must be determined structurally from the visible declarative
  syntax, not from a hardcoded list of standard-library words.
- Preserve explicit AST boundaries. Syntax matching must not consume a later
  map element through parentheses or another completed operand.
- Do not weaken canonical round-trip, type-law, or ambiguity checks to make a
  regression pass.
- Do not preserve a test merely because it predates the parser refactor. If its
  source form or expected value contradicts the current language design,
  update or replace the test and record the current invariant in its name or
  surrounding test group.
- Remove any temporary tracing after it has served its purpose.

## Triage rule

Before changing production code for a failing test, classify it as one of:

1. **Implementation regression:** the test still expresses intended language
   behavior, and the parser, rewrite, evaluator, or type system violates it.
2. **Outdated source spelling:** the intended behavior remains valid, but the
   test program uses syntax or boundaries superseded by the declarative parser.
3. **Outdated expectation:** the program is valid, but its expected AST,
   canonical value, error, or ambiguity decision reflects pre-refactor
   semantics.
4. **Unclear architectural case:** the intended behavior is not established
   strongly enough to choose between implementation and test changes. Stop and
   resolve the design rather than adding a special case.

The classifications below have not yet been made. Error messages are recorded
only to help find shared causes; they are not evidence by themselves that the
implementation rather than the test is wrong.

## Remaining failures

### Canonical function reconstruction: 5

- captured standard-library Boolean
- captured computed `this` projection
- computed `this` projection inside a function
- inferred parameters
- optional number closure avoids nested module reconstruction

These do not currently present as one uniform failure: they include inferred
application, access bounds, declared-result validation, alternative selection,
and compact variadic reconstruction. Treat canonical reconstruction as a
separate workstream and preserve round-trip checks.

### Functions: 3

- function sum selects the numerical alternative
- function sum selects the string alternative
- recursive result type mismatch

The two function-sum failures report `EitherAlternativesNotDistinct`. The
recursive-mismatch test expects rejection of the declared result type but
currently receives `1`; confirm that expectation against the current recursive
typing model before changing it.

### Datra type laws: 4

- canonical federation: reflexive subfederation and self-specification
- canonical federation: string capability
- skip numerical coercion: coercion does not erase skip typing identity
- total begin/yield blocks: its yielded value is its only member

The federation cases report `EitherAlternativesNotDistinct`. The skip case is
a parse failure at the second parenthesized operand. The total-block case
reaches Boolean evaluation with a function-valued right operand.

### Cross-feature regression programs: 1

- standard-library syntax and string-template decoding

This currently fails with `UnknownIdentifier "value"`.

### Overloading and assertions: 4

- right overload reverses the operands
- safe overload fills a later compatible slot
- reverse safe overload reverses the operands
- safe overload result supports subfederation

The two safe-overload failures report `EitherAlternativesNotDistinct`. The
reverse overload cases evaluate only the supplied value, losing the expected
typed/map structure.

### Standard library and declarative syntax: 31

#### Qualified syntax: 3

- `Std.if false then (1 + "bad") else 11`
- `Std.from (1 + 1) to 5`
- `Std.range 2 down`

All three report `NoApplicableFunctionAlternative`.

#### Inline fixed points: 4

- finite access lazily unfolds recursive data
- recursive concatenation is not string-specific
- `let` and `fun` share productive fixed-point access
- fixed-point reverse specification

The first three lose recursive bindings (`name` or `values`). The reverse
specification returns only its target and drops the specified value.

#### Mapped access: 7

- coalization preserves an `Either` boundary
- coalization preserves an identifier boundary
- coalization composes with subfederation
- coalization composes with specification
- coalized types concatenate positionally despite overlap
- function inference retains coalization
- identifier erasure retains coalization

This group contains three kinds of failure: federation distinctness, dropped
coalization structure, and neutral parse failures around `><`. Establish the
intended neutral AST before changing evaluation.

#### Maybe and list operators: 7

- list sequencing applies a function to a nonempty split
- list sequencing accepts an optional named parameter
- list sequencing result supports specification
- list sequencing result supports subfederation
- optional named matcher accepts split positional values
- required named matcher rejects split positional values
- inferred type aliases reduce to their canonical type

The first six currently reach evaluation with an unconsumed `yield`. The
inferred-alias case reports `EitherAlternativesNotDistinct`.

#### Library and dependent-list types: 2

- `Str of Template`
- `List Str` rejects a non-string member

These disagree with their expected Boolean results. First verify that those
expectations still follow from the current declarations. If implementation
work is required, it must use ordinary declared type semantics, without a
`Str`, `Template`, or `List Str` special case.

#### Dependent family sugar: 5

- `with-in-do` builds an indexed sum family
- `with-from-do` omits the `in` keyword
- `for-in-do` builds an indexed product family
- `for` without `in` rejects an ordinary range
- `with` without `in` rejects an ordinary range

The construction cases report `NoApplicableFunctionAlternative`. The two
negative cases lose the binder and report `UnknownIdentifier "i"` instead of
the expected range-type error.

#### Integer limits and infinity: 1

- `from` rejects a negative-infinite origin

This loses the directional literal and reports `UnknownIdentifier "up"`.

#### Declared patterns: 2

- a template may begin with a postfix operand hole
- one function accepts an inhabited list of templates

Both currently fail in the neutral parser around the declared postfix `++`
form. The fix must remain generic for postfix templates.

## Likely shared workstreams

These are working hypotheses, not confirmed diagnoses and not permission to
special-case the named tests. A cluster may instead identify several tests
that share an outdated assumption.

1. **Validate the tests.** For each cluster, inspect the source program, its
   expected neutral AST boundary, and the declaration in `std.datra`. Decide
   whether the test still states intended behavior before editing production
   code. Add a replacement regression when removing an obsolete expectation.
2. **Block and continuation rewriting.** The six list-sequencing `yield`
   failures, the dependent-family failures, and several lost identifiers may
   share an incorrect expression or block extent, or may share pre-refactor
   source spelling.
3. **Federation admission.** Eight failures report
   `EitherAlternativesNotDistinct` across function sums, canonical
   federations, safe overloads, coalization, and inferred aliases. Determine
   whether the alternatives are intended to remain distinct under the current
   type model, then check the common admission path before addressing call
   sites.
4. **Neutral operator boundaries.** For the coalization, skip, and
   postfix-template parse failures, first decide whether each source form is
   still valid. Valid forms need parser regressions stating their neutral AST;
   outdated forms need updated tests. Declarative word syntax must still be
   applied only in the rewrite pass.
5. **Structure preservation.** Reverse overload, reverse specification, and
   coalization failures appear to discard a wrapper while retaining an inner
   value. Confirm that the wrapper remains semantically required, then trace
   normalization and specification rather than patching rendered output.
6. **Canonical closures and fixed points.** Work on these after the shared
   parser/rewrite failures are reduced. Re-read termination and reconstruction
   paths before adding recursion guards; do not restore arbitrary search caps.
7. **Semantic tail.** Reassess the expected semantics of recursive result
   validation, total block typing, `Str of Template`, and dependent-list
   membership after their parsed and canonical forms are confirmed correct.

## Focused verification

Use Tasty patterns while working on a cluster, for example:

```sh
cabal test datra-interpreting-test --test-show-details=direct \
  --test-option=-p --test-option='Maybe and list operators'

cabal test datra-interpreting-test --test-show-details=direct \
  --test-option=-p --test-option='canonical federation'

cabal test datra-interpreting-test --test-show-details=direct \
  --test-option=-p --test-option='canonical function reconstruction'
```

After each shared fix, rerun the complete interpreter suite because failures in
different groups frequently share parser or normalization machinery. Run the
full non-Liquid suite before declaring completion:

```sh
cabal test all
```

## Completion criteria

- All five non-Liquid test suites pass.
- Every formerly failing interpreter test has been classified; outdated tests
  have been updated or replaced rather than forcing compatibility into the
  implementation.
- The build emits no warnings.
- No standard-library expression has compiler-side special handling.
- No temporary tracing or arbitrary search bound remains.
- `docs/PARSER_BOOTSTRAP_REMAINING.md` is deleted.
