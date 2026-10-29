# Dependent declaration test suite report — 2026-10-28

## Scope

This report contains only results observed during the current verification
pass. It distinguishes baseline results from checks rerun after the latest
repair. It intentionally does not retain counts or failure lists from older
verification passes, because the AST, block model, declaration modifiers,
assertion feature, and test programs have changed since those runs.

The complete suite was not run to completion. Per the decision to avoid the
known hanging path, verification focused on the dependent-declaration
acceptance tests, the new `def` regressions, a current core-suite run, and a
small number of directly relevant integration checks. The callable-payload
repair described below was made after the 19-test acceptance run and the core
suite run, so those two runs are retained as baseline results rather than
claimed as post-repair verification.

## Passing checks

### Build

```sh
cabal build all -f-liquid
```

Passed. The library and `datra-haskell` executable compiled and linked.
`git diff --check` also passed.

### Dependent declarations and declaration modifiers

```sh
cabal test datra-interpreting-test \
  --test-show-details=direct \
  --test-option=-p \
  --test-option='$NF=="dependent declarations" || $0 ~ /canonical value declarations/'
```

All 19 selected tests passed:

- the dependent-declarations example;
- independent `def` definition protection;
- independent `val` canonical presentation;
- declarations with neither marker and with both markers;
- the full `let def val` form;
- optional declaration names;
- declaration specification and subfederation behavior;
- rejection of `val` on an annotated assignment and on a non-declaration; and
- the unified modifier diagnostic for `val let`, `val val`, `def let`,
  `val def`, `let val def`, and `def def`.

Every invalid modifier sequence reports its unique correct ordering. Modifier
names are derived from the operator definitions rather than duplicated string
constants.

`ExpectedDependentDeclaration` remains the internal error constructor for a
non-declaration in a declaration-only block. Its user-facing message is:

```text
operation has no effect inside block
```

### Core suite

```sh
cabal test datra-core-test --test-show-details=direct
```

All 35 tests passed: 29 examples and six Hedgehog properties. Each property
completed 100 generated cases.

### Migrated integration check

The focused `recursive defaults, overloads, typing, and total blocks`
integration regression passed after its assertion-only checks were migrated to
named Boolean declarations and one yielded Boolean tuple.

## Callable dependent-declaration repair

Concrete dependent declarations now invoke ordinary callable payloads through
the interpreter's normal `applyFunction` path. Runtime-insertion payloads still
use their existing direct insertion path, and non-callable payloads remain
unchanged. A single captured value is supplied as that positional value rather
than as a singleton atlas map; named contextual bindings are still constructed
from the validated dependent-declaration input.

The migrated integration type check now inspects the declaration descriptor
explicitly:

```datra
successorTypeCheck :=
  ((~"successor Nat next")[0].value) of ({value? : Nat} -> Int)
```

The bare `successor` check was invalid because the declaration introduces the
dependent name family, not a standalone `successor` identifier.

Two focused regression cases were added:

- `dependent captures call ordinary functions through subfederation`, which
  expects `successor 4 next` to produce `5` when `%Nat` feeds an optional
  `Int` parameter; and
- `dependent declaration descriptors expose their functions`, which expects
  the descriptor lookup above to retain the callable and satisfy the narrowed
  function type.

The current tree builds successfully with these changes. Neither new test is
claimed as passing because both encounter the downstream `from` failure below
before an assertion result is produced.

## Removal and stale-symbol scans

Current source scans found no remaining language-level `assert` in `.datra`
files or embedded Datra program strings. Haskell's ordinary test assertion
helpers are intentionally unchanged.

The same scans found no remaining active implementation or test uses of:

- `assert_body`, `datra.assert`, or `AssertionFailed`;
- `UnresolvedFunctionBody`, `UnresolvedBegin`, or `BlockEntry`;
- `dependentDeclarationExpression`;
- `RuntimeModules`, `EvaluationMode`, `modulesForMode`, or
  `expressionForMode`;
- the superseded standard-library namespace spelling;
- the obsolete block-position modifier errors; or
- the superseded declaration and map terminology.

## Current failures and interrupted check

### Newly exposed `from` failure

The focused `standard-library syntax and string-template decoding` integration
regression no longer reports `UnknownIdentifier "successor"`. It now advances
farther and fails with:

```text
SourceParseFailure (ParseFailure {parseFailureMessage =
  "UnknownIdentifier \"from\""})
```

The same failure was observed in focused runs of both newly added regression
tests. The pre-existing `value holes evaluate expressions before selection`
test provides a smaller reproducer:

```datra
"double %Nat" := (Nat -> Nat) do yield it * 2
yield double (2 + 2)
```

It expects `8`, but fails while the standard-library parsing environment is
constructing its syntax rules, before this program is evaluated. The adjacent
`zero-hole syntax completes a total domain` program case and the
`Std.(from (1 + 1) to 5)` expression case fail at the same boundary in the
current tree. The earlier passing results in this report predate the
callable-payload repair and were not rerun after it.

The failure is in reconstruction of a declaration capture bound. An evaluated
bound such as `Nat` is rendered as canonical Datra source, producing:

```datra
from 0 up
```

`closedSourceExpression` parses that text with the neutral parser and asks
`inlineDependencies` to close its library dependencies. The neutral AST still
contains an ordinary application headed by `from`. The closure resolver only
starts from `lookupScope`, so it can capture lexical bindings but cannot capture
the `from` dependent declaration family stored in
`scopeDependentDeclarationLayers`. Consequently no dependency is collected,
the source remains headed by bare `from`, and evaluation asks for a complete
declaration member literally named `from`. The available family contains names
such as `from 0 up`, not a member named only `from`, so lookup ends in
`UnknownIdentifier "from"`. A diagnostic trace reached that lookup while the
active resolution key was `Nat` and the declaration layer containing `from`
was present.

The closure representation already has the structural machinery needed to
retain such a family: `Dependency` contains `dependencyDeclaration`, and
`capturedDeclaration` can preserve and translate a complete dependent
declaration head. No resolver construction currently sets
`dependencyDeclaration` to `Just`; all three construction sites set it to
`Nothing`, leaving that path unused.

The underscore translation must obey these invariants:

- a dependency address records its unmodified semantic origin;
- reconstruction prepends one underscore only to the first address segment;
- therefore `[Std, from]` is referenced as `_Std.from`, with the nested member
  name unchanged; it must never become `Std._from` or `_Std._from`;
- a genuinely local one-segment family `[from]` may become `_from`, in which
  case the prefix translates the complete dependent name family rather than
  one concrete member; and
- references and recreated declarations must receive the same translation.

A repair cannot merely teach `lookupScope` to return `_from`. In the neutral
AST, the inner application in `from 0 up` is also structurally
`FunctionApplication from 0`; the closure code's current strict-reference path
recognizes that shape as the path `[from]`. Replacing the whole inner node by
`_from` would discard the captured origin `0` and leave `_from up`. The repair
must recognize and reconstruct the complete declared syntax invocation, retain
all captures, and then translate only the dependency root according to the
address invariant above. No repair was attempted in this pass.

### Current hanging path

The focused `module exports, private closure state, and declared syntax`
integration check printed its test label but produced no result for 30 seconds.
It was interrupted. No pass/fail claim is made for that check.

### Not run

The full interpreter suite and the parsing, types, and CLI suites were not run
to completion in this verification pass. The 19 selected acceptance tests and
the core suite were not rerun after the callable-payload repair. This report
therefore makes no post-repair pass/fail claim about those suites.

## Runtime-performance approaches that did not work

These are historical experiments retained only to prevent repeating known
dead ends. They are not current benchmark results.

- A singleton-only implementation of `dependentDeclarationNamedView` did not
  improve the complete cold-start benchmark and was removed.
- Replacing full ordinal coalization in `scopeEntriesValue` with finite
  collection did not reduce allocation and was reverted.
- Disabling dependent-family validation improved one focused measurement, but
  is invalid because the validation is required for correctness.
- Reordering structural and semantic overlap checks helped locally but did not
  eliminate repeated family compilation or solve the runtime regression.
- Separately caching syntax- and runtime-insertion probes helped locally but
  did not compensate for compiling the same family in several passes.
- A separate exact-name runtime map improved timing but split lookup into two
  implementations; it was replaced by the uniform prefix-trie design.
- Caching every family produced by the strict pass for validation made no
  measurable improvement and was reverted.
- Removing eager application-adapter admission without changing the matcher
  made the focused run slower because unusable rules remained in every scan.
- Retaining deferred-validity rules and checking them at matcher boundaries
  increased both runtime and allocation.
- Combining an ordered first-literal map index with deferred validity remained
  slower because rebuilding indexes and merging candidate buckets cost more
  than candidate filtering saved.
