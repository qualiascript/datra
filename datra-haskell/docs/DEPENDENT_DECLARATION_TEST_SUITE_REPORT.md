# Dependent declaration test suite report — 2026-10-28

## Scope

This report contains only results observed against the current working tree.
It intentionally does not retain counts or failure lists from earlier runs,
because the AST, block model, declaration modifiers, assertion feature, and
test programs have changed since those runs.

The complete suite was not run to completion. Per the decision to avoid the
known hanging path, verification focused on the dependent-declaration
acceptance tests, the new `def` regressions, a current core-suite run, and a
small number of directly relevant integration checks.

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

### Removal and stale-symbol scans

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

## Current failure and interrupted check

### Custom syntax integration failure

The focused `standard-library syntax and string-template decoding` integration
regression currently fails with:

```text
SourceEvaluationFailure (UnknownIdentifier "successor")
```

This is a custom syntax declaration/lookup failure, not a failure in the
dependent-declaration or `def` acceptance set.

### Current hanging path

The focused `module exports, private closure state, and declared syntax`
integration check printed its test label but produced no result for 30 seconds.
It was interrupted. No pass/fail claim is made for that check.

### Not run

The full interpreter suite and the parsing, types, and CLI suites were not run
to completion in this verification pass. This report therefore makes no
current pass/fail claim about them.

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
