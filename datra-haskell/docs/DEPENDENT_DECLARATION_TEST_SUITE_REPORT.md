# Dependent declaration test suite report — 2026-10-29

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

## Unified declaration-scope refactor

The interpreter no longer has a parallel `ScopeBindings`/`Binding` declaration
system or a parallel `scopeNamedMapLayers` lookup path. `Scope` contains one
declaration environment: dependent-declaration layers. Every exact lexical name
created by the interpreter is represented as a singleton scoped declaration in
one of those layers. This includes:

- the `datra` host declaration;
- contextual `_it` and `_this` declarations;
- inferred generic and prepared function-argument declarations;
- qualified imported-module declarations; and
- declarations projected by `with` and module opening.

Runtime values, import provenance, source-definition provenance, and canonical
presentation are payload metadata on the scoped dependent declaration. They do
not form another lookup table or fallback resolver. Retained eager source
declarations use that payload as their unrestricted cached value, while
restricted shadow-consistency evaluation still evaluates their source
implementation. Runtime singleton declarations always use their stored value
and are represented by `ScopedRuntimeSingletonDeclaration`; they do not invent
a source implementation.

The scoped declaration type distinguishes `ScopedDatraDependentDeclaration`,
`ScopedRuntimeSingletonDeclaration`, and
`ScopedProjectedDependentDeclaration`. A dynamic or transfinite named-map
projection is a fallback declaration in the same layer index; it no longer uses
a separate scope field. Neither runtime variant has a fabricated source head or
implementation. In particular, an earlier temporary empty-identifier sentinel
and the singleton `AtlasMap []` placeholder were removed. Exact lookup,
containment, and discovery delegate through the scoped declaration. Exact
runtime values are described by `RuntimeSingletonPayload`, explicitly payload
metadata rather than another declaration type.

The same declaration-layer abstractions now govern all relevant operations:

- exact resolution uses the layer singleton/prefix index;
- named-view discovery obtains the same stored runtime payload as exact lookup;
- contextual-level collection uses indexed candidates for `_it` or `_this`;
- definition protection and overlap checks use declaration candidates;
- closure reconstruction obtains source definitions and module origins from the
  selected scoped declaration; and
- module discovery enumerates declaration-layer members and reads typed import
  metadata.

There is no secondary exact-name map and no linear exact-name fallback. The
refactor also removed two avoidable quadratic paths: successful filtering now
uses order-preserving linear accumulation, and shadow-consistency overlap checks
query the already-built declaration index instead of scanning every local
declaration for every candidate name.

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

## Current bounded verification

The old `UnknownIdentifier "from"` diagnosis depended on `lookupScope` being a
binding-only closure boundary. That boundary has been removed: closures now
obtain local and imported definitions through indexed scoped dependent
declarations. The old failure has not been reproduced after the refactor,
because the focused test does not yet finish standard-library syntax rewriting.
It must therefore not be reported as the current failing result.

The focused `value holes evaluate expressions before selection` check was run
under a hard 12-second timeout. It printed its test label but did not complete.
A temporary progress trace, removed after diagnosis, located the time inside
`rewriteResourceSyntax` while parsing `std.datra`, before module evaluation or
eager declaration retention. The process remained CPU-bound with approximately
24 MB maximum resident memory and continued advancing through rewrite passes.
It repeatedly reconstructed validation scopes containing 50–53 declarations.
This supports a severe repeated-computation diagnosis, not a deadlock or a
proved infinite loop.

Post-refactor bounded checks currently establish:

- `cabal build exe:datra-haskell test:datra-interpreting-test -f-liquid`
  passes;
- `git diff --check` passes;
- `closed infinite valued range` passes; and
- all 12 `scope-protection substrate` tests pass.

The syntax-rewriter scope-cache problem is separate from declaration lookup:
the repeated work occurs before Std is imported into a runtime scope. It remains
the next performance issue to resolve before the dependent-declaration and
closure regressions can receive a meaningful post-refactor result.

### Not run

The full interpreter suite and the parsing, types, and CLI suites were not run
to completion in this verification pass. The 19 selected acceptance tests and
the core suite were not rerun after the callable-payload and unified-scope
repairs. This report therefore makes no post-repair pass/fail claim about those
suites.

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
