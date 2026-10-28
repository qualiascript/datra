# Test suite report — 2026-10-28

## Scope and status

The full Haskell test command was started from `datra-haskell/`:

```sh
cabal test all -f-liquid -j1 --test-show-details=direct
```

The run did not finish. It stopped making progress while running
`canonical function reconstruction.selected transparent number function is
self-contained`; after more than 100 seconds without output, the run was
interrupted rather than allowed to hang indefinitely.

Results below are therefore a partial full-suite snapshot, not a claim that
the repository's complete test suite passed or failed as a whole. Before the
hang, 106 test cases completed: 59 passed and 47 failed.

| Suite | Result observed |
| --- | --- |
| `datra-core-test` | Complete: 35 passed, 0 failed |
| `datra-interpreting-test` | Partial: 24 passed, 47 failed, 1 hung; later tests not reached |
| `datra-parsing-test` | Not reached |
| `datra-types-test` | Not reached |
| `datra-cli-test` | Not reached |

The Cabal warning that the Hackage package list was 50 days old did not prevent
dependency resolution or test execution.

## Passing tests

### Core suite

All 35 `datra-core-test` cases passed. This includes all 29 example cases and
all six Hedgehog properties. Each property completed 100 generated tests:

- finite ordinals round-trip naturals;
- ordinal construction is canonical;
- ordinal ranks round-trip;
- finite-tail splitting reconstructs ordinals;
- spine positions round-trip; and
- identity insertions round-trip.

The passing example coverage includes identity insertion, ordinal enumeration,
the dominion atlases, spine and chain operations, consolidation, folio, page
elements, pagination, atlas construction and combinations, navigation,
expedition, transformations, stable confederal data, charter, transposals,
transversals, coalition, and domanial inclusion.

### Interpreter examples

The following completed interpreter example cases passed:

- literals and arithmetic;
- slot ordinal distinctness;
- dependent declarations;
- argumentative maps;
- argumentative maps in concatenation;
- argumentative maps in string templates;
- internal typed decoding;
- begin/yield scope and provenance;
- implicit programs;
- integers and integer ranges;
- closed infinite valued range;
- booleans and Either;
- ranges;
- canonical results;
- rendering;
- maps;
- atlas-map federations;
- access;
- specification;
- Datra and canonical type capabilities;
- typed rejections; and
- located rejection.

The `dependent declarations` case includes the overlap-diagnostic regressions:
both an unprojectable declaration on its own and one overlapping an earlier
family report `OverlappingDependentDeclarations`. The obsolete
`SyntaxTemplateProjectionOrderMismatch` diagnostic has been removed.

### Canonical function reconstruction

Two completed cases passed before the hang:

- nothing result; and
- registered native function.

## Failing tests

### Interpreter examples

Eleven completed example cases failed:

| Test | Observed failure |
| --- | --- |
| generic product ordinal indexing | `a positive-infinity endpoint prevents map projection` assertion failed |
| string templates | optional missing constructor produced `$nothing ~> "%(nothing \| () \| Just : Int)"` |
| lookup follows transfinite foliage traversal | `NamedAccessFailed (NamedFieldNotFound "key")` |
| named field access | optional map member `b` was not found |
| template-backed keyword forms | `UnknownIdentifier "range"` |
| begin/yield scope rejections | duplicate `a` declaration produced `OverlappingDependentDeclarations "a" "a"` during parsing |
| module aliases retain syntax rules | same-block redeclaration was accepted as `Right ["abc","abc"]` |
| optionals and conditionals | `Maybe evaluates to its source-defined federation` assertion failed |
| combined type systems | `Boolean equality and arithmetic compose into Maybe Int` assertion failed |
| combinatorial numerical systems | `descending numerical subtypes compose into optional Int` assertion failed |
| identifier types and assignments | supplied-specification case failed with `UnknownIdentifier "range"` |

### Canonical function reconstruction

Thirty-six completed cases failed before the hanging case.

Seven failed with `SourceEvaluationFailure EitherAlternativesNotDistinct`:

- recursive factorial;
- recursive self can be aliased;
- transitive captured definitions;
- narrowed callable;
- only the selected module member is reconstructed;
- qualified dependency names retain their module origin; and
- user name cannot collide with a nested module function.

Twenty-two failed with `ModuleEvaluationFailed (ModuleNotLoaded "Std")`:

- user local named `_fun`;
- quoted local matches generated root;
- captured name matches generated root;
- quoted capture matches generated root;
- three dependency levels reconstruct independently;
- user value is distinct from the inline fixed point;
- outer user name cannot capture a nested fixed point;
- eager capture retains its definition;
- named input access survives serialization;
- input names survive serialization;
- outer `it` depth is captured by an escaping function;
- outer `this` depth is captured by an escaping function;
- defaults survive serialization;
- local `this` is not polluted by dependency bindings;
- higher-order captured value;
- captured standard-library Boolean;
- quoted parameter reference;
- strict quoted access in an optional named parameter;
- strict references apply a captured function;
- library inlining preserves a user `_AST` parameter;
- quoted captured identifier; and
- computed `this` projection inside a function.

The other seven failures were:

| Test | Observed failure |
| --- | --- |
| function input can be aliased | canonical serialization was not idempotent: a captured `begin let` form rendered back as `fun` |
| each dependency level uses the closure-local namespace | wrong dependency for `next` |
| user captures receive unique closure-local names | missing encoded declaration for `abc` |
| generated recursion uses `fun` without a temporary name | begin entries were not separated from `yield` |
| mutual recursive definitions | expected one collected `odd` declaration, got zero |
| unused ambient bindings are absent | source-defined integer-range dependency assertion failed |
| different captured values have different representations | capture identity was erased |

## Hanging test and unobserved coverage

The run reached the label:

```text
canonical function reconstruction
  selected transparent number function is self-contained:
```

No result or additional diagnostic appeared for more than 100 seconds. The
process was interrupted. Any interpreter tests ordered after that case, and
the parsing, types, and CLI suites, have no result in this report.

## Runtime-performance approaches that did not work

These are historical experiments preserved from the removed runtime handoff.
They were not rerun as part of this test report.

- A singleton-only implementation of `dependentDeclarationNamedView` did not
  improve the complete cold-start benchmark and was removed.
- Replacing full ordinal coalization in `scopeEntriesValue` with finite
  collection did not reduce allocation and was reverted.
- Disabling dependent-family validation improved the focused measurement to
  about 6.41 seconds and 20.27 GB, but it is not a valid optimization because
  the validation is required for correctness.
- Reordering structural and semantic overlap checks helped but did not remove
  repeated family compilation or solve the runtime regression.
- Separately caching syntax- and runtime-insertion probes helped locally but
  could not compensate for compiling the same family in several passes.
- A separate exact-name runtime map improved timing but split lookup into two
  implementations; it was replaced by the uniform prefix-trie design.
- Caching every family produced by the strict pass for validation made no
  measurable improvement. Allocation changed from 25,300,965,696 bytes to
  25,303,238,848 bytes and timing stayed within noise, so it was reverted.
- Removing eager application-adapter admission without changing the matcher
  regressed the focused run to 9.52 seconds because unusable rules remained in
  every matcher scan.
- Retaining deferred-validity rules and checking them at matcher boundaries
  regressed the focused run to 8.66 seconds and 25.52 GB.
- Combining an ordered first-literal `Map` index with deferred validity was
  semantically correct for the focused case but regressed it to 8.89 seconds;
  rebuilding indexes and merging ordered candidate buckets cost more than the
  candidate filtering saved.
