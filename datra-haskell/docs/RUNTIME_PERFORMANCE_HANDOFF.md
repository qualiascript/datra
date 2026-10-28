# Runtime performance regression handoff

## Goal and current status

The goal is to restore linear-time dependent-declaration processing and bring
the cold standard-library path back near `master` without changing unrelated
test behavior. Most of the repository's tests currently fail for pre-existing
reasons; fixing those failures is out of scope. Use focused tests and compare
only failures introduced by this work.

The regression is improved but not fixed:

| Revision/state | Focused test time | Heap allocation |
| --- | ---: | ---: |
| `master` baseline | 1.42 s | 5,984,472,304 B |
| branch before this investigation | 19.32 s | 54,839,044,008 B |
| committed optimization `133a15e` | about 11.7 s | about 34-51 GB depending on profiling build |
| committed exact-family validator index (`8258a30`) | 10.36 s locally | 30,428,141,688 B in the prior run |
| current working tree, with compiled-let family reuse | 7.81 s | 25,300,965,600 B |

The current working tree is therefore still approximately 5.5 times slower
and allocates 4.2 times as much as `master`. Do not treat the current result as
complete.

Commit `133a15e` (`improve runtime speed`) contains the runtime declaration
index, seeded eager-let retention, recursive-environment reuse, and syntax-rule
capability caching described below. Commit `8258a30` contains the literal-name
validator fast path and shared compilation between validation and scope
advancement. Preserve that change unless a replacement measures better.

## Exact focused test used throughout

All headline measurements use this existing Tasty test:

```text
Datra interpreter.examples.literals and arithmetic
```

It is declared as `testLiteralsAndArithmetic` in
`test/DatraInterpretingTests.hs`. It is a useful cold-start benchmark because
its first interpretation forces construction of the standard module and its
syntax/declaration environment. It also checks enough ordinary evaluation to
catch obvious semantic damage.

Run it from `datra-haskell/` through Cabal. Running the test executable directly
does not set up Cabal's data-file path and can fail with `missing bundled Datra
library: std.datra`.

Timing command:

```sh
/usr/bin/time -f '%e seconds %M KB' \
  cabal test datra-interpreting-test \
  --test-show-details=direct \
  --test-option=-p \
  --test-option='literals and arithmetic'
```

Allocation command:

```sh
cabal test datra-interpreting-test \
  --test-show-details=direct \
  --test-option=+RTS \
  --test-option=-s \
  --test-option=-RTS \
  --test-option=-p \
  --test-option='literals and arithmetic'
```

Use the time printed beside the Tasty case, not the outer `/usr/bin/time`
duration when a rebuild occurs. The latest cache-only run printed `OK (7.81s)`
and allocated `25,300,965,600 bytes`.

For a fair baseline, create an isolated `master` worktree, build it with the
same GHC and `-O1` profile, and run the same command there. The earlier baseline
worktree was `/tmp/datra-master.fpoU9i`, but it should not be assumed to still
exist.

## Focused profiling procedure

Build a cost-centre-enabled test executable in a separate build directory:

```sh
cabal build test:datra-interpreting-test \
  --builddir=dist-prof-focused \
  --enable-profiling \
  --profiling-detail=all-functions
```

Then run only the focused case:

```sh
cabal test datra-interpreting-test \
  --builddir=dist-prof-focused \
  --enable-profiling \
  --profiling-detail=all-functions \
  --test-show-details=direct \
  --test-option=+RTS \
  --test-option=-p \
  --test-option=-po/tmp/datra-current-focused \
  --test-option=-s \
  --test-option=-RTS \
  --test-option=-p \
  --test-option='literals and arithmetic'
```

The report is `/tmp/datra-current-focused.prof`. Profiling overhead is large;
compare inherited percentages and allocation shape, not its wall time with an
ordinary build.

The most useful profile taken before the latest uncommitted validator index
reported:

- 52.63 seconds of profiled mutator work and 51.16 GB of profiled allocation;
- `parsedSourceImportInvocations -> discoverImportInvocations ->
  rewriteResourceSyntax` owning 70.5% of time and 65.3% of allocation;
- the validation `currentFamily -> compileScopedRewriteRules` subtree owning
  20.5% of time and 17.2% of allocation; and
- 918 eager evaluations of syntax-rule implementations in one hot validation
  subtree.

On `master`, syntax rewriting accounted for only about 17% of the corresponding
profile. This establishes that the remaining regression is in repeated syntax
scope/rule work, not primarily in `dynamicDependentDeclarationNamedView`.

## Optimizations already implemented

### 1. A uniform prefix trie for runtime declaration lookup

`Interpreting.hs` now stores `[DependentDeclarationLayer]` instead of raw lists
of scoped declarations. Each layer contains:

- its ordered members;
- a trie keyed by the longest common leading literal of each declaration
  family's name-template branches; and
- a fallback list for families with no static leading literal.

An exact literal name is not a separate lookup algorithm. It is a trie entry
whose prefix consumes the entire queried name. Runtime lookup walks the query
through the trie, collects declarations attached to nodes on that path, then
fully matches only those candidates plus the fallback declarations.

With `m` query characters, character fan-out `sigma`, `k` indexed candidates,
and `d` genuinely dynamic/no-prefix declarations, lookup is
`O(m log sigma + k + d)` because trie children currently use `Data.Map Char`.
Since character fan-out is bounded, this is effectively linear in the name
length and output candidates, not logarithmic in the declaration count. Using
an array or bounded integer map could remove the `log sigma`, but that is not a
meaningful current hotspot.

Trie construction uses `foldr` and cons, not `here <> [scoped]`; the latter
becomes quadratic when many declarations share a prefix. Expanded template
branches are cached on `ScopedDependentDeclaration` so lookup does not keep
calling `dependentDeclarationTemplateBranches`.

All declarations still use `dynamicDependentDeclarationNamedView`. A previous
singleton-only view shortcut did not improve the complete focused run and was
removed to keep runtime view semantics uniform.

### 2. Seeded eager-let retention was restored

The dependent-declaration refactor had removed the old behavior where eager
`let` values become retained after recursive seed discovery. Scope construction
now returns a rebuilding function. `importScopeUsing`:

1. discovers statically singleton eager-let families;
2. partitions recursive seeds from ordinary eager lets;
3. resolves the seeds first;
4. rebuilds the scope with those retained values;
5. resolves the remaining eager lets; and
6. builds the final scope with all retained members.

Productive self-recursive declarations are excluded from forcing. Retained
members are stored on `ScopedDependentDeclaration` and are returned directly
for unrestricted named access. This is both the intended recursive-family
semantics and a cache after seed discovery.

Do not remove this mechanism while optimizing syntax rewriting. The next cache
should extend the same principle to compiled let syntax families.

### 3. Duplicate recursive-environment construction was removed

`rewriteSequence` now creates one `recursiveRewriteEnvironment` for the stable
discovery result and reuses it for the tentative pass, strict pass, and
validation, changing only `rewriteStrictCaptures`. Previously each phase
recompiled recursive rules independently.

This was correct and measurable, but only a small part of the total regression.

### 4. Cheap structural overlap rejection runs first

Dependent-family validation now calls `rewriteRulesOverlap` before evaluating
and comparing semantic name federations with `eitherValue`. Most unrelated
literal syntax families are structurally disjoint, so they should not force
semantic scope construction.

### 5. Syntax/runtime insertion capabilities are cached per compiled rule

`RewriteRule` now retains `rewriteRuleSyntaxInsertion` and
`rewriteRuleRuntimeInsertion`. `compileScopedRewriteRules` shares one evaluated
implementation between the syntax and runtime probes. Expansion and val
injectivity validation consume the cached capabilities instead of reevaluating
the same adapter two or three times.

This fixed a real repeated-evaluation problem, but compiled families are still
created too often. Caching the result at the family/seed level is the higher
priority.

### 6. Literal-name validation is indexed again

The `SyntaxRewriting.hs` change in `8258a30` recognizes declaration
families whose every branch is one `StringTemplateLiteral`. Validation stores
those families in `Map String ...`, compares a new exact family only with an
existing declaration at the same name and with genuinely dynamic families,
and uses `compileRewriteRule` rather than semantic
`compileScopedRewriteRules` for the exact family.

This is the special case that reduced the focused run by roughly 1.3 seconds
in isolation (about 11.76 s to 10.42 s). It was briefly removed to keep logic
uniform, then restored because the measured benefit is material. This is a
validation index, not the removed runtime singleton named-view implementation.

The same change adds `advanceScopeResolved`, which returns both the
next environment and the newly compiled family. Dynamic validation can then
validate the exact compiled object that scope advancement retains instead of
resolving and compiling the declaration twice.

### 7. Compiled recursive-let families are retained after discovery

The current working tree makes `recursiveRewriteEnvironment` return both the
recursive environment and a `Map Int [RewriteRule]` keyed by stable rewritten
block position. Each let family is compiled with its source-position
`scopedBlockDeclarations` snapshot. The strict pass promotes that cached family
with ordinary shadowing behavior, and validation consumes the same compiled
object instead of resolving and compiling the let again.

This reduced the focused local run from 10.36 seconds to 7.81 seconds and heap
allocation from 30.43 GB to 25.30 GB. The standalone test `recursive let
aliases to syntax bodies are discovered` passes.

The post-change focused profile (`/tmp/datra-let-cache-focused.prof`) reports
36.12 seconds of profiled mutator work and 36.85 GB of allocation excluding
profiling overhead. In its hot recursive-discovery subtree,
`recursiveRewriteEnvironment -> advanceScopeResolved ->
compileScopedRewriteRules` still owns 44.7% of time and 35.5% of allocation.
Eager adapter evaluation owns 32.1% of time and 25.8% of allocation, while
hole classification owns another 12.2% and 9.2%. These are inherited
percentages and overlap with the parent compilation total.

## Experiments that did not solve the regression

- A singleton implementation of `dependentDeclarationNamedView` did not
  improve the full focused benchmark. Keep the dynamic delayed view unless a
  layer-level redesign replaces it.
- Replacing the full ordinal coalization in `scopeEntriesValue` with finite
  collection did not reduce allocation and was reverted.
- Disabling dependent-family validation reduced the focused run to about
  6.41 seconds and 20.27 GB after recursive-environment reuse. This is a useful
  upper-bound experiment, but validation is required and must not be disabled.
- Reordering structural and semantic overlap checks helped, but did not remove
  repeated family compilation.
- Separately caching the syntax and runtime insertion probe helped, but it
  cannot compensate for compiling the same family in several passes.
- A separate exact-name runtime map improved timing, but it divided runtime
  lookup into two implementations. The current trie represents exact and
  templated prefixes uniformly and should remain the runtime structure unless
  a new benchmark proves otherwise.
- Caching every family produced by the strict pass for validation made no
  measurable improvement: allocation moved from 25,300,965,696 bytes to
  25,303,238,848 bytes and timing remained within noise. Laziness was already
  avoiding most of that apparent recompilation, so the experiment was reverted.
- Removing eager application-adapter admission without changing the matcher
  regressed the focused run to 9.52 seconds because unusable rules remained in
  every matcher scan.
- Retaining deferred-validity rules and checking them at matcher boundaries
  also regressed, to 8.66 seconds and 25.52 GB. The additional scans and
  predicates cost more than the avoided probes.
- An ordered first-literal `Map` index combined with deferred validity was
  semantically correct for the focused test but regressed it to 8.89 seconds.
  Rebuilding indexes during scope advancement and merging ordered candidate
  buckets outweighed the savings at the current rule count. It was reverted.

## Remaining work, in priority order

### 1. Avoid eager adapter admission without retaining invalid rules

Compiled-let reuse is complete, but the first compilation of each recursive
let still evaluates simple-declaration implementations to decide whether they
produce a `SyntaxFunctionInsertion`. Most standard-library recursive lets are
ordinary types or values, so this is expensive negative discovery.

Do not repeat the reverted list-level deferred-validity or rebuilt `Map` index
experiments above. A successful design likely needs a persistent ordered index
maintained incrementally as rules are shadowed and introduced, with structural
candidate records that do not force adapter evaluation. Empty-prefix/hole-first
rules need an ordered fallback, and invalid rules must still shadow earlier
rules without participating in matching. Measure index maintenance separately
from candidate matching before integrating it with every block/continuation
query.

### 2. Fuse strict rewriting and validation

After discovery stabilizes, `rewriteSequence` currently walks a block once for
the strict pass and once again for validation. Both passes reconstruct the same
position-specific declaration scope, resolve the same declaration head, and
advance the same environment.

Either validate inline in `strictPass`, or make `strictPass` return per-entry
metadata containing:

- the position-specific `RewriteEnvironment`;
- the resolved declaration;
- the compiled/cached family; and
- the rewritten entry.

Validation should consume that metadata without another traversal or compile.
Keep the exact-family `Map` and dynamic-family index as validation state carried
through this single pass.

### 3. Remove the remaining quadratic declaration-list operations

Even after compilation is cached, the following list operations are formally
quadratic over a block:

- `scopedBlockDeclarations` scans all entries for every source position;
- it repeatedly concatenates `bindingNames` and rescans outer declarations for
  shadowing;
- `advanceScope` uses `retainedDeclarations <> [entry]`; and
- rule/declaration shadowing filters the entire accumulated list on each entry.

Use an incremental persistent representation rather than materializing every
prefix as a fresh list. A suitable structure should maintain:

- all recursive lets;
- the prefix of preceding ordinary declarations;
- a set/map of locally bound names for outer-shadow filtering; and
- source order for callbacks where declaration order is semantic.

A `Sequence` alone fixes append but not repeated filtering/conversion. Prefer a
small `DeclarationScope` abstraction with an ordered persistent collection and
a binding-name index. Change `SyntaxContext` callbacks to accept that scope or
a prepared closure; converting it back to `[Expression]` at every callback
would restore the same quadratic cost.

### 4. Index dynamic validation candidates

The literal-name map removes exact-versus-exact all-pairs validation. Dynamic
families are still kept in a list, and each new dynamic family can compare with
every earlier family.

Build a validation trie/index from each compiled syntax rule's literal prefix.
Use the same general principle as runtime lookup:

- rules with a nonempty static prefix enter the index;
- exact rules are simply full literal prefixes;
- rules with no static prefix enter a fallback bucket; and
- full `rewriteRulesOverlap` and semantic federation comparison run only for
  retrieved candidates.

The target complexity is proportional to total template size plus actual
candidate overlaps. Families beginning with an unconstrained hole may
legitimately overlap every declaration; that output-sensitive worst case cannot
be optimized away without a stronger semantic partition.

### 5. Prepare one lexical syntax scope per compiled family

`SyntaxContext` currently exposes separate `contextClassify`,
`contextEvaluate`, `contextEvaluateWithInput`, and `contextApply` callbacks.
The `Interpreting` implementation can rebuild the same declaration scope for
classification and evaluation.

Add a prepared context operation, conceptually:

```haskell
contextPrepare :: DeclarationScope -> PreparedSyntaxContext
```

where `PreparedSyntaxContext` holds classification/evaluation/application
closures sharing one declared `Scope`. Then `compileScopedRewriteRules` can
classify holes and evaluate an implementation without independently calling
`declareSyntaxScope`.

Do this after seed-family caching: the profile showed that repeated family
compilation dominates, while direct `declareSyntaxScope` construction was a
smaller child cost.

### 6. Avoid eagerly combining every dynamic view when `_this` is formed

`dynamicDependentDeclarationNamedView` itself is delayed: constructing it does
not evaluate capture schemas. However, `scopeEntriesNamedView` still folds all
declaration views together before replacing name lookup and containment with
the trie-backed operations. Thus forming `_this` can allocate one delayed view
shell per declaration even when the only later operation is a named lookup.

Replace this with one layer-level `NamedMapView`:

- `memberByName` and `containsName` should query the layer trie directly;
- ordinal, collection, and declared-member projections should lazily construct
  the existing combined dynamic view only if one of those projections is
  requested; and
- cache that combined projection once forced.

This preserves one uniform dynamic declaration implementation while making
named `_this.foo` access avoid an up-front O(n) view fold. It is a plausible
secondary optimization, but the current profile does not identify it as the
main remaining regression.

### 7. Revisit eager adapter inspection only if caching is insufficient

Compared with `master`, `compileScopedRewriteRules` now evaluates syntax-rule
implementations to determine syntax/runtime insertion capability. Haskell
thunks avoid some work, but the application-implementation validity guard
forces the syntax insertion for relevant rules.

First ensure each family is compiled only once. If the focused profile still
shows large eager adapter cost, split compilation into:

- structural template compilation;
- a memoized capability thunk; and
- forced validation only for rule forms that require it.

Do not return to evaluating the implementation separately for syntax expansion,
runtime insertion, and injectivity validation.

## Required scaling evidence

The focused test demonstrates the cold standard-library regression but does not
by itself prove asymptotic linearity. Add a focused benchmark or allocation
test that constructs blocks of `n`, `2n`, and `4n` nonoverlapping dependent
declarations, including:

- ordinary exact-name families;
- recursively seeded let families;
- literal-prefix template families; and
- a small fixed number of genuinely dynamic/no-prefix families.

Measure allocations rather than asserting wall-clock time in a normal unit
test. Doubling the number of nonoverlapping indexed declarations should
approximately double build/validation allocation, not quadruple it. Keep
dynamic fallback count fixed in the primary scaling case, then add a separate
output-sensitive case where every dynamic family can actually overlap.

Until that benchmark exists, inspect these specific functions for all-pairs or
repeated-prefix behavior:

```text
rewriteSequence
recursiveRewriteEnvironment
scopedBlockDeclarations
advanceScope / advanceScopeResolved
compileScopedRewriteRules
validateDependentDeclarations
scopeEntriesNamedView
dependentDeclarationCandidates
```

## Correctness constraints

- Exact literal names and template names must have the same runtime lookup
  semantics; the validator may index exact families specially.
- Computed/template families must remain available through the fallback path.
- Recursive lets are visible throughout their block, but their lexical capture
  snapshot remains tied to source position.
- Once seed discovery stabilizes, let families and retained eager-let values
  must be reused as ordinary cached families/values.
- Productive recursion must remain deferred rather than being eagerly forced.
- Ambiguity must still be reported when multiple candidate declarations match.
- Ordinal/manifest named-map behavior must remain lazy and transfinite-safe.
- Structural disjointness may avoid semantic comparison; structural overlap
  must still fall back to the federation check where required.
- Do not disable validation to obtain benchmark numbers.

## Warning cleanup completed in the current working tree

The profiling build exposed two pre-existing redundant-import warnings. The
current working tree fixes both:

1. Removed `import Numeric.Natural (Natural)` from
   `src/DatraTypes/Evaluation/Specification/String.hs`.
2. Removed `withInterpretedSemantics` and `interpretedSemantics` from the
   `Evaluation.Value` import list in `src/DatraTypes/DatraTypes.hs`; a normal
   build confirmed they were unused.

After the runtime changes, run at least:

```sh
cabal build test:datra-interpreting-test
```

and confirm no warnings originate from the touched modules. Do not run the full
suite repeatedly; repository guidance permits it at most once, and unrelated
failures are explicitly out of scope.

The focused `dependent declarations` Tasty case still reaches a known baseline
failure: its overlap assertion expects `OverlappingDependentDeclarations`, but
the current branch reports `InvalidSyntaxTemplate "pair 1 %Int"
SyntaxTemplateProjectionOrderMismatch`. Assertions earlier in that case pass.
Do not attribute this existing mismatch to the compiled-let cache without a
clean baseline comparison.

## Suggested completion checklist

- Preserve or replace the current exact-family validator index with measured
  evidence.
- Cache compiled let families after recursive seed discovery.
- Fuse strict traversal and validation, or prove why the second traversal is
  unavoidable.
- Replace repeated list-prefix/shadow scans with an incremental indexed scope.
- Add an allocation-based declaration-count scaling benchmark.
- Re-run the exact focused Tasty test and profiler against `master`.
- Demonstrate approximately linear allocation scaling.
- Fix the two redundant-import warnings.
- Run focused dependent-declaration overlap, injectivity, recursive-let, and
  `_this` named/ordinal access tests.
- Only then consider the performance goal complete.
