# Syntax rewrite algorithm design

## Purpose

This document specifies a replacement for the current syntax-rewrite
algorithm. The replacement must preserve Datra's declaration, scope, overload,
generic, recursion, and protection semantics while making rewrite progress
explicit, dependency-driven, and measurable.

The design starts from the unmodified current implementation. It does not
depend on any in-progress `SyntaxRewriting` changes.

## Scope

The replacement owns:

- discovery and selection of dependent syntax declarations;
- capture validation;
- expansion of selected syntax;
- declaration discovery inside expanded syntax;
- ordering and retrying rewrites whose inputs are not yet available;
- compile-time recursion between declarations and rewrites;
- activation-deferred validation or selection that depends on a function
  activation;
- diagnostics and instrumentation for rewrite progress.

It does not change:

- Datra surface syntax;
- declaration precedence or argumentative-map ordering semantics;
- the single dependent-declaration scope model;
- generic `^`-binder protection and escape rules;
- runtime overload semantics;
- the meaning of `this`, `it`, `_this`, or `_it`;
- parser ownership of neutral AST boundaries.

## Problems in the current model

### Correctness

#### Stable rewrite shape is not authoritative

`rewriteSequence` discovers declarations by repeatedly rewriting a raw block
until its recursive declarations stabilize. The final strict phase then uses
the stable expressions to construct scopes but rewrites the raw entries again.

The second expansion can produce a different result from the expansion that
established the fixed point. A successful selection can therefore disappear
after declaration discovery has already relied on it.

#### Missing values are treated as failed matches

Capture callbacks return `Maybe Expression`. This collapses materially
different outcomes:

- the captured value is valid;
- the value is invalid for the requested hole;
- evaluation is blocked on a declaration which is still being assembled;
- evaluation depends on a function parameter or generic value which exists
  only during invocation;
- evaluation failed for an unrelated semantic reason.

Once these outcomes become `Nothing`, the matcher can only report that no
template matched. The resulting diagnostic is often a broad
`NoApplicableFunctionAlternative` or an unresolved syntax literal rather than
the actual dependency or validation failure.

#### Function-local captures are validated in the wrong phase

A function body is rewritten before its parameters have runtime values. Syntax
selection may still be structurally determined, but a typed capture can depend
on an ordinary parameter, a generic binder, `Args`, `it`, or another
activation-local value.

For example:

```datra
public := {_declarations : Collection _DeclarationEntry} do
  yield (
    ((&_declaration :: _declarations) do
      yield if _declaration._key[0] = "_" then () else _declaration),
  )
```

The `if` shape and its three source captures are available while rewriting the
function definition. The Bool value of the first capture is available only
when `_declaration` is bound. Treating the unavailable value as a rejected Bool
capture loses a valid selection.

#### Selection provenance is discarded

After matching, the current executable AST does not retain a first-class record
of:

- which rule was selected;
- which template branch matched;
- the source expression for each capture;
- which captures were validated;
- which captures still require a value;
- the declaration scope and rule-set version used for selection.

Later phases consequently reconstruct the selection from raw syntax or from a
string-key lookup. Reconstruction is not equivalent when captures are
non-canonical values, are lazy, or depend on runtime scope.

#### Dependencies are implicit and name-based at failure time

The evaluator reports an unavailable identifier only after attempting concrete
evaluation. The rewrite engine has no semantic edge from the blocked rewrite
to the declaration or binder occurrence that would satisfy it.

Names alone are insufficient because nested functions, shadowing, modules, and
recursive scopes may contain several distinct occurrences with the same
spelling. A dependency must target an occurrence identity in a particular
scope.

#### Recursion is handled by localized exceptions

Recursive `let` declarations require provisional scope and seed behavior.
Without a general dependency model, individual rewrite paths retain tentative
results or special-case cycles. These exceptions do not establish a common
rule for:

- legal seeded cycles;
- illegal cycles;
- changes to a recursive declaration's shape;
- invalidation of expressions which depend on that shape.

#### Candidate ordering can become incorrect when validation is deferred

Datra rule order and longest-match behavior are semantic. If the first
structural candidate has a capture whose value is unavailable, it cannot be
silently rejected in favor of a later candidate. It also cannot be accepted as
valid without retaining its validation obligation.

A deferred selection must preserve the complete ordered candidate decision,
not just one optimistic expansion.

#### Diagnostics lose the causal failure

Because blocking, rejection, and no-match share the same path, the user sees
the last generic failure rather than:

- the syntax site being rewritten;
- the candidate rule;
- the capture which failed;
- the missing declaration or activation;
- a dependency cycle;
- a non-convergent rewrite.

### Execution speed

#### Whole-block fixed-point passes repeat unchanged work

When one declaration changes, every entry in the block is rewritten again.
Entries whose source, declaration scope, and selected rule are unchanged still
repeat projection, rule filtering, matching, capture evaluation, expansion,
and child traversal.

#### The strict pass repeats selection and expansion

After the tentative fixed point, the strict pass begins from raw syntax. This
duplicates the expensive part of rewriting even when strict validation would
confirm the existing selection.

#### Nested sequences multiply retries

`rewriteSequence` is used by blocks, function bodies, maps, and syntax
expansions. A retry in an outer sequence can rebuild inner sequences which have
already stabilized, multiplying work with nesting depth.

#### Capture evaluation is repeated without dependency changes

An unavailable capture can be evaluated many times even though none of the
declarations or runtime values it depends on have changed. The implementation
has no dependency generation with which to suppress an identical retry.

#### Rule projection and expression facts are recomputed

Candidate projections, literal facts, rendered source forms, and template
classification are derived repeatedly for the same expression and rule set.
Some projection paths enumerate many equivalent candidates, making global
rescans disproportionately expensive.

#### There is no useful work accounting

Wall time alone cannot distinguish necessary evaluation from retries. The
current model does not expose stable counters for node attempts, candidate
matches, capture evaluations, invalidations, or dependency wakeups.

## Required properties of the replacement

The replacement must satisfy these invariants:

1. A selected syntax shape is never discarded merely because one of its value
   validations is not ready.
2. A deferred validation is never treated as accepted.
3. A rejected closed capture cannot survive through a tentative expansion.
4. Syntax precedence, rule order, longest-match behavior, and argumentative-map
   permutations are unchanged.
5. Dependencies refer to semantic occurrences, not identifier strings.
6. A node is retried only after one of its dependency generations changes or
   its containing scope is invalidated.
7. Compile-time cycles are either resolved through an explicitly legal seed or
   rejected with a cycle diagnostic.
8. Runtime dependencies remain owned by their function or contextual
   activation and cannot escape its protection boundary.
9. Finalization never performs an unrecorded second selection from raw syntax.
10. Rewriting the same source and dependency graph is deterministic.

## Proposed architecture

The algorithm consists of a ready stack, a rewrite-node table, and a dependency
graph.

```text
neutral AST
    |
    v
node indexing -----> semantic occurrence identities
    |
    v
ready stack <------ reverse dependency wakeups
    |
    v
rewrite attempts --> node state + stable selection/expansion
    |
    +-------------> compile-time dependency graph
    |
    +-------------> activation-deferred plans
    |
    v
final executable AST
```

The stack determines deterministic local execution order. The graph determines
which nodes need to run again.

## Semantic identities

The neutral scoped AST must assign identities before rewrite evaluation:

```haskell
newtype RewriteNodeId = RewriteNodeId Natural
newtype DeclarationOccurrenceId = DeclarationOccurrenceId Natural
newtype ParameterOccurrenceId = ParameterOccurrenceId Natural
```

Existing `GenericBinderId` remains the identity for generic binders.
Contextual dependencies use a role plus the owning activation identity rather
than a spelling such as `_it`.

Identities are stable for the lifetime of one rewrite operation. They are not
serialized and do not change Datra's public AST equality.

## Rewrite nodes

A node is the smallest source boundary which can be independently retried.
Block entries are always nodes. Nested syntax boundaries become nodes when
their selection or validation can block independently.

Conceptually:

```haskell
data RewriteNode = RewriteNode
  { rewriteNodeId :: RewriteNodeId
  , rewriteNodeSource :: Expression
  , rewriteNodePosition :: SourcePosition
  , rewriteNodeScope :: ScopeSnapshotId
  , rewriteNodeRuleSetGeneration :: Generation
  , rewriteNodeSelection :: Maybe SelectionRecord
  , rewriteNodeExpansion :: Maybe Expression
  , rewriteNodeObligations :: [ValidationObligation]
  , rewriteNodeState :: RewriteNodeState
  , rewriteNodeAttemptGeneration :: Generation
  }

data RewriteNodeState
  = Pending
  | Queued
  | Active
  | Blocked (Set DependencyKey)
  | Expanded
  | ActivationDeferred ActivationOwner
  | Rejected RewriteFailure
```

`SelectionRecord` contains the selected rule identity, template branch,
candidate boundary, ordered captures, and the rule-set generation. Expansion
uses this record directly; it does not rematch `rewriteNodeSource`.

## Dependency keys

```haskell
data DependencyKey
  = DeclarationShape DeclarationOccurrenceId
  | DeclarationValue DeclarationOccurrenceId
  | ParameterValue ParameterOccurrenceId
  | GenericValue GenericBinderId
  | ContextualValue ActivationOwner ContextualRole
  | RewriteResult RewriteNodeId
  | ModuleProjection ModuleOccurrenceId
```

Each key has a generation. Resolving or changing a key increments its
generation and enqueues its reverse dependants. Re-registering the same value
at the same generation does nothing.

The graph stores both directions:

```text
node -> dependencies
dependency -> dependent nodes
```

This supports targeted wakeups and transitive invalidation.

## Structured capture results

Capture validation must not return `Maybe`.

```haskell
data CaptureResult
  = CaptureAccepted Expression
  | CaptureRejected CaptureFailure
  | CaptureBlocked
      { captureSource :: Expression
      , captureDependencies :: Set DependencyKey
      }
```

`CaptureRejected` means the required values were available and did not satisfy
the hole. `CaptureBlocked` means the validation result is unknown because named
semantic dependencies are unavailable. Other evaluation failures remain
failures; they are not converted to dependencies unless the evaluator can
identify an exact satisfier.

## Candidate selection

Selection has two stages.

### Structural candidate enumeration

The matcher applies literal prefixes, syntax boundaries, longest-match rules,
and hole categories without evaluating value holes. It returns candidates in
the exact semantic order in which they must be considered.

```haskell
data SelectionCandidate = SelectionCandidate
  { candidateRule :: SyntaxRuleId
  , candidateBranch :: TemplateBranchId
  , candidateCaptures :: [CapturedSource]
  , candidateRemaining :: [Expression]
  }
```

### Candidate validation

Candidates are validated in order:

- the first fully accepted candidate is selected;
- a rejected candidate is removed;
- a blocked candidate prevents selection of later candidates unless the
  language can prove that every possible resolution produces the same
  selection and expansion;
- when selection is blocked, the ordered candidate list becomes part of the
  node's activation-deferred decision rather than being recomputed.

This preserves rule order when a value-dependent capture is unavailable.

## Ready-stack algorithm

### Initialization

1. Build the initial scope snapshots and semantic occurrence identities.
2. Create nodes for source-order block entries.
3. Push them in reverse source order so the first source entry is processed
   first.

### Attempting a node

For each popped node:

1. Verify that its scope and dependency generations still match its cached
   selection and expansion.
2. Enumerate structural candidates if no valid selection record exists.
3. Validate candidates and captures.
4. If a required dependency is unavailable, register edges and mark the node
   `Blocked`.
5. If a candidate is accepted, store its `SelectionRecord` and expand from that
   record.
6. Discover declarations and independently retryable children in the expansion.
7. Publish changed declaration shapes and rewrite results, incrementing only
   the affected generations.
8. Push newly ready child nodes before continuing with siblings.
9. Mark the node `Expanded` when all compile-time obligations are satisfied or
   explicitly deferred to an activation.

The attempt clears obsolete dependency edges before registering its current
ones.

### Wakeup

When a dependency generation changes, visit its reverse edges. Enqueue a
dependent node only when it is not already queued and at least one recorded
generation is stale.

### Quiescence

An empty ready stack means no node can currently make progress. It does not by
itself mean rewriting succeeded.

At quiescence:

1. If there are no blocked compile-time nodes, finalize.
2. Move activation-dependent nodes into their owning activation-deferred
   plans.
3. Compute strongly connected components of the remaining compile-time graph.
4. Process legal recursive components from their declared seeds.
5. Reject unseeded cycles.
6. Reject blocked acyclic components whose dependencies have no producer.
7. If processing a component publishes a new generation, resume the ready
   stack.

Rewriting is complete only when the stack is empty and every node is expanded,
activation-deferred, or rejected.

## Recursive components

A recursive component is legal only when its declarations provide the same
semantic seed required by ordinary recursive evaluation. Syntax rewriting does
not invent a seed.

Within a legal component:

1. install the seed declarations;
2. enqueue component nodes in deterministic source order;
3. publish declaration-shape generations after each structural change;
4. stop when every node's structural fingerprint and dependencies are stable;
5. report `NonConvergentRewrite` if the component revisits a prior graph state
   without stabilizing or exceeds a defensible safety limit.

Only dependants of the changed component are invalidated.

## Activation-deferred rewrite plans

An activation-deferred plan is necessary when candidate selection, capture
validation, or expansion genuinely requires a function-local value.

```haskell
data ActivationDeferredRewritePlan = ActivationDeferredRewritePlan
  { activationDeferredOwner :: ActivationOwner
  , activationDeferredNodes :: [ActivationDeferredRewriteNode]
  , activationDeferredDependencies :: Set ActivationDependency
  }
```

The plan retains ordered candidates and source captures. It does not contain a
raw block to run through the global rewriter again.

At function invocation:

1. install ordinary arguments, generic values, `Args`, and contextual values in
   the ordinary runtime scope;
2. satisfy the deferred dependency keys from that activation;
3. validate the recorded candidates and captures in semantic order;
4. execute the recorded syntax insertion or selected dependent-declaration
   insertion with the prepared argument;
5. evaluate the resulting expression;
6. discard the plan's activation state when the function returns.

If structural expansion does not depend on runtime values, it should be done at
compile time and only its validation guard should be activation-deferred. Full
runtime selection is reserved for nodes whose applicable candidate or
expansion really depends on activation values.

Values produced by activation-deferred rewrites remain subject to the existing
protection and handoff rules. The scheduler does not provide a route for a
protected generic value to escape.

## Finalization

Finalization traverses node results, not raw source. It verifies:

- every emitted expression comes from an expanded node;
- every closed capture has an accepted validation;
- every remaining validation belongs to an explicit activation-deferred plan;
- every selected rule still belongs to the recorded rule-set generation;
- declaration positions and shadowing relationships are consistent;
- no compile-time dependency edge remains unresolved;
- no surface syntax literal remains merely because a blocked match was treated
  as no match.

There is no final strict expansion pass. Strictness is represented by completed
validation obligations.

## Invalidation and caching

A node cache key contains:

- source-expression fingerprint;
- scope snapshot identity;
- rule-set generation;
- generations of registered dependencies.

Cached expression facts, projection candidates, and structural candidate lists
may be reused while this key is unchanged. Evaluated capture values may be
reused only when all of their dependency generations are unchanged.

Invalidation removes the node's expansion and downstream declaration-shape
publications, but retains its immutable source and identity. Reverse graph
edges identify the minimal transitive set to enqueue.

Source rendering is for diagnostics only and must not be used as a cache,
dependency, or binder identity.

## Determinism

Determinism is enforced by:

- source-order node allocation;
- LIFO child-before-sibling execution;
- declaration-order rule candidates;
- existing longest-capture ordering;
- sorted dependency wakeups by `RewriteNodeId`;
- stable SCC traversal order;
- generation increments only for structural changes.

Diagnostic output and graph dumps must use the same ordering.

## Diagnostics

New failures should retain causal information:

```haskell
data RewriteFailure
  = NoStructuralSyntaxCandidate Expression
  | CaptureValidationFailed SyntaxRuleId Int CaptureFailure
  | UnresolvedRewriteDependency RewriteNodeId DependencyKey
  | RewriteDependencyCycle [RewriteNodeId]
  | NonConvergentRewrite [RewriteNodeId]
  | ActivationDeferredRewriteEscaped ActivationOwner RewriteNodeId
```

User-facing diagnostics should include the source site, selected template when
known, capture position, and missing semantic occurrence. Broad function
alternative errors may still be correct for ordinary runtime overload failure,
but must not hide a rewrite dependency.

## Integration boundaries

### Parser and neutral AST

The parser continues to produce neutral syntax boundaries. A scoping pass adds
ephemeral ordinary declaration and parameter occurrence identities alongside
existing generic identities.

### Syntax template matching

Matching becomes a pure structural candidate enumerator. It must not call the
concrete evaluator or erase blocked capture results.

### Syntax rewriting

The replacement module owns nodes, the stack, dependency graph, selection
records, expansion, invalidation, and finalization.

### Interpreter

The interpreter exposes dependency-aware evaluation for rewrite validation:

```haskell
data RewriteEvaluation value
  = RewriteKnown value
  | RewriteBlocked (Set DependencyKey)
  | RewriteFailed InterpretingError
```

It also executes activation-deferred plans inside their owning activation and
continues to use `PreparedFunctionArgument` for already-selected runtime
insertions.

### Scope

There remains one dependent-declaration environment. Scope snapshots and
dependency identities index that environment; they do not create a parallel
name resolver.

## Observability

The replacement must expose debug counters without requiring ad hoc traces:

- nodes allocated;
- node attempts;
- successful selections;
- structural candidates considered;
- capture validations attempted, accepted, rejected, and blocked;
- dependency edges added and removed;
- wakeups and duplicate wakeups suppressed;
- invalidated nodes;
- recursive components and iterations;
- activation-deferred nodes created and executed;
- projection-cache and capture-cache hits;
- time spent in matching, capture evaluation, expansion, and finalization.

An optional deterministic graph dump should list nodes, states, generations,
dependencies, selected rules, and activation-deferred owners.

## Implementation plan

### Phase 1: behavioral contract and instrumentation

- Add focused tests for the acceptance cases below.
- Add counters to the current entrypoints to establish attempt and evaluation
  baselines.
- Define normalized AST comparison helpers for old/new equivalence testing.

### Phase 2: identities and structural selection

- Allocate ordinary declaration and parameter occurrence identities.
- Split structural candidate enumeration from capture evaluation.
- Introduce `SelectionCandidate`, `SelectionRecord`, and structured
  `CaptureResult`.

### Phase 3: scheduler and compile-time graph

- Implement node allocation, ready stack, dependency generations, reverse
  wakeups, and deterministic finalization in a new internal module.
- Support ordinary blocks and declaration discovery first.
- Add targeted invalidation and caching.

### Phase 4: recursion

- Add SCC classification.
- Connect legal recursive components to existing seed semantics.
- Add cycle and non-convergence diagnostics.

### Phase 5: activation-deferred rewrites

- Add activation-deferred validation for ordinary parameters and generic
  binders.
- Add contextual and `Args` activation dependencies.
- Attach activation-deferred plans to function values and execute them inside
  the owning activation.

### Phase 6: integration and removal

- Run old and new algorithms against the same non-blocked corpus and compare
  normalized results.
- Switch resource, standalone, block, and function-body rewriting to the new
  entrypoint.
- Remove whole-block fixed-point rescans and strict raw replay.
- Remove compatibility code after all acceptance gates pass.

## Acceptance criteria

### Correctness

The replacement is acceptable only when all of the following hold:

- Std loads successfully.
- `yield from 0 up` resolves its selected positional captures.
- Argumentative maps continue to accept every declared ordering; the
  alternatives `(0; "up") | ("up"; 0)` are not collapsed into positional
  unions.
- The `public` function shown above rewrites and executes without treating
  `_declaration` as an unknown global identifier.
- `%Int` syntax holes reject `Infinity`.
- Nat captures reject negative integers.
- `%IntLimit` accepts `Infinity`.
- A capture must still inhabit both its syntax-hole schema and the selected
  function domain.
- A blocked earlier rule is never skipped in favor of a later rule solely
  because its capture value is unavailable.
- Shadowed parameters with the same spelling produce distinct dependency
  edges and use the correct activation.
- Sequential generic bounds can depend on earlier generic binders.
- `Args` remains available in its function activation.
- `^`-protected binders cannot escape through an activation-deferred rewrite.
- Legal recursive `let` declarations converge and illegal unseeded cycles
  report a dependency cycle.
- Duplicate and overlapping dependent declarations retain their current
  diagnostics.
- Module-projected syntax and contextual `this`/`it` use the correct scope.
- The dependent-declaration, scope, closure, function, standard-library,
  parsing, core, types, and CLI suites pass.

### Determinism

- Rewriting the same source 100 times produces the same normalized AST,
  dependency graph dump, and diagnostics.
- Changing evaluation order through unrelated declaration insertion does not
  change selection results.
- Test execution with randomized map allocation or hash seeds does not change
  graph order or output.

### Work bounds

- A node with unchanged source, scope, rule-set generation, and dependency
  generations is attempted at most once.
- A blocked capture is not reevaluated until at least one recorded dependency
  generation changes.
- Finalization performs zero syntax-rule selections from raw source.
- Changing one declaration enqueues only graph dependants, verified by counter
  assertions in a block containing unrelated declarations.
- No compatibility path performs a whole-block strict replay.

### Performance

- A synthetic block with `N` independent declarations plus one late dependency
  exhibits near-linear rewrite work; doubling `N` may not increase node
  attempts by more than 2.2 times.
- A nested-block stress test performs no more than one unchanged attempt per
  node per dependency generation.
- On a fixed benchmark host, median rewrite-stage time over at least 10 runs
  must improve by at least 30% on the Std-loading benchmark relative to the
  instrumented baseline revision.
- Peak resident memory on the same benchmark may not regress by more than 10%.
- Performance results include node-attempt and capture-evaluation counts so a
  wall-time improvement cannot conceal increased repeated work.

### Diagnostics and maintainability

- Every blocked node in a graph dump names at least one exact dependency key.
- Every unresolved compile-time dependency produces a causal rewrite
  diagnostic rather than `NoApplicableFunctionAlternative`.
- Scheduler state is represented by explicit data types; no debug-only mutable
  global state or identifier-name convention is used.
- The old fixed-point/strict-replay implementation is removed after migration,
  leaving one production rewrite algorithm.

## Completion definition

The rewrite is complete when:

- all acceptance criteria pass;
- the new scheduler is the only production path;
- no compile-time node remains blocked at finalization;
- every runtime obligation belongs to a specific activation-deferred plan;
- benchmark and graph-counter results are recorded in the test-suite report;
- the implementation and diagnostics contain no name-based deferred-binding
  mechanism.
