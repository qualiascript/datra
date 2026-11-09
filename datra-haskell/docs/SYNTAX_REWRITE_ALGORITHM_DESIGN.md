# Syntax rewrite algorithm: next steps

## Goal

Finish the stack-based syntax rewriter with one algorithm for ordinary
expressions, declarative-syntax phrases, and neutral sequences.

The stack owns:

- rewrite-node allocation and scheduling;
- structural candidate enumeration and greedy ordering;
- candidate child work, dependencies, and backtracking;
- incremental installation of finalized child results;
- incremental candidate type checks;
- expansion and finalization;
- the syntax-rule families visible at each rewrite locus;
- ordered syntax-rewrite diagnostics.

The evaluator/interpreter owns:

- dependent-declaration recognition;
- declaration-head interpretation;
- declaration lowering;
- family construction and validation;
- precedence, shadowing, overlap, and injectivity;
- recursive declaration semantics;
- declaration implementation evaluation;
- runtime function application and value evaluation.

Syntax rewriting receives evaluator-produced syntax-rule families and orders
work against them. It does not reproduce declaration semantics.

## Core invariants

1. A rewrite node owns one stable rewrite input.
2. A neutral sequence is supplied as one rewrite input, not one input per
   physical line or parser entry.
3. Candidate enumeration records every structural choice in semantic order.
4. A blocked candidate remains the active choice; later candidates are not
   tried until it accepts or rejects.
5. A rejected candidate advances the cursor in the node's candidate-search
   state.
6. Exhausting a required child rejects the active parent candidate.
7. Exhausting a parent propagates failure to the next active parent choice
   point.
8. A finalized child schedules its parent, which consumes that result on its
   next stack transition exactly once.
9. Candidate checks run when the required child result becomes available.
10. An accepted candidate expands exactly once.
11. Expansion is non-failing after acceptance.
12. A finalized node is never rematched.
13. Finalization returns the expression already stored by the node.
14. No end-of-rewrite rebuilding or validation pass exists.
15. Syntax families are published only from finalized results.
16. Declaration interpretation is never performed by the syntax rewriter.
17. The work stack contains only rewrite-node IDs; node state is the sole
    description of how a node continues.

## Rewrite inputs

A rewrite input is an `Expression`. For a block-like scope, that expression is
the complete neutral sequence container, such as an `AtlasMap`, `Begin`, or
`FunctionBody`.

Newline and semicolon boundaries remain parser-owned structure inside that
expression. They do not determine rewrite-node boundaries.

For example:

```datra
val Args := &T? do
  slots := (^_i :: Nat) do yield "arg%(_i)"? : T
yield ((^n? :: Nat) do yield slots[0..n])
```

The outer rewrite input contains the complete neutral sequence. Candidate
projection can therefore select the outer `do`, capture its `_Block`, find the
following `yield`, and retain the ordinary unmatched remainder using the same
candidate representation used for inline syntax.

## Rewrite node state

Conceptually, each node stores:

```haskell
data RewriteNode = RewriteNode
  { rewriteNodeSource :: Expression
  , rewriteNodeExpression :: Expression
  , rewriteNodeScope :: SyntaxScopeId
  , rewriteNodeParent :: Maybe RewriteNodeId
  , rewriteNodeState :: RewriteNodeState
  }

data RewriteNodeState
  = NodePending
  | NodeReady RewriteWork
  | NodeWaiting RewriteWork WaitCondition
  | NodeFinalized RewriteResult

data WaitCondition
  = WaitForChild RewriteNodeId
  | WaitForFamilies SyntaxScopeId

data RewriteWork
  = SearchCandidates CandidateSearch
  | TraverseChildren OrdinaryTraversal

data CandidateSearch = CandidateSearch
  { candidateSearchCandidates :: [StructuralCandidate]
  , candidateSearchCursor :: Int
  , candidateSearchRejections :: [CandidateRejection]
  , candidateSearchFrame :: Maybe CandidateFrame
  }

data OrdinaryTraversal = OrdinaryTraversal
  { ordinaryTraversalCursor :: Int }
```

`rewriteNodeSource` is immutable. `rewriteNodeExpression` is the incrementally
updated expression whose finalized children have already been installed.

`rewriteNodeScope` identifies the stack-owned syntax scope whose current
syntax families apply at that locus. The node does not copy that family set or
store a syntax-rewriter-owned declaration environment.

Candidate selection and ordinary traversal are mutually exclusive node modes.
The candidate cursor indexes alternative structural candidates and advances
only after rejection. The ordinary cursor indexes AST children and advances
only after a finalized child is installed. `RewriteWork` stores the complete
state for either mode, whether the node is ready or waiting.

A child stores only its parent node ID. The parent's `RewriteWork` identifies
whether that child is a candidate capture or an ordinary AST child and stores
the corresponding cursor. `WaitForChild` identifies the one active child; the
child-completion relationship is represented only by those two links.

## Structural candidates

A structural candidate contains the existing syntax choice:

```haskell
data StructuralCandidate = StructuralCandidate
  { structuralCandidateRule :: RewriteRule
  , structuralCandidateBranch :: Int
  , structuralCandidateProjection :: Int
  , structuralCandidateSelection
      :: TemplateSelection Expression Expression
  , structuralCandidateCaptures
      :: [(SyntaxHoleKind Expression, Expression)]
  , structuralCandidateRemaining :: [Expression]
  }
```

Candidate enumeration preserves:

1. syntax-family visibility and declaration order;
2. rule order;
3. longest applicable projection first;
4. template branch order;
5. longest capture first;
6. argumentative-map alternative order.

Enumeration is structural. It does not evaluate captures or declarations.

The same candidate fields are used for neutral sequences. Projection presents
the complete sequence to matching, and the selection, captures, and remainder
fully describe the choice.

## Candidate execution

For the candidate at `candidateSearchCursor`:

1. Create or resume its `CandidateFrame`.
2. Read the next unprocessed capture.
3. Allocate a child node for that capture if necessary.
4. Run the child above the parent frame on the stack.
5. When the child finalizes, consume its result once.
6. Check the syntax-hole requirement immediately.
7. Update the candidate's existing generic-function typing context.
8. Advance the capture cursor.
9. Repeat until all captures and the instantiated return type are known.
10. Accept or reject the candidate.

Completed capture checks and inferred generic inputs remain stored in the
candidate frame. The active candidate is identified by
`candidateSearchCandidates[candidateSearchCursor]`; `CandidateFrame` stores
only progress within that candidate. Resuming a candidate never repeats
completed work.

### Blocked

A candidate pauses either for its one active child or for its syntax scope's
syntax families.

The candidate frame, capture cursor, typing context, source selection, and
remainder remain in `SearchCandidates` while child work runs or syntax families
become available. Allocating a child changes the parent to
`NodeWaiting work (WaitForChild child)`. Waiting for family publication uses
`NodeWaiting work (WaitForFamilies scope)`.

### Rejected

Rejection records:

- the rule and branch;
- the capture index and source;
- the expected and actual result types;
- the generic typing context;
- the rejection reason;
- nested child rejections.

The node then advances to its next structural candidate. If no candidate
remains, failure updates the active work stored by its parent.

### Accepted

Acceptance requires:

- all captures finalized;
- all required syntax-hole checks completed;
- generic inputs propagated through the existing generic implementation;
- the instantiated return type established.

Expansion consumes the stored selection and finalized capture results. It
cannot perform another match or reject the accepted candidate. The expanded
expression is stored immediately on the same node. If the expansion introduces
unfinished child expressions, the node continues as `TraverseChildren`; its
already-finalized captures remain installed and are not scheduled again.

## Ordinary expression traversal

If no syntax candidate applies, the node traverses the actual AST children of
`rewriteNodeExpression` in source order.

For each child:

1. Allocate one child node with the appropriate visible syntax families.
2. Run it to finalization.
3. Replace that child in `rewriteNodeExpression` immediately.
4. Advance the ordinary-child cursor exactly once.

When no child remains, the current stored expression is the ordinary result.
The node does not collect child results for later reconstruction.

If a syntax expansion introduces an `AtlasMap`, `Begin`, or `FunctionBody`,
the expansion creates that expression once. Any unfinished nested children are
then rewritten and installed through the same ordinary traversal.

## Neutral sequences and syntax-family scope

A syntax scope represents the syntax-family visibility of one block-like
scope. It stores the interpreter-provided current syntax families and a
source-ordered collection of nodes waiting for that family view to change.

```haskell
data SyntaxScope = SyntaxScope
  { syntaxScopeFamilies :: [SyntaxRuleFamily]
  , syntaxScopeFamilyWaiters :: [RewriteNodeId]
  }
```

It does not split the source into one rewrite node per entry. Rewrite phrases
are established by ordinary structural candidate selection and AST child
traversal.

Sequence execution is:

1. Ask the interpreter for the initial and provisional recursive syntax
   families for the scope.
2. Allocate the complete sequence root with that scope ID and push its node ID.
3. Process child work in source order.
4. When a phrase at that scope finalizes, pass the finalized result to the
   interpreter's publication callback.
5. If the callback returns a new visible syntax-family set, store it on the
   scope, take and clear that scope's family waiters, and push them in reverse
   source order.
6. Continue the existing stack work without replaying finalized nodes.

Each awakened node is pushed with its `NodeWaiting work (WaitForFamilies
scope)` state intact. When popped, it observes the updated family view and
continues from the stored work. Family publication does not reset candidate
enumeration or completed candidate-frame work.

The publication callback may recognize a dependent declaration, lower it,
validate it, construct its family, and return the resulting syntax-family
view. Those actions occur behind the interpreter boundary. The syntax
rewriter only stores the returned families and schedules dependants.

For the `Args` example, the finalized outer result is
`val Args := <FunctionBody>`. The nested `slots` declaration is finalized and
published only in the nested function-body scope.

## Incremental validation

Every syntax-rewrite invariant is checked at the transition where its inputs
become available:

- a finalized child schedules its parent, and the parent consumes that result
  on its next transition;
- a typed hole is checked when its finalized child type is consumed;
- generic input propagation occurs when each capture completes;
- candidate return type instantiation occurs before acceptance;
- an accepted expansion is stored before any introduced child work is
  scheduled;
- syntax-family publication occurs when the relevant phrase finalizes;
- a node finalizes only when it has no active wait condition.

Root finalization is therefore the completed result, not a request to validate
or assemble it.

## Stack ownership

The scheduler is a LIFO stack of node IDs:

```haskell
type RewriteStack = [RewriteNodeId]
```

Popping a node dispatches from its stored state:

- `NodePending` enumerates candidates and becomes ready;
- `NodeReady (SearchCandidates search)` performs the next candidate transition;
- `NodeReady (TraverseChildren traversal)` performs the next ordinary-child
  transition;
- `NodeWaiting work (WaitForChild child)` consumes that child after the child
  schedules its parent;
- `NodeWaiting work (WaitForFamilies scope)` resumes after that scope schedules
  its family waiters;
- `NodeFinalized result` has no further work.

Every transition updates the node before pushing more IDs. Allocating a child
marks the parent as waiting and pushes the child ID. Finishing a child pushes
its parent ID; the parent consumes the child's stored result when it is popped.
Rejecting a candidate updates the candidate search and pushes the same node ID.
Publishing a changed family view pushes that scope's waiter IDs in reverse
source order so the LIFO stack pops them in source order. Root finalization
returns its stored result.

Failure propagation also updates and pushes the parent node: the parent's
stored work determines whether exhaustion rejects a candidate or terminates
the root search. It does not require a separate failure task.

Recursive helper calls may calculate local projections or type operations, but
they do not own rewrite scheduling.

## Diagnostics

Typing rejections are retained in semantic attempt order. A failed search with
one or more typing rejections reports those rejections before using the
unknown-identifier fallback.

Each diagnostic includes the attempted rule, selected branch, captured source,
expected type, actual finalized type, generic context, and nested rejection
path when present.

Errors returned by evaluator/interpreter callbacks remain evaluator/interpreter
errors. Syntax rewriting does not reinterpret them as candidate mismatches.

## Implementation order

### 1. Simplify the state model

- Remove the stale `RewriteEnvironment` abstraction and any remaining aliases
  for it.
- Keep one syntax-family view per syntax scope and store only its scope ID on
  each node.
- Move the candidate cursor, candidates, ordered rejections, and active
  candidate frame into `CandidateSearch`.
- Move the child cursor into `OrdinaryTraversal`.
- Store either mode as `RewriteWork` under `NodeReady` or `NodeWaiting`.
- Store only the parent node ID on a child; let the parent's `RewriteWork` own
  the capture or child position.
- Represent the one active child with `WaitForChild`; do not also register a
  `RewriteNodeResult` dependency or retain a second active-child field.
- Represent family waiting directly with `WaitForFamilies SyntaxScopeId` and one
  source-ordered waiter set per scope.
- Keep active candidate identity in `candidateSearchCandidates` plus
  `candidateSearchCursor`; keep only per-capture progress in `CandidateFrame`.
- Remove persistent `CandidateAttempt` variants: the active frame represents
  blocked work, ordered rejections represent failed attempts, and
  `RewriteResult` represents acceptance.
- Keep `StructuralCandidate` limited to rule, branch, projection, selection,
  captures, and remainder.

### 2. Simplify scheduling

- Make the work stack a list of `RewriteNodeId` values.
- Dispatch exclusively from `RewriteNodeState` when a node ID is popped.
- Remove action-specific `RewriteTask` constructors and specialized resume,
  sequence, and failure tasks.
- Push a child ID when it is allocated, a parent ID when its child finalizes,
  and the same node ID after an immediately continuing transition.
- Use parent linkage for child completion and the scope waiter table for family
  changes.
- Remove the generic dependency graph after its child-result and family-waiting
  cases have moved to those direct representations.

### 3. Stop splitting sequence input

- Change sequence entry so `AtlasMap`, `Begin`, and `FunctionBody` are supplied
  to the root node as complete expressions.
- Remove eager allocation of one node per sequence entry.
- Run structural candidate enumeration on the complete neutral sequence before
  ordinary child traversal.
- Ensure candidate projection exposes multiline block syntax to the existing
  matcher without adding a second candidate representation.
- Replace `SequenceFrame` with syntax-family scope state containing only the
  current families and ordered family waiters.

### 4. Make ordinary traversal fully incremental

- Retain the current expression on each node.
- Install each finalized child directly into that expression.
- Advance the stored child cursor after installation.
- Remove `rebuildOrdinaryExpression` and equivalent collected-child rebuilds.
- Finalize the stored expression when traversal completes.

### 5. Remove sequence assembly

- Remove `stackAssembleSequence`, `contextAssembleSequence`,
  `materializeSequence`, and equivalent end-of-sequence reconstruction.
- Keep sequence constructors produced by parsing or syntax expansion as the
  stable parent expression.
- Rewrite and install their children in place through the parent node's stored
  traversal work.

### 6. Keep declaration work behind the interpreter boundary

- Replace declaration-specific stack helpers with a syntax-family publication
  callback.
- Pass only finalized results and interpreter-owned scope inputs to that
  callback.
- Store only the returned syntax-family view.
- Push the selected scope's waiter IDs in reverse source order when that view
  changes.
- Keep recognition, lowering, validation, family construction, overlap,
  injectivity, and evaluation out of `SyntaxRewriting.*`.

### 7. Complete candidate execution

- Preserve candidate frames across child work.
- Consume each child result once.
- Propagate generic inputs incrementally.
- Store the instantiated candidate return type in `RewriteResult`.
- Expand an accepted candidate once into the node's stored expression.
- Continue with ordinary traversal only for unfinished children introduced by
  that expansion; never reschedule finalized captures.
- Propagate required-child exhaustion through the parent candidate work.

### 8. Remove stale paths

- Remove unused sequence replay, fixed-point, strict-pass, and rebuilding
  helpers.
- Remove obsolete operation-specific dependent-name paths.
- Remove stale tests which assert line-based rewrite boundaries or removed AST
  constructors.
- Keep one production path through the stack scheduler.

## Verification

Add focused tests in this order:

1. The parser produces `DependentArgument` for simple and templated dependent
   names and uses `MapSpecification` for `:=`.
2. Candidate enumeration sees the complete multiline `Args` neutral sequence.
3. The outer `do _Block yield _Expr` candidate captures the nested block and
   terminating expression correctly.
4. The inline nested `do yield` inside `slots` does not terminate the outer
   block capture.
5. A blocked earlier candidate prevents later candidates from running.
6. A rejected candidate advances to the next semantic choice.
7. Exhausting a required child rejects its active parent candidate.
8. A finalized child is installed once and is never rematched.
9. Typed-hole and generic checks occur as child results finalize.
10. Syntax-family publication wakes only that scope's family waiters and they
    resume in source order.
11. The outer `Args` declaration publishes only after its complete phrase
    finalizes; `slots` remains in the nested function-body scope.
12. Finalization performs no reconstruction or validation traversal.
13. Candidate rejection diagnostics retain semantic attempt order.

Then run the existing parser, type, and standard-library suites. During the
stack migration, unrelated WIP failures may remain, but every new focused test
must distinguish a syntax-rewriter failure from an evaluator/interpreter
failure.

## Completion criteria

- One stack algorithm handles ordinary expressions, syntax candidates, and
  complete neutral sequences.
- The work stack contains only node IDs; stored node state determines every
  transition.
- Candidate search and ordinary traversal share one `RewriteWork` scheduling
  path.
- Child completion uses parent linkage, and family waiting uses syntax-scope
  waiters; neither is duplicated in a generic dependency graph.
- Sequence input is never partitioned by physical line before matching.
- Syntax rewriting stores only evaluator-provided syntax families from
  declaration scope.
- Declaration recognition and semantics remain evaluator/interpreter-owned.
- Child installation and candidate validation are incremental.
- No ordinary-expression or sequence rebuilding path remains.
- No final validation pass remains.
- Accepted candidates expand once and finalized nodes are never rematched.
- Multiline `Args` reaches the correct finalized AST through the stack path.
- Stale AST and line-boundary tests are updated.
