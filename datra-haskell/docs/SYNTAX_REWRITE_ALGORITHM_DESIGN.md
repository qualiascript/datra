# Syntax rewrite algorithm design

## Purpose

This document specifies a replacement for the current syntax-rewrite execution
model.

The replacement is an internal refactor of syntax rewriting. It replaces
whole-sequence fixed-point passes and strict raw replay with an explicit stack
of rewrite nodes, candidate choice points, and rewrite-result dependencies.

The replacement does not introduce a new name resolver, evaluator, scope
model, executable AST, or runtime dependency system. Datra declarations,
function parameters, generics, `Args`, `this`, `it`, dependent declarations,
and protected values keep their current meanings and implementations.

## Scope

The replacement owns:

- allocation and ordering of internal rewrite nodes;
- ownership, reservation, and commitment of the neutral sequence spans consumed
  by those nodes;
- structural syntax-candidate enumeration;
- greedy candidate selection and parent-level backtracking;
- dependencies between rewrite nodes;
- matching finalized child result types against syntax-hole types;
- propagating candidate type checks through existing generic function
  contexts;
- retention of rejected candidate attempts;
- expansion of accepted candidates;
- publication of evaluator-provided syntax-rule families from finalized
  results;
- ordering and resumption of nodes whose inputs are not finalized;
- finalization from stored rewrite results rather than raw source;
- syntax-rewrite diagnostics when candidates were rejected by typing.

It does not change:

- parser ownership of neutral syntax boundaries;
- declaration lookup, precedence, shadowing, or scope semantics;
- dependent-declaration representation or evaluation;
- dependent-declaration recognition, validation, lowering, family
  construction, or shadowing;
- function activation or parameter binding;
- generic-binder allocation or protection;
- `Args`, `this`, `it`, `_this`, or `_it`;
- syntax-function or runtime-function insertion semantics;
- runtime overload behavior;
- module projection;
- public source rendering.

`SyntaxRewriting` remains the public integration boundary. The implementation
may be divided into internal `SyntaxRewriting.*` modules.

### Dependent arguments are neutral syntax, not rewrite state

The neutral AST has one dependent-argument form for every name family:

```haskell
DependentArgument
  :: Expression       -- name or name-family expression
  -> Maybe Expression -- explicit type annotation
  -> Expression
```

Simple names and template names do not use separate AST constructors.
Assignment is ordinary specification syntax rather than another field on the
dependent argument:

```text
x : T       -> DependentArgument x (Just T)
x := value  -> MapSpecification value (DependentArgument x Nothing)
x : T := v  -> MapSpecification v (DependentArgument x (Just T))
```

In particular, inferred assignment stores `value` once. Rewriting cannot
rewrite one copy and later compare or rebuild it against a stale duplicate.
The evaluator interprets the missing annotation from the supplied
specification value. Dependent-declaration recognition likewise remains an
evaluator/interpreter concern: an inferred specification may be a declaration
in block position, while syntax rewriting sees only ordinary AST structure.

### Neutral sequence boundaries are not rewrite-node boundaries

The parser may retain a completed newline- or semicolon-separated expression
as one entry in a neutral `AtlasMap`. That separator is useful source structure,
but it does not prove that the entry is a complete declarative-syntax phrase.
In particular, it must not cause syntax rewriting to allocate and finalize one
independent node per source line.

For example, the standard `do` syntax is declared as:

```datra
%($do; _Block; $yield; _Expr)
```

and `Args` uses it across neutral sequence entries:

```datra
val Args := &T? do
  slots := (^_i :: Nat) do yield "arg%(_i)"? : T
yield ((^n? :: Nat) do yield slots[0..n])
```

Here `do` begins inside the first entry, `_Block` captures following entries,
and `yield` terminates that capture in a later entry. The complete outer entry
is the finalized `val Args := <FunctionBody>` declaration, not any one parsed
line. Publishing the first line independently would expose an incomplete
declaration and make the `do` candidate impossible to own correctly.

The governing invariant is:

> Rewrite nodes correspond to selected syntax phrases or ordinary expressions,
> not source lines. Neutral sequence-entry boundaries are matching structure,
> and the stack decides when a finalized phrase has consumed one or more
> entries.

The parser continues to own neutral parentheses, maps, separators, and other
source boundaries. Syntax templates decide how those boundaries may be
consumed: a block hole may capture an ordered entry span up to a following
literal such as `yield`, while an ordinary expression hole does not acquire
unrestricted permission to consume unrelated entries.

## Problems in the current execution model

### Stable rewrite results are discarded

`rewriteSequence` repeatedly rewrites a raw block until its recursive
declarations stabilize. It then constructs scopes from the stable expressions
but performs a strict pass over the original raw entries.

The second rewrite can produce a different result from the rewrite that
established the stable block. A syntax form selected during the tentative pass
can disappear when strict replay tries to evaluate a capture whose type can be
established structurally but whose ordinary value is not available while the
function body is being rewritten.

The `public` failure is an example:

```datra
if _declaration.key[0] = "" then () else _declaration
```

The `if` syntax is found during the tentative pass. Strict raw replay later
tries to obtain the value of the condition before `_declaration` has an
invocation value and discards the established rewrite.

The rewrite decision does not require that value. The inner `=` candidate has
return type `Bool`, and the `if` condition hole expects `Bool`.

### Whole-sequence fixed points repeat unrelated work

When one rewritten entry reveals a declaration, every raw entry is rewritten
again. Nested sequences multiply this work. Entries whose candidates, child
results, and syntax scope have not changed still repeat matching, capture
checks, expansion, and traversal.

### Raw sequence entries are mistaken for rewrite nodes

Allocating one rewrite node for every neutral sequence entry commits to a node
boundary before structural candidate selection has established the phrase's
extent. This fails for block syntax whose leading literal occurs inside one
entry and whose block and terminating literal occur in later entries.

The stack must instead retain the ordered neutral sequence, begin matching at
the current sequence position, and let each structural candidate record the
span it would consume. A blocked candidate keeps that tentative span reserved.
A rejected candidate releases it before the next candidate is tried. Only a
finalized result commits the span and advances the sequence beyond it.

### Greedy matching crosses node boundaries

Syntax matching is greedy, but its choice points are nested. A candidate for a
parent node may require child nodes to establish the result types of captured
expressions.

If every candidate for a required child is rejected, the failure rejects the
active parent candidate. Matching then tries the parent's next candidate. If
the parent also exhausts its candidates, failure continues to the next active
parent choice point.

This backtracking is currently implicit in recursive matcher control flow. The
replacement must represent it explicitly.

### Candidate rejection information is lost

When candidate matching ultimately fails, a user can receive an unknown
identifier even though several syntax candidates were considered and rejected
for specific typing reasons.

The replacement must retain every candidate rejected by a type mismatch. If
rewriting fails and any such rejection exists for the failed search, the
diagnostic reports the attempted candidates and their rejection reasons.
Unknown identifier is used only when no candidate was rejected by typing.

## Required properties

The replacement must satisfy these invariants:

1. A candidate is accepted as soon as all of its required child results prove
   that it applies.
2. An accepted candidate is expanded exactly once and its node is finalized.
3. A finalized node is never returned to candidate selection.
4. A blocked candidate is not skipped in favor of a later candidate.
5. A rejected candidate advances to the next candidate in greedy order.
6. Exhausting a required child's candidates rejects the active parent
   candidate.
7. Exhausting a parent's candidates propagates failure to the next active
   parent choice point.
8. Candidate order preserves declaration order, longest-match behavior,
   template-branch order, and argumentative-map alternatives.
9. Expansion is the final, non-failing materialization of an accepted
   selection.
10. Finalization consumes stored rewrite results and never rematches raw
    syntax.
11. Declarations are published only from finalized results.
12. Rewriting the same source and scope is deterministic.
13. Typing rejections take diagnostic precedence over an unknown-identifier
    fallback.
14. A generic candidate publishes its instantiated return type, not its
    uninstantiated declared codomain.
15. An unresolved generic typing context suspends one candidate frame while
    child frames run; continuing that frame never repeats completed checks.
16. Existing Datra scope, declaration, generic, protection, and runtime
    semantics remain unchanged.
17. A newline or semicolon retained as a neutral sequence separator does not by
    itself create a rewrite-node boundary.
18. A candidate may start at a focus inside the current entry and consume a
    following entry span when its template, such as a block hole followed by a
    delimiter, requires that structure.
19. Entries tentatively claimed by a blocked candidate are not independently
    finalized or published by overlapping nodes.
20. A sequence advances and publishes evaluator-provided families only from
    the finalized phrase which committed the corresponding source span.

## Proposed module structure

```text
SyntaxRewriting
  public entrypoints and integration

SyntaxRewriting.Types
  nodes, results, candidates, dependencies, and stack tasks

SyntaxRewriting.Candidates
  structural enumeration, generic type propagation, and rejection records

SyntaxRewriting.Stack
  work stack, greedy choice points, and failure propagation

SyntaxRewriting.Dependencies
  node-result edges and reverse wakeups

SyntaxRewriting.Sequence
  block scheduling and syntax-family publication

SyntaxRewriting.Expansion
  final materialization of accepted candidates

SyntaxRewriting.Diagnostics
  ordered candidate-rejection reporting
```

The exact file split may change during extraction. Candidate enumeration,
stack execution, dependency wakeups, sequence scheduling, expansion, and
diagnostic selection should remain separate responsibilities.

## Rewrite nodes and results

A rewrite node is an internal wrapper around one rewrite locus. An ordinary
locus is an existing `Expression`; a sequence-aware locus also has access to
the unconsumed neutral sequence continuation needed to establish the complete
phrase. A rewrite node is not an AST constructor, and its identity must not be
derived mechanically from a physical source line.

Conceptually:

```haskell
newtype RewriteNodeId = RewriteNodeId Int

data RewriteNode = RewriteNode
  { rewriteNodeId :: RewriteNodeId
  , rewriteNodeSource :: Expression
  , rewriteNodeContext :: SyntaxContext
  , rewriteNodeCandidates :: [StructuralCandidate]
  , rewriteNodeAttempts :: [CandidateAttempt]
  , rewriteNodeCandidateCursor :: Int
  , rewriteNodeExpression :: Expression
  , rewriteNodeChildCursor :: Int
  , rewriteNodeParent :: Maybe CandidateContinuation
  , rewriteNodeState :: RewriteNodeState
  }

data RewriteNodeState
  = NodePending
  | NodeActive
  | NodeWaiting (Set RewriteDependency)
  | NodeFinalized RewriteResult
```

The states mean:

- `NodePending`: the node exists and has not begun its current work;
- `NodeActive`: the node is testing candidates in greedy order;
- `NodeWaiting`: the current candidate cannot be decided until dependencies
  finalize;
- `NodeFinalized`: the node has its stable result and will never be matched
  again.

For sequence-aware work, the active structural candidate also retains its
tentative source span. The span may begin at a focus within the current entry
and end in a later entry. It remains candidate state until the enclosing entry
result finalizes; only then may the sequence frame commit it. Parent and child
continuations therefore install finalized results incrementally without
reparsing or reconstructing the claimed source.

Rewriting failure is a result of the scheduler, not a persistent node state:

```haskell
runRewrite
  :: SyntaxContext
  -> Expression
  -> Either RewriteFailure RewriteResult
```

When a non-root node exhausts its candidates, failure propagates to its active
parent continuation. When a root node exhausts its candidates, the whole
rewrite fails.

### Finalized rewrite results

A finalized node publishes both its rewritten expression and the result type
established by its selected candidate:

```haskell
data RewriteResult = RewriteResult
  { rewriteResultExpression :: Expression
  , rewriteResultType :: Maybe InterpretedValue
  , rewriteResultSelection :: Maybe SelectedCandidate
  }
```

`rewriteResultType` is the existing Datra value/federation used to classify the
candidate's return type. It is not the runtime value of
`rewriteResultExpression`.

Syntax-selected nodes publish the return type of the selected rule after its
generic function context has been resolved from the finalized types of its
captured children. For a non-generic rule this is its ordinary declared return
type. Ordinary nodes which do not establish a syntax result may publish no
type. Parent candidates only depend on a child type when a hole or generic
context requires one.

## Structural candidates

Structural enumeration produces every candidate in the exact order required
by current syntax semantics:

1. rules in declaration order;
2. longest applicable expression prefix first;
3. longest capture first within a hole;
4. existing template-branch order;
5. existing argumentative-map and projection alternatives.

Conceptually:

```haskell
data StructuralCandidate = StructuralCandidate
  { structuralCandidateRule :: RewriteRule
  , structuralCandidateBranch :: Int
  , structuralCandidateCapturedSource :: [Expression]
  , structuralCandidateRemaining :: [Expression]
  , structuralCandidateSequenceSpan :: Maybe SequenceSpan
  }
```

Enumeration records source captures but does not evaluate their runtime
values. This is a refactor of `SyntaxTemplateMatching`, not a new matching
language.

`structuralCandidateSequenceSpan` is present only when the candidate consumes
neutral sequence continuation outside its initial expression focus. It records
the tentative extent; it does not mutate the sequence cursor. Different
candidates at the same choice point may claim different extents according to
the existing longest-match order.

The ordered list is also the complete backtracking order. The next choice may
be another rule, template branch, projection, argumentative-map alternative,
or shorter greedy capture.

## Candidate attempts

```haskell
data CandidateAttempt
  = CandidateAccepted SelectedCandidate
  | CandidateBlocked
      StructuralCandidate
      CandidateFrame
      (Set RewriteDependency)
  | CandidateRejected CandidateRejection
```

### Accepted

Every literal, category, and typed-hole requirement has been established. The
selection is complete and expansion happens immediately.

### Blocked

The candidate could apply, but one or more required rewrite results are not
finalized. The node records dependencies and waits. Later candidates are not
tried while an earlier candidate is blocked.

The blocked candidate's frame remains on the stack with its current capture
cursor and typing context. Child frames run above it. When they finish, the
parent frame continues at its next unfinished check. It does not enumerate the
candidate again or repeat checks already recorded in the frame. No later
candidate is considered until the current candidate is accepted or rejected.
Any tentative sequence span owned by that candidate remains reserved for the
same duration, so overlapping entries cannot be scheduled as unrelated work.

### Rejected

Available results establish that the candidate cannot apply. The rejection is
retained and the candidate cursor advances.

A typing rejection records at least:

```haskell
data CandidateRejection = CandidateRejection
  { candidateRejectionRule :: RewriteRule
  , candidateRejectionBranch :: Int
  , candidateRejectionCaptureIndex :: Int
  , candidateRejectionSource :: Expression
  , candidateRejectionExpected :: InterpretedValue
  , candidateRejectionActual :: InterpretedValue
  , candidateRejectionChildren :: [CandidateRejection]
  }
```

The child list preserves nested rejection paths when exhausting a child
rejects an active parent candidate. The final representation may store stable
rule labels rather than the complete `RewriteRule`, but it must preserve every
attempted candidate and reason in semantic order.

Structural non-candidates are not typing rejections. A candidate which is
blocked is not recorded as rejected unless its finalized dependencies later
prove a mismatch.

## Typed-hole checks

A typed hole is checked against the finalized return type of its child node.

If the child is not finalized, the parent candidate becomes blocked on that
node. If the child is finalized, the check is:

```text
child candidate return type ⊆ expected hole type
```

The implementation uses Datra's existing subfederation relation. It does not
evaluate the child's runtime expression.

For example:

```datra
if _declaration.key[0] = "" then () else _declaration
```

The outer `if` candidate expects `Bool` for its condition hole. Its condition
node selects `=`, whose return type is always `Bool`:

```text
actual return type:  Bool
expected hole type: Bool
Bool ⊆ Bool
```

The condition is accepted without obtaining a runtime value for
`_declaration`. The outer `if` candidate can then be accepted and finalized.

This rule applies generally. A child result may be more specific than the hole
type as long as its return federation is a subfederation of the expected one.

## Generic candidate typing contexts

Some dependent declarations select generic functions whose return type depends
on the types of their captured values. In that case, candidate checking cannot
compare the declaration's uninstantiated codomain directly with the parent
hole type.

The candidate has one persistent stack frame while its children are being
rewritten:

```haskell
data CandidateFrame = CandidateFrame
  { candidateFrameCandidate :: StructuralCandidate
  , candidateFrameNextCapture :: Int
  , candidateFrameTypingContext :: CandidateTypingContext
  }

data CandidateTypingContext = CandidateTypingContext
  { candidateTypingInputs :: Map Int InterpretedValue
  , candidateTypingExpectedHoles :: Map Int InterpretedValue
  , candidateTypingReturnType :: Maybe InterpretedValue
  }
```

`candidateFrameNextCapture` is a monotonic cursor. Completed capture checks and
inferred generic inputs stay in `candidateFrameTypingContext`. Continuing a
frame never restarts from the first capture.

This is stack state around Datra's existing generic function preparation and
inference. It does not introduce new generic identifiers, bounds, or resolution
rules.

Candidate typing proceeds in capture order:

1. Use each finalized child result type as the type of that captured input.
2. Feed the known input types through the selected function's existing generic
   argument and bound checks.
3. Instantiate any later hole types which depend on the generic values already
   established.
4. Propagate those instantiated expected types to the corresponding child
   checks.
5. Instantiate the candidate's return type when enough input types are known.
6. Compare the instantiated return type with the parent hole type using the
   existing subfederation relation.

If a required child type is unavailable, the candidate frame records a
`RewriteNodeResult` dependency and remains below that child on the work stack.
The child performs its own single candidate traversal. When the child
finalizes, the parent frame consumes its result, advances its cursor, and
continues. Resolving one child can determine the expected type of a later
capture, which is then pushed as the next child frame.

```text
candidate frame at capture A
  -> needs child A type
  -> push child A frame
  -> child A finalizes
  -> pop child A frame
  -> generic argument becomes known
  -> advance parent cursor
  -> later hole type is instantiated
  -> push child B frame under that hole type
  -> child B finalizes
  -> pop child B frame
  -> return type is instantiated
  -> final parent-hole subfederation check
```

This is one depth-first traversal of one candidate. The frame can be suspended
behind several nested child frames, but candidate enumeration, completed
capture checks, and established generic arguments are not redone. This is not
a whole-sequence fixed point and does not rewrite finalized unrelated nodes.

For example:

```text
((abc ^^ def) %% (ghi ^^ jkl))
```

The outer `%%` candidate frame waits below the frames needed for its operands.
The left `^^` frame waits below the identifier nodes for `abc` and `def`; the
right `^^` frame similarly depends on `ghi` and `jkl`. During the left descent,
the outer and left operator candidates can both be blocked on the stack:

```text
%% candidate frame (blocked)
  ^^ left candidate frame (blocked)
    abc or def leaf work
```

After the left result finalizes, the stack descends through the right side:

```text
%% candidate frame (blocked)
  ^^ right candidate frame (blocked)
    ghi or jkl leaf work
```

As leaf types finalize, each inner frame unwinds into its parent. Each `^^`
frame computes its instantiated return type once, and the `%%` frame consumes
the two finalized operand types once. No candidate is restarted merely because
its children were nested or generic.

The candidate is accepted only when:

- every required child type is finalized;
- generic arguments and bounds are satisfied;
- every dependent hole type has been instantiated and checked;
- the instantiated return type is known; and
- that return type satisfies the parent hole, when a parent hole exists.

A generic mismatch produces a `CandidateRejection` containing the instantiated
expected and actual types. An unresolved generic input blocks the candidate;
it is not a rejection. Once accepted, `rewriteResultType` stores the
instantiated return type, so the candidate's parent can continue the same
process recursively.

## Rewrite dependencies

Dependencies describe rewrite ordering, not Datra identifier or runtime-value
dependencies.

```haskell
data RewriteDependency
  = RewriteNodeResult RewriteNodeId
  | SequenceFamilies SequenceId
```

### Node-result dependency

`RewriteNodeResult child` means that the active candidate requires the child's
finalized result, usually to check a typed hole.

The dependency graph stores reverse edges so finalizing a child wakes only the
parents which require it.

### Sequence-family dependency

`SequenceFamilies sequence` means that a node cannot determine its syntax
candidates until the interpreter-owned family context in the containing
sequence makes further progress or completes.

When a finalized node publishes a new declaration or syntax rule, dependants
of that sequence-family context are resumed. Implementations may later replace
this coarse edge with exact family edges as an optimization. This does not
change matching behavior or give the scheduler ownership of declaration
recognition.

There is no general semantic dependency graph and no name-based deferred
binding mechanism.

## Greedy choice points and backtracking

Every active node is a greedy choice point. Its candidate cursor identifies
the current candidate in the already-ordered list.

Trying a candidate may activate child nodes. The parent candidate remains
active while those children run.

Child completion has three outcomes:

- a compatible finalized result advances the parent candidate's generic typing
  context and allows checking to continue;
- an unresolved child blocks the parent on `RewriteNodeResult child`;
- exhaustion of the child's candidates rejects the active parent candidate.

Advancing a generic typing context may reveal another required child. The
parent frame advances its capture cursor and pushes that child. Previously
completed checks remain stored in the frame until its instantiated return type
is known.

Rejection advances the parent's cursor. If the parent exhausts its candidates,
failure propagates to the candidate which activated that parent.

```text
parent candidate 1
  -> required child exhausts its candidates
  -> record rejection of parent candidate 1
  -> try parent candidate 2

parent candidates exhausted
  -> reject the candidate which activated that parent
  -> resume the next choice at the next active parent
```

Blocked and rejected are deliberately different:

```text
blocked  -> preserve the current candidate and wait
rejected -> record the reason and try the next candidate
accepted -> expand and finalize
```

Child results are immutable once finalized and may be reused by later parent
candidates.

## Rewrite stack

The scheduler is an explicit LIFO stack:

```haskell
data RewriteTask
  = EnterNode RewriteNodeId
  | TryCandidate RewriteNodeId Int
  | ResumeCandidate RewriteNodeId Int
  | PropagateFailure RewriteNodeId [CandidateRejection]
  | EnterSequence SequenceId
  | ResumeSequence SequenceId RewriteNodeId
  | FinalizeSequence SequenceId
```

The stack order is deterministic:

- sequence positions are considered in source order;
- a node is allocated from the current unconsumed position rather than from
  every entry in advance;
- a candidate's tentative sequence span remains reserved until the candidate
  is rejected or its containing phrase finalizes;
- child work is pushed before its parent continuation;
- dependencies wake parents in source-node order;
- candidate cursors always advance through the stored semantic order.

### Attempting a node

When a node is entered:

1. Mark it active.
2. Enumerate structural candidates if they are not already stored.
3. Try the candidate at the current cursor.
4. Schedule any child nodes required to establish its captures.
5. If a required result is unavailable, record dependencies and wait.
6. When a dependency finalizes, continue the stored candidate frame from its
   current capture cursor.
7. Consume the finalized child type once through the candidate's existing
   generic function context.
8. If that establishes the expected type of another child, advance the cursor
   and push that child without repeating completed checks.
9. Reject and record the candidate if a literal, category, generic bound, or
   instantiated typed-hole check fails.
10. Advance the cursor after rejection.
11. Propagate failure to the active parent if all candidates are exhausted.
12. Accept the candidate once all checks and its instantiated return type are
    resolved.
13. Expand it and finalize the node.

An ordinary node stores its current expression and a monotonic child cursor.
Each finalized child is installed immediately into that stored expression and
advances the cursor exactly once. There is no end-of-pass ordinary-expression
rebuild. Its lack of a syntax candidate is not itself a failure unless an
active parent requires that node to establish a matching result.

## Expansion

Expansion is the last operation for an accepted candidate. It consumes the
stored selection and finalized child results and produces the stable
`Expression` stored in `NodeFinalized`.

Expansion cannot reject the candidate or return to matching. All work needed
to decide the candidate, including generic type propagation and return-type
instantiation, must already have completed.

If syntax insertion introduces nested expressions that require rewriting,
those expressions are allocated as dependencies during candidate preparation
and finalized before acceptance. Final expansion only assembles their stored
results.

An expansion failure after acceptance would be an implementation invariant
violation, not a reason to try another syntax candidate.

## Sequence scheduling

A sequence frame owns the ordered neutral entries for one block-like scope. It
does not initially turn those entries into independently owned nodes:

```haskell
data SequenceFrame = SequenceFrame
  { sequenceSource :: [Expression]
  , sequenceCursor :: SequencePosition
  , sequenceActiveSpan :: Maybe (RewriteNodeId, SequenceSpan)
  , sequenceContext :: SyntaxContext
  , sequenceWaitingNodes :: [RewriteNodeId]
  , sequenceResults :: [RewriteResult]
  }
```

`SequencePosition` is a logical position in the neutral sequence and may carry
an expression focus within its current entry. `SequenceSpan` is the source
extent tentatively consumed by a candidate. These are scheduler concepts, not
new AST nodes or declaration representations; their exact implementation may
be a zipper, stable paths, or an equivalent stack-owned continuation.

Initialization:

1. Retain the ordered raw entries and place the cursor at the first unconsumed
   position.
2. Ask the interpreter for the provisional recursive family context.
3. Allocate work lazily at the cursor, exposing the unconsumed continuation to
   structural matching.

At a sequence position:

1. Enumerate candidates from the current expression focus and, where the
   template permits it, the following neutral entries.
2. Record the candidate's tentative span without advancing the frame cursor.
3. Run captured child work above the stored candidate frame.
4. If the candidate blocks, preserve both its typing progress and span claim.
5. If it rejects, release the claim and try the next candidate, which may have
   a different extent.
6. If the containing phrase finalizes, commit its span, append its stored
   result, and advance to the first unconsumed position.

If no sequence-spanning syntax applies, the ordinary expression at the cursor
forms the next rewrite locus and commits its single-entry extent when it
finalizes. Nested block captures create nested sequence frames; their entries
are not also scheduled as peers of the containing outer phrase.

When a finalized result introduces a syntax family:

1. Ask the interpreter-owned context for the next visible family context.
2. Resume nodes waiting on `SequenceFamilies` for that sequence.
3. Leave all unrelated finalized nodes unchanged.

Family publication occurs only after the complete phrase commits. For the
multiline `Args` example, the outer sequence publishes the finalized
`val Args := <FunctionBody>` result. The captured `slots` declaration belongs
to the nested function-body frame and is never published as an outer sibling.

The rewrite scheduler stores and orders the returned syntax families. It does
not recognize dependent declarations, resolve declaration heads, construct or
validate families, check overlap or injectivity, lower declarations, or
evaluate declaration implementations. Those operations remain entirely in
the evaluator/interpreter.

When family publication completes, remaining sequence-family dependants
receive the completed family context. If they still exhaust their candidates,
ordinary parent backtracking or root failure applies.

Recursive `let` declarations continue to use the existing provisional-scope
and seed behavior. The scheduler does not add another recursion model.

A nested sequence is processed before its parent candidate resumes. Its
finalized results may establish the parent candidate; exhausting a required
nested match rejects the active parent candidate.

## Failure diagnostics

Candidate typing rejections are accumulated for the currently failing search
tree. Rejections from unrelated nodes which later succeeded do not affect an
error.

The rewrite failure decision is:

```text
failed search has one or more typing rejections
    -> report every attempted candidate and its rejection reason

failed search has no typing rejections
    -> report unknown identifier through the existing fallback
```

Conceptually:

```haskell
data RewriteFailure
  = RejectedSyntaxCandidates
      { rejectedSyntaxSource :: Expression
      , rejectedSyntaxAttempts :: [CandidateRejection]
      }
  | UnknownSyntaxIdentifier Expression
  | ExistingSyntaxRewriteFailure SyntaxRewriteFailure
```

The diagnostic preserves semantic attempt order. Each attempted candidate
reports:

- the rule and template branch;
- the captured source involved;
- the expected hole type;
- the actual finalized child or instantiated candidate return type;
- the resolved generic typing context relevant to the mismatch;
- nested child rejection reasons, when applicable.

For example, an `if` candidate whose condition finalizes to `Int` reports that
candidate and the failed `Int ⊆ Bool` check. It must not fall through to an
unknown identifier for `if`.

Existing specific rewrite failures, such as invalid declaration modifiers or
overlapping declarations, remain specific failures. Candidate-rejection
precedence applies to the generic unknown-identifier fallback; it does not
erase a different causal error.

## Finalization

Rewriting succeeds when every required node is `NodeFinalized` and the work
stack is empty.

Finalization is a terminal stack transition, not an assembly or validation
pass. The transition returns the result already stored by the finalized root.
The scheduler enforces its invariants incrementally at the transition which
could violate them:

- a child result is installed only when that child finalizes;
- a syntax selection is stored when its candidate is accepted;
- required child and generic checks complete before parent acceptance;
- a sequence span is committed only when its containing phrase finalizes;
- evaluator-provided families are published only from that finalized phrase;
- a node with blocked dependencies or an active choice point cannot finalize;
- raw source is never rematched after its node finalizes.

Consequently, reaching root finalization is sufficient evidence of success.
There is no end-of-rewrite reconstruction or validation walk.

Finalization does not:

- perform a strict whole-block pass;
- rebuild an ordinary expression from a collected child list;
- evaluate function-local runtime values;
- resolve identifiers through a new mechanism;
- reconstruct selections from source;
- modify the Datra AST.

## Determinism

Determinism is enforced by:

- source-order sequence positions and committed spans;
- LIFO child-before-parent execution;
- existing rule and template-branch ordering;
- existing longest-prefix and longest-capture ordering;
- deterministic argumentative-map alternatives;
- source-order dependency wakeups;
- ordered candidate-rejection accumulation.

Internal maps must not determine traversal or diagnostic order.

## Implementation plan

### Phase 1: extract current responsibilities

- Introduce the internal `SyntaxRewriting.*` modules.
- Move candidate matching, expansion helpers, and sequence helpers without
  changing behavior.
- Add focused tests for current rule, branch, capture, projection, and
  argumentative-map ordering.

### Phase 2: structural candidates and result types

- Split structural enumeration from candidate checks.
- Add `StructuralCandidate`, `SelectedCandidate`, `RewriteResult`, and
  `CandidateAttempt`.
- Expose each selected candidate's existing return type/federation.
- Check typed holes with the existing subfederation relation.
- Add `CandidateFrame` and its monotonic capture cursor around the existing
  generic preparation and inference path.
- Preserve completed capture checks and inferred generic inputs while nested
  child frames run.
- Add the `=`-establishes-`Bool` and `if`-expects-`Bool` regression.

### Phase 3: stack, dependencies, and backtracking

- Add `RewriteNode`, the four node states, and the explicit work stack.
- Add node-result dependencies and reverse wakeups.
- Represent active candidate cursors and parent continuations.
- Propagate exhausted child candidates to their active parent.
- Verify greedy fallback to later rules, branches, projections, and shorter
  captures.

### Phase 4: sequences and declarations

- Add sequence frames and `SequenceFamilies` dependencies.
- Allocate nodes lazily from sequence positions rather than eagerly per raw
  entry.
- Retain tentative candidate spans across blocking and commit them only from
  finalized phrase results.
- Allow block-hole candidates to capture following neutral entries through
  their terminating literal without making every syntax hole line-spanning.
- Publish interpreter-owned syntax families only from finalized nodes.
- Preserve the current provisional recursive `let` environment.
- Verify that finalized nested sequences are not rebuilt by outer progress.

### Phase 5: expansion and diagnostics

- Make expansion consume only accepted selections and finalized child results.
- Replace `NodeExpanded` with terminal `NodeFinalized` behavior.
- Retain ordered typing rejections throughout failed backtracking paths.
- Report candidate rejection details before falling back to unknown identifier.

### Phase 6: production switch and cleanup

- Switch standalone, resource, block, function-body, map, and syntax-insertion
  rewriting to the stack scheduler.
- Remove whole-sequence fixed-point passes.
- Remove strict raw replay and its retained-entry exception.
- Compare normalized AST results with the old implementation on the working
  corpus during migration.
- Run the complete test suite and remove the old implementation.

## Acceptance criteria

### Rewrite correctness

- Std loads successfully.
- The `public` function rewrites without evaluating `_declaration` during
  rewriting.
- The `=` child candidate establishes the `Bool` result required by `if`.
- `yield from 0 up` retains its selected positional captures.
- Argumentative-map alternatives retain every declared ordering.
- `%Int` syntax holes reject `Infinity`.
- Nat captures reject negative integers.
- `%IntLimit` accepts `Infinity`.
- A capture continues to satisfy both its syntax-hole schema and selected
  function domain.
- A dependent declaration backed by a generic function is checked using the
  return type instantiated from its captured child types.
- Sequential generic dependencies can use earlier captured types to
  instantiate later hole types and the final return type.
- Recursive `let`, module projection, contextual declarations, `Args`, and
  protection retain their current behavior.
- The multiline `Args` declaration is one outer rewrite phrase: its `do` block
  consumes the following entries through `yield`, and only the finalized
  declaration is published to the outer sequence.
- Generic binder identity, resolution, bounds, and protection remain owned by
  the existing generic implementation; candidate typing reuses that
  implementation rather than creating scheduler-specific generic semantics.

### Greedy matching

- A blocked earlier candidate prevents later candidates from being tried.
- A rejected candidate advances to the next candidate in semantic order.
- Exhausting a required child rejects the active parent candidate.
- Exhausting a parent propagates failure to the next active parent choice
  point.
- Parent fallback covers rules, branches, projections, argumentative-map
  alternatives, and shorter greedy captures.
- An accepted candidate is expanded once and immediately finalized.
- A finalized node is never rematched.

### Dependencies and sequences

- A parent waiting on a child resumes when that child finalizes.
- Finalizing a child wakes only registered dependants.
- Multiple generic candidates may be blocked simultaneously at different
  depths of the stack.
- Unwinding a finalized child continues its parent frame from the next
  unfinished capture without repeating enumeration or completed type checks.
- A generic candidate publishes its instantiated return type rather than its
  uninstantiated declaration codomain.
- Neutral newline and semicolon separators remain available to matching but do
  not force independent rewrite nodes.
- A blocked sequence-spanning candidate prevents overlapping entries from
  finalizing or publishing independently.
- Rejecting a spanning candidate releases its tentative span before the next
  greedy candidate is tried; finalizing the accepted phrase commits the span
  exactly once.
- New evaluator-provided families resume sequence-family dependants without
  replaying unrelated finalized nodes.
- Nested finalized sequences are reused when their parent resumes.
- Finalization performs no syntax selection from raw source.
- No whole-block strict replay remains.

### Diagnostics

- Every typing-rejected candidate in a failed search is reported in semantic
  attempt order.
- Each rejection reports the candidate, capture, expected type, actual return
  type, and reason.
- Generic rejections report the instantiated context and the bound, hole, or
  return-type check which failed.
- Nested rejection paths are retained across parent-level backtracking.
- Unknown identifier is reported only when the failed search contains no
  typing-rejected candidate.
- Existing specific non-matching rewrite failures retain their causal
  diagnostics.

### Architectural boundaries

- `DatraLanguage.AST` is unchanged.
- Parser generic resolution is unchanged.
- Interpreter function invocation is unchanged.
- Scope and dependent-declaration representations are unchanged.
- No activation plan or runtime rewrite scheduler is introduced.
- No name-based deferred-binding mechanism is introduced.
- Production contains one syntax-rewrite execution algorithm.

## Completion definition

The refactor is complete when:

- the explicit stack is the only production rewrite execution mode;
- every successful rewrite ends with all required nodes finalized;
- every finalized generic candidate has a fully instantiated return type;
- every failure either reports retained typing rejections or uses the
  unknown-identifier fallback when none exist;
- accepted selections are never discarded by raw replay;
- dependencies resume only affected rewrite work;
- greedy parent-level backtracking preserves current candidate order;
- all acceptance criteria and existing suites pass;
- the old fixed-point and strict-replay code has been removed.
