# Syntax Rewrite Algorithm

## Purpose

Syntax rewriting transforms one neutral `Expression` into its declarative
meaning. The transformation is an explicit stack machine. It performs
structural selection, child rewriting, incremental type checks, expansion,
declaration publication, and finalization in one pass.

The input expression is already parsed. Source layout is not an input to this
algorithm, and the rewriter does not contain another parser.

## Ownership

The rewrite stack owns all syntax-rewrite control flow:

- rewrite-node allocation and scheduling;
- structural candidate ordering and backtracking;
- candidate capture progress and typing state;
- incremental child installation;
- syntax expansion and ordinary traversal;
- source-ordered declaration publication;
- rejection ordering and root finalization.

The evaluator owns semantic context construction:

- lexical and continuation scope entry;
- opened-scope imports;
- recursive declarations;
- contextual values;
- scope-protection activation and handoff;
- semantic hole capture and normalization;
- declaration publication and syntax-family construction;
- expression and result-type evaluation.

The stack asks the evaluator for the exact context at a rewrite locus. It does
not interpret expression constructors to decide whether a context is shared,
fresh, contextual, opened, recursive, or protected.

## Machine shape

The machine is an append-only map of node IDs to nodes:

```haskell
newtype RewriteMachine environment = RewriteMachine
  { machineNodes :: Map RewriteNodeId (RewriteNode environment) }
```

There is no empty-machine execution state. The private machine constructor
creates the root node before scheduling begins. Fresh IDs are derived from the
append-only node map; no counter duplicates the allocation state.

```haskell
data RewriteNode environment = RewriteNode
  { rewriteNodeExpression :: Expression
  , rewriteNodeEnvironment :: environment
  , rewriteNodeParent :: Maybe RewriteNodeId
  , rewriteNodeRejections :: [CandidateRejection]
  , rewriteNodeState :: RewriteNodeState
  }
```

The map key is the node identity, so identity is not duplicated inside the
node. `rewriteNodeExpression` is the current expression. Every finalized child
is installed into it immediately.

The worklist is non-empty:

```haskell
NonEmpty RewriteNodeId
```

Root finalization is the only terminal transition. Worklist exhaustion is not
representable.

## Node state

```haskell
data RewriteNodeState
  = NodePending
  | NodeReady RewriteWork
  | NodeWaiting RewriteWork RewriteNodeId
  | NodeFinalized RewriteResult

data RewriteWork
  = SearchCandidates CandidateSearch
  | TraverseChildren OrdinaryTraversal
```

`NodePending` has never enumerated candidates. `NodeReady` contains the whole
continuation required by its next transition. `NodeWaiting` names exactly one
active child and retains the unchanged continuation that will consume it.
`NodeFinalized` contains the immutable result.

There are no action values on the worklist. Popping a node ID and inspecting
its stored state is the only dispatcher.

## Evaluator-provided contexts

The stack describes the current locus without assigning it semantics:

```haskell
data RewriteLocus
  = RewriteExpression Expression
  | RewriteChild Expression Int Expression

contextRewriteScope :: RewriteLocus -> SyntaxContext
```

`RewriteExpression` is used for the root, a candidate capture, and a freshly
expanded expression. `RewriteChild parent index child` identifies an ordinary
AST edge. The evaluator returns the complete context for that locus.

Every node stores that returned context directly. The stack does not store a
parallel scope table or a scope-transition tag. When a finalized declaration
changes visible syntax, the evaluator's publication callback returns the next
context and the stack installs it directly on the parent node before advancing
to the next child.

`MaybeThen`, `ScopeAccess`, `Begin`, and `FunctionBody` semantics therefore
remain evaluator concerns. A begin/yield block can enter a protected local
activation without teaching the stack about protection. An opened scope can
import syntax without teaching the stack about imports.

## Structural candidates

Candidate enumeration has one structural projection boundary:

```haskell
structuralTemplateCaptures
  :: SyntaxTemplate Expression
  -> Expression
  -> [[(Expression, Expression)]]
```

Each pair is the declared target expression and the neutral source expression
selected for that hole. Hole behavior is not encoded in the template.

Rules are enumerated in declaration order. Projections for a rule are
enumerated in the order returned by `SyntaxTemplateProjection`. Each structural
match records the rule, branch, projection, captures, whole selection, and
unconsumed application remainder.

The rewriter does not search rendered source strings, cache literal facts,
split expressions at literals, or recognize individual templates. Literal
matching and neutral-AST reassociation live in `SyntaxTemplateProjection`.
Projection contains only neutral structural views which cannot be declared in
`std.datra`. It does not reify `let`, `def`, `val`, `do`, or any other
standard-library operation as a built-in candidate. Those operations are
selected exclusively through their declared syntax rules.

Semantic capture is a later evaluator operation. For example, a `_Block`
capture normalizes its generic application-shaped provisional capture into an
`AtlasMap`. This does not change structural candidate enumeration.

## Candidate search

```haskell
data CandidateSearch = CandidateSearch
  { candidateSearchCandidates :: [StructuralCandidate]
  , candidateSearchCursor :: Int
  , candidateSearchRejections :: [CandidateRejection]
  , candidateSearchFrame :: Maybe CandidateFrame
  }
```

Only the candidate at the cursor is active. Later candidates cannot run while
it is blocked.

```haskell
data CandidateFrame = CandidateFrame
  { candidateFrameNextCapture :: Int
  , candidateFrameTypingContext :: CandidateTypingContext
  , candidateFrameResults :: Map Int RewriteResult
  , candidateFramePreparedCaptures :: Map Int Expression
  }
```

Advancing a frame performs as much synchronous work as possible. If another
child is needed, the blocked result carries the advanced frame:

```haskell
CandidateFrameNeedsChild CandidateFrame Int Expression Expression
```

The final fields are the hole's declared target and structurally selected
source. The evaluator derives capture behavior from the evaluated target.

This is a progress invariant. A child request can never discard cursor,
typing, or prepared-capture progress.

Candidate execution is:

1. Create or resume the active frame.
2. Request the next unfinished capture child.
3. Store `NodeWaiting work child` before scheduling the child.
4. Consume the finalized child exactly once.
5. Normalize the semantic capture and check its expected type immediately.
6. Update generic typing inputs and advance the capture cursor.
7. Accept only after all captures and the return type are known.
8. On rejection, append one ordered rejection and advance to the next
   candidate.

An accepted candidate expands exactly once. The expanded expression replaces
the node's current expression before ordinary traversal begins. Expansion is
not another matching phase for that node.

## Ordinary traversal

If candidate search is empty or exhausted, the node traverses
`expressionChildren rewriteNodeExpression` in source order.

For each child:

1. Ask the evaluator for the child's exact context.
2. Allocate one child node.
3. Mark the parent waiting for that node.
4. Run the child to finalization.
5. Install the finalized expression through `traverseExpressionChildren` at
   the stored cursor.
6. Publish the finalized child when it is a declaration position.
7. Install any returned evaluator context on the parent.
8. Advance the cursor once.

When no child remains, finalization returns the expression already stored on
the node. There is no reconstruction pass.

The traversal is uniform over the AST. The stack has no independent knowledge
of `GreedyStringTemplate` or any other expression constructor.

## Neutral sequences

`AtlasMap`, `Begin`, and `FunctionBody` are complete expressions. They are not
split into independent rewrite roots and are not rebuilt by a separate
sequence machine.

Their children are traversed in source order by ordinary traversal. The
evaluator supplies recursive visibility at expression entry and publishes each
finalized declaration as it becomes available. A later child therefore sees
the context returned after earlier declarations, while nested local scopes
retain their own evaluator-defined protection and contextual behavior.

An expansion that produces `Begin` or `FunctionBody` creates that expression
once. Its unfinished children then follow the same ordinary traversal.

`do` has no rewrite-stack behavior. It is an ordinary declared rule:

```datra
%($do; _Block; $yield; _Expr) :=
  (_Block; _Expr -> _FunctionBody) datra.do_body
```

## Declaration modifiers

`let`, `def`, and `val` are standard-library syntax, not expression
constructors and not projection cases. Their syntax functions operate on a
`DeclarationExpression` and append one `DeclarationModifier` to the
declaration's application history.

The history is stored in expansion order, from the innermost modifier to the
outermost modifier. This is the right-to-left order in which a written form is
applied. For example, `let def val x := value` records:

```haskell
[DeclarationVal, DeclarationDef, DeclarationLet]
```

The three semantic modifier flags are updated from that history. Declaration
validity is not stored independently; `dependentDeclarationIsValid` derives it
by comparing the exact history with the duplicate-free canonical subsequence
of `[val, def, let]`.

Modifier syntax always returns a declaration value, including invalid order or
repetition. When a declaration enters a block, block assembly checks the
derived validity predicate. An invalid declaration produces the single
localized `InvalidDependentDeclarationModifiers` compiler error, carrying the
written modifier order and its equivalent canonical `let def val` order.

## Finalization and diagnostics

A node finalizes only when it has no unfinished candidate work, no unfinished
ordinary child, and no active child wait.

A finalized child schedules its parent. A finalized root returns its stored
result and ordered rejections. A finalized node is never reset to pending and
never rematched.

Rejections are recorded at the transition where their evidence becomes
available. A rejection contains the rule and branch, capture position, source,
expected and actual types, instantiated typing context, reason, and nested
child rejections.

## Current blocking failure

The executable builds, but constructing the standard-library syntax
environment fails at `libs/std.datra:73`. The failing source is:

```datra
val Args := &T? do
  slots := (^_i :: Nat) do yield "arg%(_i)"? : T
yield ((^n? :: Nat) do yield slots[0..n])
```

The exact diagnostic is:

```text
module imports could not be scanned
  module: output.datra
  syntax environment could not be constructed
  ModuleEvaluationFailed (StandardLibraryParseFailure "std.datra" "operation has no effect inside block\n  expression: yield ((^n? :: Nat) do yield (slots[0 .. n]))")
```

The reproduction command is:

```sh
cabal run datra-haskell -- build --input output.datra \
  --ast-output /tmp/datra-design.ast --output /tmp/datra-design.out
```

At the block-assembly boundary, the outer `yield` application is still present
as an ordinary expression. Therefore the declared `do`/`yield` form did not
consume the complete neutral source region before ordinary block validation.
The identifier-literal and target-directed capture design is implemented before
diagnosing a narrower structural cause, because `$do` and `$yield` must first
have unambiguous non-string AST meaning. No `do`-, `yield`-, arity-, or
source-string-specific projection is an acceptable fix.

## Required invariants

1. The scheduled worklist is always non-empty.
2. The initialized machine always contains its scheduled root.
3. Every scheduled ID names an allocated node.
4. Node IDs are allocated once and the node map is append-only.
5. A node's stored state is its complete continuation.
6. A waiting node names exactly one active child.
7. A child result is consumed exactly once.
8. A blocked candidate retains its advanced frame.
9. Candidate order and rejection order are stable.
10. Candidate typing advances only when a finalized capture is consumed.
11. An accepted candidate expands exactly once.
12. Every finalized ordinary child is installed immediately.
13. Declaration publication occurs before the next sibling is scheduled.
14. The evaluator is the sole authority for rewrite contexts and local scope
    semantics.
15. The stack is the sole authority for syntax-rewrite scheduling and state.
16. A finalized node is never rematched.
17. Root finalization is the only terminal transition.
