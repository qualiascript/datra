# Parser Rematerialization Removal

## Status and scope

This document defines the cleanup which follows the dependent-declaration and
identifier-expression work. The parser's stack rewriter is the authority for
syntax selection and expansion. Parsing must not evaluate a selected syntax
declaration again through lookup, generic application, declaration-family
materialization, or module evaluation.

The stack rewrite algorithm itself is not changed by this plan. The cleanup
removes downstream and parallel paths which repeat work already completed by
that algorithm.

Runtime evaluation remains in scope only where parser/bootstrap code currently
uses it. Ordinary program evaluation, including the public lookup operator and
its `{key; value}` rows, is not removed. Interpreter semantics unrelated to
loading `Std` are outside this cleanup.

## Required invariant

After a stack rewrite selects a syntax declaration, the rewrite result is the
sole semantic AST for that source occurrence.

In particular:

1. Candidate discovery uses declaration syntax and the stack rewrite indexes.
2. Matching produces structural, typed captures without evaluating a selected
   declaration member.
3. The selected syntax adapter produces the replacement AST once.
4. Parsing continues with that AST; it does not encode the selection as a
   runtime `Lookup` and recover the replacement by evaluating the lookup.
5. Generic resolution consumes the rewritten AST and never evaluates a body
   merely to discover whether it is a function body.
6. Building the imported syntax environment does not evaluate `Std` values.

This separates two operations which are currently conflated:

- parsing selects and rewrites syntax; and
- runtime evaluation materializes values of dependent declarations.

The first operation must not call the second.

## Current obsolete paths

### Selected-lookup transport

`selectedDependentLookup` preserves a matched template and its captures by
constructing a tagged `Lookup` expression. `lookupExpression` then projects
the selected row positionally. The interpreter recognizes that tagged lookup
in `evaluateSelectedLookup`, searches the declaration layers again, prepares
the captures again, evaluates the syntax adapter again, and evaluates the
expanded AST.

This is a second syntax engine after the stack rewriter. It must be removed.
The positional projection was an improvement over synthesizing a source-level
`value` identifier, but it does not make the transport itself necessary.

Removal targets:

- `selectedDependentLookup`;
- the two-template `ArgumentativeMap` encoding under `Lookup`;
- `evaluateSelectedLookup`;
- `selectedDependentDeclaration` and `selectedTemplateCaptures`;
- `PreparedSelectedCapture` and `PreparedSelectedCaptureBody`;
- `selectedDependentDeclarationMember` and its syntax/value materializers;
- selected-source key rendering used only by this transport; and
- special interpreter dispatch for the tagged lookup.

The ordinary runtime `Lookup` expression and the lookup row contract remain.

### Generic body probing and replay

The general `FunctionApplication` evaluator currently handles an unowned
generic introduction by evaluating the argument, checking whether the result
is a function body, constructing an inferred function expression which still
contains the original argument AST, and evaluating that synthesized
application. The body can therefore be evaluated once as a probe and again as
the inferred function's supplied body.

Parsing already knows whether the rewritten result is a `FunctionBody`.
Generic function construction must consume that structural fact directly.
It must not probe an arbitrary expression by evaluating it, and it must not
retain an expression which must be replayed to attach an already obtained
body.

Removal targets:

- the `GenericIntroductionOutsideFunctionType` recovery branch which evaluates
  an argument to detect `interpretedFunctionBody`;
- the equivalent non-callable branch inside `applyEvaluated`;
- `inferredFunction` behavior which embeds the probed argument for a second
  evaluation; and
- any function-body attachment path whose input is an evaluated body but
  whose implementation reconstructs and evaluates its source expression.

The replacement should separate signature inference from body attachment:
infer a resolved signature from the generic introduction, then attach the one
structurally rewritten function body.

### Parser use of declaration materialization

Ordinary identifier access reaches
`dependentDeclarationMemberByName`, which prepares a declaration family,
selects a member, and evaluates its implementation. Dynamic named-map views
provide additional materialization entry points through member-by-name,
ordinal, collection, and declared-member projections.

These are valid runtime capabilities, but parser/bootstrap code must not use
them to discover syntax. In particular, syntax discovery must not pass through:

- `resolveIdentifierAccess`;
- `dependentDeclarationMemberByName`;
- `materializeDependentDeclaration` or
  `materializeDependentDeclarationActive`;
- `dynamicDependentDeclarationNamedView` projections; or
- declaration-family descriptor invocation.

Parser-facing syntax catalogs should contain compiled rewrite rules and their
structural adapters, not evaluated `NamedMember` values.

### Membership, eager lets, and consistency validation

Several paths do not intentionally request a concrete syntax member but can
still evaluate capture schemas or declarations while assembling a parser
environment:

- `scopeNameExists` delegates to `dependentDeclarationContainsName`;
- eager `let` retention resolves every singleton let through
  `importScopeUsing`;
- shadowing consistency resolves both the original and replacement values;
- named-map manifest and collection projection prepares whole declaration
  views; and
- module export discovery evaluates declaration descriptors before deriving
  syntax rules.

These operations remain meaningful for runtime scopes. They must be removed
from the parsing-environment construction path. Static syntax overlap and
visibility are decided from the rewritten declaration AST and the stack
rewriter's indexes.

### Resolution-stack fallback is not memoization

`evaluateDeferredDeclarationWith` recognizes a repeated resolution key only
when `recursiveFunctionImplementation` can provide a seed. Otherwise it
evaluates again with the repeated key pushed onto the stack. It is a recursive
function seed mechanism, not a cache and not a general cycle detector.

Parser correctness must not depend on extending this mechanism. Adding
selected-member memoization or a new resolution-stack special case would keep
the duplicate syntax engine and hide the ownership error.

## Trigger exposed by optional generics

The immediate hang exposed one stale representation:
`genericArgumentExpression` lowered `&T?` as an outer `OptionalType` around a
dependent argument. The canonical representation places optionality inside
the identifier expression on the left-hand side.

The stale form missed `optionalIdentifierExpression`, causing generic
parameter compilation to evaluate it as an ordinary expression. Ordinary
`OptionalType T` means `Maybe T`, so constructing `Maybe`'s own inferred
signature resolved `Maybe` again and re-entered its selected syntax body.

The immediate fix makes generic lowering use `constructDependentArgument`.
That removes this trigger, but the rematerialization paths above remain
architecturally obsolete and must still be deleted.

## Next exposed boundary: typed adapter evaluation

With the optional-generic representation fixed, `Std` rewriting advances to
`Nat := from 0 up`. The stack rewriter has both `from` rule branches in scope
and structurally matches the expression. The source nevertheless survives the
rewrite unchanged because rule preparation tries to obtain the syntax
insertion by evaluating the entire typed adapter:

```datra
({origin : Int; ...} -> IntValRange) datra.from_body
```

That signature depends on `Int`, while `Int` depends on `Nat`, whose source is
the `from` expression currently being rewritten. Adapter evaluation therefore
cannot complete. `directSyntaxFunctionExpansion` falls back to the unchanged
syntax application, and module evaluation later reports
`UnknownIdentifier "from"`.

This is another instance of parser rematerialization. Candidate selection has
already succeeded; the parser should consume the lowering capability attached
to the structurally identified adapter rather than evaluate the declaration's
complete runtime signature. This capability is not always a
`SyntaxFunctionInsertion`: `datra.from_body` is an ordinary runtime insertion
and should lower to a direct AST application. The static syntax catalog must
therefore carry the structural adapter, normalized domain and codomain, and
rule mode independently of the adapter's runtime signature. This is part of
steps 2 and 4 below, not a reason to add `from` as a parser special case.

## Target parsing pipeline

The target pipeline is:

```text
raw source
  -> concrete parse
  -> declaration syntax catalog
  -> stack rewrite candidate selection
  -> structural capture substitution
  -> final rewritten semantic AST
  -> generic binder resolution
```

Evaluation begins only after this pipeline completes.

For `Std`, the syntax catalog is compiled from its rewritten module source.
For imports, parser-visible syntax catalogs are compiled or loaded from module
source metadata. Neither operation evaluates the module's runtime federation
or exports merely to recover syntax declarations.

The catalog must retain everything the stack rewriter needs:

- declaration visibility and source order;
- literal and identifier-expression components used for eager rejection;
- capture schemas as syntax expressions;
- declaration modifiers relevant to parsing;
- the structural syntax adapter; and
- module provenance needed by diagnostics.

It must not retain an evaluated declaration member as the authority for a
rewrite.

## Unified syntax-rule model

### One semantic rule regardless of origin

The current rule representation distinguishes three cases:

- `SyntaxApplication` for a simple identifier declaration;
- `DependentSyntax` for an identifier-template declaration; and
- `SyntaxAdapter` for reconstructed host or imported syntax.

These constructors describe where a rule came from, not what it means. They
then force matching, capture packaging, adapter discovery, and fallback
expansion to branch on provenance. A rule can consequently try a syntax
insertion, construct a selected lookup, or apply a callable depending on which
constructor happened to create it.

The semantic invariant is instead:

> Every syntax rule matches one identifier-expression pattern, lowers its
> rewritten captures exactly once, and determines the type of that lowering
> exactly once.

Plain identifiers, string templates, backtick expressions, source-module
rules, and imported rules must all compile into that same semantic object.
Their origin remains only as diagnostic metadata.

### One identifier-expression pattern representation

Every declaration head already has the invariant that it is an identifier
expression. Rule construction must pass all such heads through the same
identifier-expression branch compiler. In particular, a simple declaration
such as:

```datra
abc := 123
```

compiles through the same literal/capture segment representation as a
backtick expression. Its pattern is simply the one-literal pattern `abc`.
Literal-prefix indexing may recognize this as the fast path after the pattern
has been compiled; rule construction must not select a different matcher in
advance.

This removes the semantic need for `IdentifierApplicationMatcher` and
`IdentifierApplicationPattern`. Capture order comes solely from the compiled
identifier pattern. Spacing, line-break, and empty-identifier rules remain
owned by the identifier-expression/string-expression federation machinery,
so the optimization cannot create a second spelling model.

An ordinary literal identifier whose evaluation needs no AST transformation
does not require an active rewrite entry. It remains in the declaration index
and resolves normally at runtime. This is an optimization of an already
compiled literal pattern, not a separate kind of syntax declaration. A
literal-headed declaration whose adapter is a syntax insertion, such as
`let`, remains an active rule and uses the same lowering contract as every
other rule.

### Static rule and compiled rule

There are two useful phases, but only one syntax semantics:

1. A static rule retains AST metadata which can cross module boundaries: the
   compiled identifier pattern, structural adapter expression, normalized
   domain and codomain, rule mode, branch identity, visibility, and
   provenance.
2. A scoped rewrite rule resolves that metadata against the current syntax
   environment and exposes total lowering and result-typing operations to the
   stack rewriter.

A conceptual static representation is:

```haskell
data SyntaxRule = SyntaxRule
  { syntaxRulePattern :: IdentifierPattern
  , syntaxRuleAdapter :: Expression
  , syntaxRuleDomain :: Expression
  , syntaxRuleCodomain :: Expression
  , syntaxRuleMode :: SyntaxRuleMode
  , syntaxRuleMetadata :: SyntaxRuleMetadata
  }

data SyntaxRuleMode
  = ExpressionMode
  | FunctionMode
```

This sketch specifies responsibilities rather than final names. The important
points are that the adapter is already structurally separated from a typed
function application and that every rule has a domain and codomain. The
complete declaration implementation remains in the runtime declaration
system; the parser rule does not retain it as an alternate authority.

The rule mode is a real semantic distinction, unlike the current
origin-based rule constructors. Treating a regular value as an implicit
constant function for typing must not make that value callable. For example:

```datra
x := 3
f := (() -> Nat) do yield 3
```

The value `x` has the implicit rule contract `() -> 3`, but selecting it uses
`ExpressionMode` and returns `3` without constructing an application. Its
codomain is literally the given value `3`, not a widened type such as `Nat` or
`Int`. The value `f` is itself a function value. Selecting `f` returns that
function; obtaining its result still requires the ordinary explicit
application `f ()`.

More generally, a non-function right-hand side is viewed as a constant
function from the declaration's compiled capture domain to the right-hand
side value. With no captures the domain is `()`. This view supplies total
typing metadata only; `ExpressionMode` preserves the omission of the synthetic
argument. An actual adapter which consumes declaration captures uses
`FunctionMode`, and an empty capture list then supplies the real `()` argument.

The scoped compiled rule exposes the two semantic operations directly:

```haskell
lowerSyntaxRule
  :: [Expression]
  -> Maybe SyntaxFunctionExpansion

typeSyntaxRuleResult
  :: [RewriteResult]
  -> Either CandidateRejection InterpretedValue
```

`Maybe` in the lowering operation means that a concrete capture shape is not
accepted by that lowering. It does not mean that the compiled rule lacks a
lowering strategy. Likewise, failure from the result operation rejects a
candidate; it does not leave an accepted rule with an unknown result type.

### Exactly one lowering operation

Catalog construction chooses one lowering operation:

- `ExpressionMode` returns the structural adapter expression directly. Its
  implicit domain exists for typing but is not supplied operationally.
- `FunctionMode` supplies the canonical capture argument to the structural
  adapter. If that adapter resolves to an `EvaluatedSyntaxFunctionBody`, this
  invokes its `SyntaxFunctionInsertion`; otherwise it constructs a
  `SyntaxExpression` containing the ordinary application.

The rule mode is chosen from the rule's actual semantics, not merely
from whether the adapter expression happens to have a function type. A simple
identifier whose value is a function still returns the function value. A
template rule whose implementation consumes its captures applies that
implementation.

Capture packaging is shared. Empty, singleton, and multiple captures use one
canonical helper; matcher provenance does not decide whether captures are
flattened. The compiled identifier pattern already defines their order and
boundaries.

The adapter capability is resolved once when the scoped catalog entry is
compiled. `prepareSelectedSyntaxMatch` must not try an insertion and then pass
the same application to `directSyntaxFunctionExpansion` for another attempt.
The compiled lowering is invoked once and its result is the replacement AST.

This preserves the genuine distinction in `SyntaxFunctionExpansion` between
an expression, a `Begin`, and a `FunctionBody`. Those are different output AST
shapes, not different kinds of syntax rules.

### Result typing is mandatory

A source declaration may omit an explicitly written function signature, but a
compiled rule may not omit its domain, codomain, or result-typing operation.
There is no separate `ResultFromExpansion` case.

When the lowering is an actual function application, its structurally
declared domain and codomain become the rule contract. When the lowering
returns a regular value, catalog construction supplies the implicit constant
contract:

```text
capture-domain -> right-hand-side-value
```

For `x := 3`, this is `() -> 3`. For a constant template with an `Int`
capture, it is `Int -> 3`. The codomain is the exact value federation, not an
optional annotation and not an inferred broad type such as `Nat`.

The result-typing operation always instantiates the normalized codomain in the
prepared capture environment. A structural lowering may additionally expose a
more precise result expression, as a syntax insertion does, but that is a
refinement of the same codomain contract rather than a different typing mode.
If the codomain cannot be instantiated or the refined result violates it, the
concrete candidate is rejected.

The result typer runs after the candidate's captures have been structurally
prepared. The candidate frame already owns those capture results; making them
available to the result operation is state plumbing and does not change the
stack scheduler, search order, or rewrite algorithm.

The current fallback chain must be removed:

1. cached `rewriteRuleReturnType`;
2. applying the runtime implementation to `candidateTypingInputs`; and
3. evaluating the declaration again to inspect its function codomain.

That chain makes failure to resolve static metadata silently invoke runtime
semantics. A total normalized contract makes the ownership boundary explicit.

### Concrete bootstrap examples

The natural-literal rule resolves `datra.parse_natural` to a syntax insertion.
Its normalized contract retains the structural `_NaturalLiteral -> Nat`
signature and uses `FunctionMode`. For the source literal `0`, the lowering
also exposes the precise result `EllipsisNatural 0`. Candidate typing can use
that exact result while retaining `Nat` as the declaration's result contract;
it does not evaluate the complete typed adapter while `Nat` is being
bootstrapped.

The `from` rule is structurally split as follows:

```text
pattern:       from %Int (to %IntLimit | %_Direction)
adapter:       datra.from_body
domain:        {origin : Int; target? : IntLimit | direction? : _Direction}
codomain:      IntValRange
mode:          FunctionMode
```

After its captures have been rewritten, `from 0 up` lowers once to the
semantic equivalent of:

```datra
datra.from_body (0; up)
```

`datra.from_body` is not required to masquerade as a syntax insertion. The
parser does not evaluate the domain containing `Int`, and it does not encode
the match as a lookup for the interpreter to rediscover.

### Source-owned imported catalogs

Imported syntax must preserve the same static rule representation. The
current `moduleSyntaxRulesFromValueIn` path evaluates module members, extracts
`FunctionSyntax String`, reparses those strings, and reconstructs rules with a
different `SyntaxAdapter` representation. This loses the original structural
adapter and makes runtime module values the authority for parsing.

Module source metadata must instead carry the static rules compiled from the
module's declaration AST. Namespace qualification transforms the rule's
provenance and any external references; it does not reconstruct its semantics
from an evaluated function. `FunctionSyntax` may remain runtime presentation
metadata, but parser catalog construction must not consume it.

### Representation cleanup enabled by the invariant

Once rules have one pattern, lowering operation, and result operation, the
following state becomes obsolete:

- `SyntaxRuleSemantics`, `SyntaxApplication`, `SyntaxAdapter`,
  `DependentSyntaxRule`, and `DependentSyntaxInvocation`;
- `dependentSyntaxCaptures`, which is currently stored but not consumed;
- `syntaxApplicationImplementation` and provenance-based capture flattening;
- `directSyntaxFunctionExpansion` and its second insertion attempt;
- `rewriteRuleEvaluation` and simultaneous storage of an adapter plus an
  optionally resolved insertion;
- `syntaxRuleFamilyApply`, which is populated but not read;
- `contextEvaluateWithInput`, which is populated but not read;
- the result-type field in `CandidateTypingContext`, which is consulted before
  it can provide a completed candidate result;
- duplicate branch identity on both a rewrite rule and its structural
  candidate; and
- the tagged selected-lookup transport and its interpreter-side capture
  preparation records.

`DeclarativeCapture` should also be collapsed unless a second genuinely
different capture representation appears; it currently wraps only
`StringExpression Expression`.

## Removal sequence

### 1. Enforce canonical construction

- Route optional generic arguments through `constructDependentArgument`.
- Audit producers of `DependentArgument` and require optionality on the
  identifier-expression left-hand side.
- Add structural tests which fail if an outer optional-value node is produced.

### 2. Make rewrite results direct

- Replace the origin-based syntax-rule constructors with one identifier
  pattern and one static lowering plan.
- Compile one lowering operation and one mandatory result-typing operation for
  every scoped rule.
- Change syntax expansion to return the selected replacement AST directly.
- Pass structurally rewritten captures to the lowering exactly once.
- Extract typed adapters into structural body and codomain metadata without
  evaluating the full signature.
- Remove `IdentifierApplicationMatcher` after the shared literal-pattern path
  covers simple identifiers.
- Remove the insertion retry in `directSyntaxFunctionExpansion`.
- Remove `selectedDependentLookup` and the interpreter's tagged-lookup branch.
- Keep ordinary runtime lookup unchanged.

### 3. Separate generic signature inference from evaluation

- Accept a structural `FunctionBody` in the generic construction path.
- Resolve the inferred generic signature without evaluating the body.
- Attach the body once to the resolved signature.
- Delete both evaluate-to-detect-body recovery branches.

### 4. Build static syntax catalogs

- Compile `Std` rules from declaration AST after its own stack rewrite.
- Store the unified static rule representation as module source metadata.
- Compile imported module rules from source metadata rather than evaluated
  module exports.
- Stop reconstructing parser rules from `FunctionSyntax String`.
- Remove parser calls through module value materialization, named-map
  manifests, eager runtime lets, and runtime shadowing consistency.

### 5. Narrow runtime declaration APIs

- Keep membership, selection, and materialization as distinct runtime
  operations.
- Ensure a membership query cannot invoke an implementation.
- Ensure named-map view construction is inert; only an explicit runtime member
  request may materialize a member.
- Remove parser-specific branches and comments from these runtime APIs.

### 6. Delete compatibility code

- Remove the tagged lookup representation and all selected-capture records.
- Remove rendered-source keys used only to coordinate parser rematerialization.
- Remove parser/bootstrap exceptions in deferred declaration evaluation.
- Remove tests which assert the intermediate lookup encoding and replace them
  with final-AST assertions.

## Verification

The cleanup is complete when:

1. Raw and ordinary parsing of `Std` complete without evaluating a `Std`
   declaration implementation.
2. The full parsing suite passes, including `numbers.datra` and natural-map
   properties.
3. A selected syntax adapter is invoked exactly once per accepted rewrite.
4. Every compiled rule has exactly one lowering operation and one result-type
   operation; neither operation is optional or absent.
5. Optional generic arguments compile without evaluating an outer
   `OptionalType` expression.
6. Parser tests assert final rewritten ASTs and contain no tagged selected
   lookup representation.
7. Runtime `~` lookup still produces `{key; value}` rows and internal payload
   access remains positional.
8. Runtime dependent declarations retain their ordinary selection and
   materialization semantics outside parsing.
9. No change is made to the stack rewrite algorithm to compensate for removed
   evaluator paths.

## Non-solutions

The following do not satisfy this plan:

- caching `evaluateSelectedLookup` results;
- adding another resolution-stack cycle exception;
- recognizing more rendered-source strings in the interpreter;
- keeping both tagged lookup and direct rewrite results;
- representing a compiled rule with optional lowering or optional result
  semantics;
- retaining separate matcher or lowering semantics for simple identifier
  declarations;
- evaluating `Std` eagerly and retaining its values for parser reuse; or
- changing candidate-stack rewrite behavior to accommodate evaluator-owned
  syntax selection.

Each would preserve two authorities for parsing. The intended cleanup leaves
the stack rewriter as the only authority.
