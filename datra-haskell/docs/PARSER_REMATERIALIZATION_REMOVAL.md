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
already succeeded; the parser should consume the insertion capability attached
to the structurally identified adapter rather than evaluate the declaration's
complete runtime signature. The static syntax catalog must therefore carry the
adapter insertion independently of its runtime domain and codomain. This is
part of steps 2 and 4 below, not a reason to add `from` as a parser special
case.

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

## Removal sequence

### 1. Enforce canonical construction

- Route optional generic arguments through `constructDependentArgument`.
- Audit producers of `DependentArgument` and require optionality on the
  identifier-expression left-hand side.
- Add structural tests which fail if an outer optional-value node is produced.

### 2. Make rewrite results direct

- Change syntax expansion to return the selected replacement AST directly.
- Pass structural captures to the adapter once.
- Remove `selectedDependentLookup` and the interpreter's tagged-lookup branch.
- Keep ordinary runtime lookup unchanged.

### 3. Separate generic signature inference from evaluation

- Accept a structural `FunctionBody` in the generic construction path.
- Resolve the inferred generic signature without evaluating the body.
- Attach the body once to the resolved signature.
- Delete both evaluate-to-detect-body recovery branches.

### 4. Build static syntax catalogs

- Compile `Std` rules from declaration AST after its own stack rewrite.
- Compile imported module rules from source metadata rather than evaluated
  module exports.
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
4. Optional generic arguments compile without evaluating an outer
   `OptionalType` expression.
5. Parser tests assert final rewritten ASTs and contain no tagged selected
   lookup representation.
6. Runtime `~` lookup still produces `{key; value}` rows and internal payload
   access remains positional.
7. Runtime dependent declarations retain their ordinary selection and
   materialization semantics outside parsing.
8. No change is made to the stack rewrite algorithm to compensate for removed
   evaluator paths.

## Non-solutions

The following do not satisfy this plan:

- caching `evaluateSelectedLookup` results;
- adding another resolution-stack cycle exception;
- recognizing more rendered-source strings in the interpreter;
- keeping both tagged lookup and direct rewrite results;
- evaluating `Std` eagerly and retaining its values for parser reuse; or
- changing candidate-stack rewrite behavior to accommodate evaluator-owned
  syntax selection.

Each would preserve two authorities for parsing. The intended cleanup leaves
the stack rewriter as the only authority.
