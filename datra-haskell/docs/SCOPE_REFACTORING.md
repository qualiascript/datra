# Scope Refactoring

## Status and scope

This document defines the unified lexical-scope, module, and syntax-rewriting
model. `Scope` is the single owner of visible dependent declarations. Value
lookup, dependent declaration selection, qualified access, unqualified module
imports, `with`, and declarative syntax all consult the same ordered declaration
layers.

The design removes parallel representations of visibility. In particular:

- syntax rules are derived from scoped dependent declarations;
- modules are prepared as dependent declaration layers;
- qualified module namespaces are ordinary dependent declarations;
- unqualified imports push ordered declaration layers;
- `with` pushes the same layers as strict imports and diagnoses ambiguity only
  when more than one strict layer accepts a concrete use; and
- candidate suspension records exact blocker expressions and is resumed only
  when publication into `Scope` can resolve one of them.

This refactor does not normalize, render and reparse, or otherwise rematerialize
expressions. It does not introduce a replacement for `SyntaxContext` under a
different name.

## Core invariants

The implementation must preserve these invariants:

1. `Scope` is the only semantic source of declaration visibility.
2. A scope is an ordered stack of `DependentDeclarationLayer`s. The first
   applicable layer has precedence over outer layers.
3. Declarations within one layer belong to the same declaration family
   environment. All applicable declarations in that layer participate in the
   ordinary ambiguity, overload, specification, and subfederation decisions.
   `with` does not merge declarations from different origins into one layer.
4. A declaration retains the lexical scope used to evaluate its implementation
   and the family scope used to evaluate its dependent name.
5. Module preparation evaluates a module once. Installing or opening that
   module reuses its prepared declarations and captured scopes.
6. Qualified access and local namespace access use the same declaration and
   scope operations.
7. Syntax candidates are enumerated in declaration-layer order. A candidate in
   an inner layer is decided or refuted before an applicable candidate in an
   outer layer is selected. A local or preferential match wins immediately,
   including over matching strict layers below it. Only when the highest
   matching layer is strict does acceptance remain provisional while lower
   strict layers are checked.
8. An undecidable candidate with blockers is suspended. It is not retried,
   structurally rematched, or externally normalized.
9. A suspended candidate is reconsidered only after publication makes one of
   its exact blocker expressions resolvable.
10. An undecidable candidate with no unresolved blockers is refuted.
11. No `.hs-boot` modules or compatibility facades are introduced.

## Scope representation

The central representation remains an ordered list:

```haskell
data Scope = Scope
  { scopeDependentDeclarationLayers :: [DependentDeclarationLayer]
  , scopePresentationOwner :: Maybe PresentationOwner
  , scopeActivation :: ScopeActivation
  , scopeHandoff :: Maybe ScopeHandoff
  }
```

Module source catalogs and copied syntax catalogs do not belong in `Scope`.
External loading prepares declarations before installation; runtime lookup
uses those installed declarations.

Each layer represents one visibility boundary. Prepending a layer makes it
more local than every existing layer:

```text
new layer
previous local layer
outer lexical layer
...
```

Resolution examines layers from top to bottom. Within a layer it collects and
decides all structurally matching declaration candidates. It proceeds to the
next layer only when the current layer has no accepted or suspended candidate.

This distinction is essential. Multiple declarations in one layer are a
family; multiple layers express precedence.

Layer import policy is semantic metadata used where composition changes
selection:

```haskell
data DeclarationLayerImportPolicy
  = LocalDeclarationLayer
  | PreferentialImport
  | StrictImport
```

The layer's position and policy contain all information required for selection.
A preferential import participates in ordinary stack precedence. A strict
import retains its stack position but cannot be accepted until the lower strict
layers have been shown not to accept the same use. No group identifier or
declaration-origin value is retained.

Resolution is governed by the highest layer that actually matches:

1. A matching `LocalDeclarationLayer` is accepted immediately. Lower local,
   preferential, and strict matches are irrelevant.
2. A matching `PreferentialImport` is accepted immediately for the same reason.
3. A matching `StrictImport` is provisional. Lower strict layers are checked
   for another match; lower local and preferential layers cannot override it.
4. If a layer does not match, resolution continues downward without changing
   the selection mode.

Thus policy never overrides stack precedence. Strictness changes how a match
is validated; it does not allow a lower strict import to compete with a higher
local or preferential match.

The existing source-versus-runtime layer origin remains separate from import
policy. A layer can therefore retain both how its declarations were produced
and how they participate in import selection.

## Scope operations

`Evaluation.Scope` owns the structural operations for composing scopes:

```haskell
pushDependentDeclarationLayer
  :: DependentDeclarationLayer -> Scope -> Scope

pushDependentDeclarationLayers
  :: [DependentDeclarationLayer] -> Scope -> Scope

enterDeclarationScope
  :: salt
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> Scope
  -> Scope

pushImportedDeclarationLayer
  :: DeclarationLayerImportPolicy
  -> DependentDeclarationLayer
  -> Scope
  -> Scope
```

The exact names may follow the surrounding module vocabulary, but the
operations remain distinct:

- pushing preserves layer boundaries and establishes precedence;
- entering establishes activation and handoff boundaries;
- importing preserves each declaration source as a separate layer and attaches
  its preferential or strict selection policy.

These operations retain existing `ScopedDependentDeclaration` values. They do
not flatten declarations into named runtime values or reconstruct declarations
from rendered output.

## Declaration publication

Rewriting a lexical resource publishes declarations into its active source
layer in source order.

- Ordinary declarations become visible after their finalized declaration node
  is published.
- Recursive `let` declarations are predeclared once for their lexical block.
- Publishing a finalized `let` replaces its predeclared family in the current
  scope version.
- Later rewrite nodes receive the updated `Scope`.
- Previously finalized nodes are never re-evaluated.

Publication preserves the declaration head, implementation, captured scope,
and family scope. It must not rewrite recursive declarations into alternate
validation seeds.

Declarations whose name families overlap inside one lexical source layer are
validated through the ordinary declaration-family decision. Source-level
duplicate declarations continue to produce `OverlappingBindings`.

## Module representation

A module source evaluates to an ordered dependent declaration layer. A module
file may export one or more namespace declarations, and those declarations are
independent of the filename.

Conceptually, a prepared module is:

```haskell
data PreparedModule = PreparedModule
  { preparedModuleIdentity :: FilePath
  , preparedModuleNamespaces :: DependentDeclarationLayer
  }
```

The identity is retained for diagnostics, dependency presentation, and input
deduplication. The layer is the runtime and syntax representation of the
module.

A namespace such as `Numbers` is represented by a normal scoped dependent
declaration. Its declaration retains:

- the original dependent name expression;
- the evaluated public namespace value;
- the private lexical scope captured by exported implementations;
- the public declaration layer exposed when the namespace is opened;
- canonical presentation and dependency origin metadata; and
- the module identity used by diagnostics and closure presentation.

The public layer contains only declarations selected by the module's public
result. Each public declaration may capture the module's private scope, so an
exported implementation can use private helpers without exposing those helpers
to qualified access or direct import.

Module preparation retains arbitrary dependent export heads. It does not
reduce the exported layer to simple identifier names. A simple identifier is
required only by operations whose surface syntax specifically requires one,
such as literal dot access.

Prepared module declarations carry their evaluated payloads. Installing a
prepared module, opening it, or capturing one of its functions does not
evaluate the module again.

## Qualified modules

A qualified import installs the module's namespace layer without opening the
namespaces' public layers:

```text
module namespace declarations
enclosing declarations
```

For example, importing `Numbers` qualified makes `Numbers` an ordinary
dependent declaration. The expression:

```datra
Numbers.max
```

performs ordinary declaration resolution for `Numbers`, followed by ordinary
scope or named access for `max`.

Qualified syntax follows the same path. Rewriting:

```datra
Numbers.(some declared syntax)
```

opens `Numbers`' public declaration layer while rewriting the enclosed
expression. There is no separate qualified syntax catalog.

If multiple qualified imports contribute overlapping namespace declarations,
their module layers establish precedence. The most recently installed layer is
considered first. No setup-time namespace collision table rejects the import.

## Unqualified imports

An unqualified import pushes the selected module's public declaration layer.
Multiple imports remain separate layers:

```text
most recently imported module
previously imported module
enclosing declarations
```

For imports `A` followed by `B`, candidates from `B` are considered before
candidates from `A`.

Precedence is determined by applicability, not only by literal identifier
equality:

1. All matching candidates in `B`'s layer are considered as one family.
2. A suspended candidate in `B` remains suspended until its blockers resolve.
3. A lower layer is not selected merely because the upper candidate is
   temporarily undecidable.
4. If every matching candidate in `B` is refuted, selection may continue into
   `A`.
5. Once `B` accepts a candidate, `A` is not considered for that expression.

Cross-module overlap is therefore legal for ordinary unqualified imports. It
does not run the same-scope overlap check and does not merge the layers.

Standard-library visibility is expressed through the same operations:

- `NoStandardLibrary` installs neither `Std` nor its public layer;
- `QualifiedStandardLibrary` installs only the `Std` namespace declaration;
- `AllStandardLibrary` installs `Std` and pushes its public declaration layer.

## `with` scope composition

`with` performs strict importing. It pushes the same public declaration layers
used by ordinary unqualified imports, but marks each pushed layer as
`StrictImport`.

For:

```datra
with First; Second do body
```

the body scope is conceptually:

```text
Second public declarations  [strict]
First public declarations   [strict]
enclosing declarations
```

The layers remain separate. Their order determines traversal. If the highest
matching layer is strict, its match does not hide a match in another lower
strict layer.

Overlapping declarations are valid while they remain unused. This expression
is valid even when `First` and `Second` contain overlapping families:

```datra
with First; Second do yield 0
```

Selection begins with ordinary top-to-bottom lookup. A matching local or
preferential layer is accepted immediately, even if a lower strict layer also
matches. When the first matching declaration is instead in a strict layer,
that acceptance is provisional and the compiler checks the lower strict
layers:

1. If no lower strict layer accepts, the provisional declaration is the unique match
   and is accepted.
2. If a declaration from another strict layer accepts, selection fails with
   the dedicated strict-import ambiguity diagnostic.
3. If a lower strict declaration remains undecidable with blockers, the
   provisional acceptance remains held until that declaration is accepted or
   refuted.
4. Declarations within each layer retain their ordinary family and overload
   semantics; strict ambiguity concerns accepted declarations from different
   strict layers.
5. If a strict layer has no match, ordinary resolution continues downward. A
   local or preferential match reached this way then wins over all layers below
   it.

For simple names, if both `First.x` and `Second.x` exist, using `x` directly in
the body checks both strict layers and reports ambiguity. If only `First.y`
exists, using `y` accepts the unique declaration from `First`. If the body adds
a local declaration of `x` above both imports, that local declaration wins and
there is no strict-import ambiguity. A preferential import above the strict
layers behaves the same way.

Dependent declarations use the same rule. Declarations with heads equivalent
to these can coexist in different strict layers:

```datra
`convert %Nat`
`convert %Int`
```

An application admitted by both strict layers is ambiguous. An application
admitted by exactly one strict layer selects that declaration normally.

The compiler introduces a dedicated structured reason, conceptually:

```haskell
AmbiguousStrictImport String
```

The payload identifies the requested identifier or rendered dependent
application. It is not `OverlappingBindings`, because the declarations are
allowed to coexist. It is not `NamedFieldAmbiguous`, because the ambiguity is
between declarations selected from separate strict layers rather than members
of one named map.

Declarative syntax follows the same rule. Rules from all `with` operands are
available in their original layers. A rule accepted from the highest matching
strict layer is provisional until matching rules in lower strict layers are
decided. A single accepting strict layer succeeds; multiple accepting strict
layers for the same rewritten extent produce `AmbiguousStrictImport`. A higher
local or preferential syntax match wins before this strict check begins.

When a `with` source is not yet resolvable during rewriting, the source
expression is a blocker. The body scope is not constructed until all source
layers are available. Once installed, the layers remain distinct and retain
only their `StrictImport` policy.

## Namespace aliases

Opening a namespace is a property of declarations, not of module identities.
A declaration whose implementation aliases another namespace exposes that
namespace's public declaration layers through ordinary declaration-definition
resolution.

For example:

```datra
Alias := Numbers
```

allows `Alias` to be opened without copying module metadata or syntax rules.
The implementation follows the captured definition of `Numbers` to its public
layer. This behavior applies equally to module namespaces and local namespace
values.

General namespace provenance replaces module-specific runtime lookup. A
runtime declaration may retain an openable public scope or declaration layer,
but that capability is not named or dispatched as a module binding.

## Syntax rewriting

The rewrite stack uses `Scope` as its environment. The rewriting entry points
receive one stateless evaluation capability:

```haskell
Scope -> Expression -> Maybe InterpretedValue
```

Source spans remain separate diagnostic input. They are not fields in `Scope`.

Visible syntax rules are derived from dependent declarations in layer order.
Each compiled rule retains the family scope of its declaration so its codomain
and capture types use the same lexical environment as ordinary declaration
resolution.

The responsibilities previously grouped into `SyntaxContext` map to ordinary
operations:

| Rewrite responsibility | Scope-based operation |
| --- | --- |
| Visible rules | Derive from scoped dependent declarations |
| Capture classification | Evaluate in the active or retained family scope |
| Candidate return type | Evaluate the codomain in the declaration family scope |
| Sequential publication | Publish the finalized declaration into the active layer |
| Recursive declarations | Predeclare lexical `let` families once |
| Qualified syntax | Open the namespace declaration's public layer |
| Unqualified syntax | Read the imported layers already in `Scope` |
| `with` syntax | Push strict import layers; validate a highest strict match against lower strict layers |
| Child lexical scope | Use ordinary scope-entry operations |
| Diagnostics | Carry source span separately |

Scope transitions remain persistent structural updates. Entering a `with` body
does not fail merely because its operands contain overlapping declarations.
Strict-layer checking occurs as part of declaration or syntax-candidate
selection for a concrete use.

## Candidate suspension

The rewrite machine retains its blocker index:

```haskell
machineBlocked :: Map Expression (Set RewriteNodeId)
```

`CandidateHeld` stores the selected candidate, prepared expansion, exact
blocker expressions, and fallback rejection. Publication returns an updated
`Scope`; the machine tests only blockers registered in the index and wakes the
corresponding nodes.

Waking a candidate performs its decision step with the updated scope. It does
not:

- enumerate candidates again;
- rerun structural matching;
- traverse or rewrite completed captures again;
- normalize the expression;
- render and reparse a value; or
- extract a secondary identifier-only blocker representation.

If the decision is still undecidable and produces blockers, the candidate is
registered under the new blockers. If it is undecidable without blockers, it
is refuted with its stored fallback diagnostic.

Layer ordering also applies to held candidates. An unresolved candidate in an
inner imported layer prevents premature selection of an outer module's
candidate.

Strict imports add one selection state without changing structural traversal.
Every candidate is enumerated once and retains its layer policy. A local or
preferential acceptance commits immediately. Acceptance from the highest
matching strict layer is stored as a provisional accepted selection while the
existing candidate search advances through lower strict layers:

- a refuted lower strict candidate is discarded;
- a held lower strict candidate keeps the provisional selection suspended under its exact
  blockers;
- candidates in the same layer participate in that layer's ordinary
  declaration-family decision;
- an accepted candidate from another strict layer produces
  `AmbiguousStrictImport`; and
- exhaustion of lower strict candidates commits the unique provisional
  selection.

Matches in lower non-strict layers cannot replace a provisionally accepted
strict match. Conversely, a local or preferential match found before any
strict match commits immediately, so strict candidates below it are never
considered. No candidate is re-enumerated or structurally rematched during
this uniqueness check.

## Module loading and dependencies

External module loading remains ordered:

1. Parse and rewrite the next module using the declaration layers prepared for
   earlier inputs.
2. Evaluate the module resource once.
3. Construct its namespace declaration layer with captured dependency scopes.
4. Append the prepared module to the ordered input collection.

A later module can therefore reference namespaces from earlier inputs. Its
exported declarations retain those dependencies in their captured scopes.

Installing prepared modules pushes their namespace layers in input order, so
the last installed layer has the highest precedence. Repeated identical module
inputs remain deduplicated by module identity before preparation.

The runtime scope does not retain source files as a lookup catalog. A loaded
module dependency is reached through captured declarations. There is no
fallback which re-evaluates a module source to reconstruct its definition
scope.

## Representation ownership

Responsibilities are divided as follows:

- `DatraTypes.Scope` owns the recursive scope, declaration-layer, scoped
  declaration, runtime payload, presentation, and namespace-provenance types.
- `Evaluation.Scope` owns structural scope composition and declaration lookup
  helpers.
- `Evaluation.Scope.Syntax` owns derivation of visible syntax rules and rewrite
  scope transitions from declaration layers.
- `Evaluation.Expression` evaluates declarations and module resources and ties
  the syntax evaluator callback to the rewrite engine.
- `Interpreting.Source` owns raw source parsing and supplies a prepared `Scope`
  to syntax rewriting.
- `SyntaxRewriting` owns candidate enumeration and selection using the supplied
  `Scope`.
- `SyntaxRewriting.Stack` owns node scheduling, suspension, blocker indexing,
  publication wakeups, and finalization.
- `ModuleInputs` owns filesystem resolution, ordered input preparation, and
  module identity deduplication.

No module owns a copied syntax-rule catalog or an independent namespace table.

## Implementation sequence

### 1. Establish declaration-layer operations

Add and test persistent layer push, lexical entry, namespace opening, and
import-policy operations. Extend declaration-layer metadata with nullary
preferential and strict import policies. Keep every imported public layer
separate; its policy and stack position are the complete selection metadata.

Do not change module installation in this step.

### 2. Prepare modules as scoped declarations

Change module evaluation to retain exported dependent heads and attach their
evaluated payloads and public layers to `ScopedDatraDependentDeclaration`s.
Preserve private captured scopes and presentation origins.

Represent a prepared module by its identity and namespace declaration layer.

### 3. Install qualified and unqualified imports as layers

Replace runtime singleton installation with declaration-layer pushes.
Introduce distinct operations for installing namespace declarations and
opening public declarations. Express standard-library visibility through those
operations.

Remove setup-time namespace collision validation. Add precedence tests for
overlapping qualified and unqualified module inputs.

### 4. Convert namespace access and `with`

Make qualified access use ordinary dependent declaration resolution. Make
unqualified opening push preferential public declaration layers. Make `with`
push the same layers marked strict. Extend declaration and syntax selection so
a highest strict match is committed only after lower strict candidates have
been refuted; route multiple accepting strict layers to
`AmbiguousStrictImport`. Preserve immediate precedence for higher local and
preferential matches.

Retain scope activation, protection, and handoff at the entered lexical
boundary.

### 5. Make syntax rewriting consume `Scope`

Add scope-native syntax rule queries, then change the rewrite stack environment
from `SyntaxContext` to `Scope`. Keep exact blocker expressions and the existing
held-candidate scheduler.

Convert standard-library bootstrap, qualified syntax, unqualified syntax,
namespace aliases, and `with` syntax to the same declaration-layer operations.

### 6. Simplify source interpretation

Reduce `ParsedDatraSource` to its resource envelope, raw located expression,
and base scope. Install prepared module layers before rewriting. Remove standard
and dependency rule-list assembly.

### 7. Delete superseded representations

Delete the obsolete paths once all callers use declaration layers:

- `SyntaxContext`
- `SyntaxRuleFamily`
- `ClassifyHoles` when unused
- `Interpreting.Obsolete.SyntaxEnvironment`
- `preparedModuleRuleSets`
- `sourceSyntaxRuleSets`
- `Interpreting.Syntax` after resource assembly moves to
  `SyntaxRewriting.Resource`
- `LoadedModuleDeclaration`
- module-specific `RuntimeModuleBinding`
- `scopeModuleCatalog`
- `extendModuleCatalog`
- `preparedModuleSources`
- `preparedModuleNamespaceOrigins`
- namespace collision validation
- module-specific branches in scope access and closure resolution
- fallback module source re-evaluation
- recursive syntax-validation seed rewriting

Do not retain compatibility facades or parallel dispatch paths.

### 8. Remove remaining external normalization seams separately

Syntax and module refactoring must consume the expression selected by the
rewrite stack. It does not add replacement normalization. Existing external
normalization and render/parse rematerialization sites remain explicitly
obsolete until removed by their own focused changes.

## Validation

### Scope and module tests

Cover:

- qualified namespace access through an ordinary dependent declaration;
- qualified syntax through the namespace's public layer;
- private module declarations remaining inaccessible but available to exported
  closures;
- multiple namespaces exported by one module layer;
- dependent and templated namespace heads;
- ordered module dependencies;
- repeated identical input deduplication;
- later qualified imports taking precedence for overlapping namespaces;
- later unqualified imports taking precedence for applicable declarations;
- fallback to an outer imported layer after every inner candidate is refuted;
- a held inner candidate preventing premature outer-layer selection;
- aliases retaining their namespace declaration layers; and
- no module re-evaluation during installation, opening, or closure capture.

### `with` tests

Cover:

- disjoint public layers composing successfully;
- unused exact-name overlap compiling and evaluating successfully;
- unused dependent-family overlap compiling and evaluating successfully;
- use of an exact-name overlap producing `AmbiguousStrictImport`
  diagnostic;
- a dependent application admitted by two families producing that diagnostic;
- a dependent application admitted by exactly one overlapping family
  succeeding;
- overlapping syntax rules being permitted until the same source extent is
  accepted by more than one rule;
- ambiguous syntax producing `AmbiguousStrictImport`;
- strict-import ambiguity not being reported as `OverlappingBindings` or
  `NamedFieldAmbiguous`;
- unresolved namespace sources suspending the scope transition;
- private declarations remaining unavailable in the strict public layers;
- a higher local declaration winning over matching strict imports;
- a higher preferential import winning over matching strict imports;
- acceptance from the top matching strict layer waiting for an undecidable
  lower strict candidate;
- one strict match being committed only after every lower strict candidate is
  refuted; and
- operand order not suppressing checks of lower strict layers.

### Syntax-stack tests

Cover:

- `from 0 up` selecting the declared range syntax;
- `_Direction` resolving `up` through ordinary declaration lookup;
- `_NaturalLiteral -> Nat` applying `datra.parse_natural`;
- publication of `Nat` waking candidates blocked by `Nat`;
- unrelated publication not waking those candidates;
- recursive `let` syntax visibility;
- ordinary declaration source-order visibility;
- module-layer candidate ordering; and
- a woken candidate being decided without candidate enumeration or capture
  traversal repeating.

### Language-law tests

For new declaration and namespace paths, retain coverage for optional names,
specification in both directions, and subfederation. Module presentation and
scope aliases must not change the semantic result used by those decisions.

### Performance checks

Compare parsing runtime and allocation against the current baseline. Layer
pushes and namespace opening must reuse prepared declarations. No operation may
rebuild all preceding declaration scopes per rewrite node or re-evaluate a
module to recover its exports.

Run focused scope, syntax, module, and CLI tests during implementation. Run the
complete suite once after deletion of the obsolete paths, with LiquidHaskell
disabled unless verification is requested separately.

## Completion boundary

The refactor is complete when:

- `Scope` is the rewrite stack environment;
- modules and namespace values are represented through dependent declaration
  layers;
- qualified, unqualified, and `with` composition follow the distinct semantics
  defined above;
- all copied syntax and module catalogs are deleted;
- module sources are never re-evaluated to reconstruct runtime scope;
- no obsolete compatibility path can interact with the replacement; and
- builds and focused regression tests pass without a parsing-time or allocation
  regression.

After those conditions hold, report the first remaining semantic failure
exposed by the unified model. Do not repair that next failure as part of the
scope refactor.
