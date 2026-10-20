# Finishing the dependent-declaration migration

## Purpose

This document is the working specification and handoff guide for completing
the dependent-declaration pull request. It describes the intended language
semantics, the implementation currently present on the
`dependent-declarations` branch, the first known failing path, and the work
required before the migration can be considered complete.

The target is one declaration system. Literal declarations, evaluated
declaration heads, quoted string-template declarations, and greedy syntax
templates must all enter the same `DependentDeclaration` pipeline. They may
have different name families, but they must not have parallel scope, lookup,
export, validation, or evaluation implementations.

## Current repository state

The state described here is based on commit `9d9fd1c` (`fixing val
injectivity`) on branch `dependent-declarations`.

At that commit:

- `libs/std.datra` rewrites and passes dependent-declaration injectivity
  validation.
- The old infix `%` syntax-type operator and its `SyntaxType` representation
  are gone.
- `%` remains intentionally as the prefix operator for greedy string
  templates and inside quoted string-template interpolation.
- The next known failure occurs while loading `libs/numbers.datra` with the
  qualified standard library:

  ```text
  LookupCaptureHasNoGenericMapView 0 "'datra.DependentDeclaration"
  ```

- The command that reaches this failure is:

  ```sh
  cabal test datra-parsing-test \
    --test-option=-p \
    --test-option='bundled module block shape' \
    -f-liquid
  ```

The failure occurs after `libs/std.datra` itself has loaded. It is therefore
the first post-Std module/export failure, not another Std parsing or
injectivity failure.

## Settled language design

These points are requirements, not implementation suggestions.

### One declaration pipeline

`DatraLanguage.DependentDeclaration.dependentDeclaration` is the semantic
recognizer for executable declarations. Ordinary declarations must not regain
a separate static-name path.

Examples:

```datra
abc := 123
```

declares the literal name `abc`, while:

```datra
(abc) := 123
```

evaluates `abc` as the declaration-head template. A `SyntaxBoundary` around a
declaration operand is transparent to declaration recognition, including
between `let` or `val` and the underlying assignment.

Plain declarations must use the same lookup, named-map, overlap, export, and
evaluation machinery as dependent declaration families. Do not optimize a
plain declaration by routing it through a second singleton-name table.

### `let` and `val`

`let` makes its entire declaration family visible throughout the containing
block, including before its source position. Its implementation remains lazy
and must not capture later ordinary declarations accidentally.

`val` marks a declaration family as canonical only when its mapping from names
to values is injective. A zero-capture declaration is accepted because its
name domain is a singleton, not because of a special syntactic exemption.

The bootstrap declaration is directly expressed as:

```datra
'datra.val (%($val; _DependentDeclaration) := 'datra.val)
```

`'datra.val` is a function whose syntax insertion produces `Val`. It is not a
function body, and there is no `in`-based bootstrap model.

### Greedy string templates

`%` is a first-class prefix operator whose AST operator symbol is also `%`.
Parentheses are ordinary syntax boundaries, not part of the operator itself.
Both of these are consequently valid shapes:

```datra
%$name
%($name; T)
```

Within a greedy template:

- sequence members form one template with flexible source whitespace;
- one canonical space separates realized sequence components;
- `Either` and optional AST nodes describe alternative template structure;
- more specific viable branches win greedily;
- alternatives are interpreted as template branches, not evaluated as an
  ordinary runtime `Either` value;
- absent optional components introduce no extra space;
- literal values use explicit syntax such as `$assert`, not a fallback from an
  unresolved identifier to the literal word `assert`.

For example:

```datra
%($assert; $hard?; _Expr)
```

has the two template branches corresponding to `assert hard <expr>` and
`assert <expr>`, with the more specific `hard` branch selected whenever it
matches.

Quoted templates remain a distinct supported form. Their whitespace is
literal: `"abc def"` must not match `abc  def`. Quoted interpolation is not the
removed infix `%` operator and must not be deleted.

Strings with optional interpolation, explicit template alternatives, greedy
template alternatives, and capture federations all need to use the same
generic branch/federation machinery. There must be no conversion or fallback
between quoted interpolation and greedy templates.

### Standard-library hooks

A `'datra.*` value whose type is `_FunctionBody` must have a `_body` suffix.
The current relevant names are:

```text
'datra.assert_body
'datra.do_body
'datra.fun_body
'datra.if_body
'datra.import_body
'datra.with_body
'datra.len_body
'datra.let_body
'datra.or_body
'datra.and_body
'datra.of_body
'datra.not_body
'datra.from_body
'datra.range_body
```

`'datra.begin` and `'datra.val` are functions, not function bodies, so neither
has a `_body` counterpart.

Keep `public` as ordinary Datra code. It is the source of truth for filtering
private declaration rows and must not be replaced with host-side visibility
logic. It is not a `val` declaration.

The current core declarations in `libs/std.datra` are deliberately split into
a non-`val` block and a `val` block. Do not rearrange or rewrite Std merely to
probe an implementation problem.

### Declaration-family overlap

Families in one block must be disjoint unless the language construct itself
provides deterministic greedy branch selection. Comparisons operate on the
actual capture federations and template structure, not only on rendered
strings, declaration identifiers, or insertion order.

Greedy template alternatives may overlap textually. The generic rule is that
the more specific viable branch is selected. This branch ordering belongs to
greedy templates; it must not weaken ordinary `Either` distinctness.

### Captures and function domains

Captured values are assembled into the function domain with the language's
argument-map/override behavior. Do not implement separate positional
conventions for specific syntax rules.

An optional literal or optional capture is an alternative in the template
family. It is not punctuation metadata, and punctuation is not a special
category of interpolation.

### Range semantics

`from` returns a valued range and is injective because its result preserves
the origin and whether the endpoint was finite, `up`, `down`, or infinite.

`range` now has one bounded surface branch:

```datra
let val %($range; IntLimit; $to; IntLimit) :=
  ({origin : IntLimit; target? : IntLimit} -> IntRange) 'datra.range_body
```

An `IntRange` retains its ordered `IntLimit` endpoints. Range-to-range
subfederation is direction-aware. For example, `range 0 to 10` includes
`range 3 to 8` but not `range 8 to 3`. Singletons are valid within either
orientation. Ordinary integer membership continues to use the underlying
integer federation.

This directional semantic identity is what makes `range` injective, including
at infinity:

```datra
range 0 to Infinity
range Infinity to 0
```

must remain distinct values.

## Implemented architecture

### Declaration recognition and greedy templates

Relevant files:

- `src/DatraLanguage/DependentDeclaration.hs`
- `src/DatraLanguage/AST.hs`
- `src/DatraLanguage/AST/Operator.hs`
- `src/DatraLanguage/AST/Source.hs`
- `app/Parsing.hs`
- `app/SyntaxDefinitions.hs`
- `app/SyntaxTemplateMatching.hs`
- `app/SyntaxTemplateAdmissibility.hs`
- `app/SyntaxRewriting.hs`

`DependentDeclarationHead` distinguishes quoted string-template heads from
evaluated heads. `dependentDeclarationTemplateBranches` lowers greedy
sequence, optional, and `Either` structure into template branches. It inserts
canonical spaces between realized greedy sequence components.

`GreedyStringTemplate` is a dedicated AST node. The parser treats `%` as a
normal prefix operator and leaves parentheses to the ordinary grouping parser.

`RewriteRule` currently retains `rewriteRuleHoleFamilies`, populated by
`compileScopedRewriteRules`. This prevents matching and overlap checks from
re-evaluating capture type expressions recursively during syntax discovery.

### Function insertion evidence

`src/DatraTypes/Evaluation/Value.hs` currently defines:

```haskell
data RuntimeFunctionInsertion = RuntimeFunctionInsertion
  { applyRuntimeFunction
      :: InterpretedValue
      -> Either InterpretingError InterpretedValue
  , preimageRuntimeFunction
      :: InterpretedValue
      -> Maybe InterpretedValue
  }
```

`EvaluatedFunction` carries `functionInsertion`. `DatraHost` constructs
`from_body` and `range_body` from a `RuntimeFunctionInsertion`, and invocation
uses `applyRuntimeFunction` itself so the executable implementation and its
claimed inverse cannot silently use different forward maps.

`attachedFunctionImplementation` in `DatraLanguage.AST` exposes the body
attached by a function specification without evaluating its domain. This is
needed for recursive declarations such as `from`: fully evaluating its typed
RHS requires `Int`, whose definition itself uses `from`. Injectivity discovery
therefore evaluates the attached host body rather than recursively forcing the
signature.

This representation is not finished. The validator currently treats the mere
presence of `RuntimeFunctionInsertion` as sufficient evidence and does not
exercise or verify the left-inverse law. See the ordered work below.

### Direction-preserving `IntLimit` ranges

`IntegerLimit` now lives with semantic value types in
`Evaluation.Value.Semantics`. The new semantic form is:

```haskell
IntegerLimitRangeSemantics IntegerLimit IntegerLimit
```

`integerLimitRangeValue` attaches this identity to bounded unvalued ranges.
`integerLimitRangeIsSubfederationOf` implements directional containment, and
`decideStructuralSubfederation` consults it before falling through to the
underlying composite federation.

The actual finite/infinite map representation still reuses the existing
integer-range, concatenation, and `Either` constructions. The semantic wrapper
preserves orientation for identity and range-to-range comparison.

## First active failure: named-map construction assumes every capture is enumerable

The immediate failure is produced in
`Interpreting.dynamicDependentDeclarationNamedView`, inside `branchView`:

```haskell
captureBounds <- traverse ...
family <- maybe
  (Left (LookupCaptureHasNoGenericMapView ...))
  Right
  (ordinalIndexedProductFamily captureBounds)
```

This happens unconditionally while constructing the `NamedMapView`, before a
caller has chosen between ordinal access and direct lookup by name.

The standard library exports this syntax family:

```datra
%($val; _DependentDeclaration)
```

Its `_DependentDeclaration` capture evaluates to the AST-category type
`'datra.DependentDeclaration`. AST-category types currently have no
`orderedAtlasMapView`, so `ordinalIndexedValueFamily` rejects the capture. As a
result, importing Std into `numbers.datra` fails even though a concrete name
could be decoded and selected directly without enumerating all possible
declarations.

This is not specific to the spelling `val`. After `_DependentDeclaration`, the
same eager assumption is likely to fail for `_Expr`, `_Block`,
`_FunctionBody`, and `_DependentIdentifier` syntax families. Do not add a
special case for `val` or for any one AST category.

The relevant call chain is:

```text
standardModuleEnvironment
  -> importLoadedModule / module export handling
  -> dependentDeclarationNamedView
  -> dynamicDependentDeclarationNamedView
  -> branchView
  -> ordinalIndexedProductFamily
```

The named-map contract currently requires:

- an ordinal order type;
- lookup by ordinal position;
- lookup by name; and
- name membership.

The fix must preserve all four operations without pretending a non-enumerable
family is finite and without scanning rendered names to answer direct lookup.
Direct lookup and membership should decode the requested string through the
prepared template. Ordinal access should be based on a genuine canonical
ordinal family when one exists. If AST-category families are intended to be
ordinal-indexed, implement that capability generically for all AST categories;
do not manufacture a fake order only for this error. If declaration maps can
legitimately support direct projection before their ordinal family is
demanded, represent that distinction explicitly and ensure operations which
actually require ordinal traversal fail locally and honestly.

Do not solve this by dropping syntax declarations from `public this`, by
adding a host-side export filter, or by restoring a separate syntax-rule table
as the semantic source of truth. Exported syntax metadata and the declaration
row capability must describe the same declarations.

## Ordered remaining work

### 1. Repair named-map capability construction

Start with the `LookupCaptureHasNoGenericMapView` failure above.

Requirements:

1. Constructing a dependent declaration's named view must not eagerly require
   ordinal enumeration merely to support lookup by concrete name.
2. `namedProjectionMemberByName` and `namedProjectionContainsName` must use
   `decodeCanonicalTemplateWith` and the retained capture federations.
3. `namedProjectionMemberAt` must preserve foliage-map ordering for genuinely
   ordinal-indexed capture products.
4. No finite list of names may be cached as a substitute for the projection.
5. Failures for genuinely unsupported ordinal traversal must occur at the
   ordinal operation, not while constructing or importing the declaration
   family.
6. The solution must work for syntax-category captures, ordinary finite
   captures, `omega`, and products such as `omega^2`.

Add focused tests before rerunning the module fixture:

- direct lookup into a family whose capture has no generic map view;
- direct membership on the same family;
- importing Std without enumerating `_DependentDeclaration`;
- existing finite, `omega`, and `omega^2` foliage ordering remains unchanged;
- an ordinal access that genuinely cannot be provided reports a localized
  capability error rather than failing during import.

Then rerun:

```sh
cabal test datra-parsing-test \
  --test-option=-p \
  --test-option='bundled module block shape' \
  -f-liquid
```

### 2. Complete injectivity validation generically

The current implementation in `SyntaxRewriting.validateInjective` has three
unfinished aspects.

First, this bypass is still present:

```haskell
| null captures = Right ()
```

Remove it. A literal declaration has a singleton input federation and must be
proved injective through the same cardinality/federation logic as every other
declaration.

Second, the fallback currently builds an input federation and calls
`rewriteApply` on the RHS expression. That is correct only when the RHS itself
is a callable. It is not the semantics of a general declaration such as:

```datra
val "pair %(_x : Int)" := it
```

For a general RHS, validation must evaluate the implementation in a context
where capture-side `it` is bound directly to the already-evaluated input
federation. It must not reparse an AST witness, invoke the RHS as a function,
or invent neutral identifiers.

A suitable generic direction is to replace `contextApply` / `rewriteApply`
with a callback that evaluates an expression under a supplied interpreted
contextual value. This should share the ordinary contextual binding machinery
but avoid re-evaluating the capture-domain expression.

Third, `RuntimeFunctionInsertion` is currently trusted solely because it is
present. Decide and implement the proof boundary explicitly:

- If host insertions are trusted executable evidence, keep the constructor
  internal or expose a deliberate smart constructor, attach the same forward
  map used by invocation, and add round-trip tests for every supplied
  insertion.
- Do not add a boolean `isInjective` flag.
- Do not infer injectivity by applying a pointwise primitive once to an entire
  type federation. A primitive such as `from_body` consumes concrete argument
  values, not a symbolic Cartesian product.
- Keep the model aligned with DatraCore's `DomanialInsertion`: injectivity is
  represented by an executable forward map and partial left inverse.

Required tests:

- literal `val x := ...` succeeds via singleton reasoning;
- identity dependent declarations succeed;
- a many-to-one RHS fails with `NonInjectiveDependentDeclaration`;
- `from` round-trips finite endpoints, `up`, `down`, `Infinity`, and
  `-Infinity`;
- `range` round-trips ascending, descending, singleton, and infinite endpoint
  pairs;
- a runtime function without insertion evidence is not accepted merely
  because it is a host hook.

Remove `contextApply` and `rewriteApply` if the contextual-value evaluator
fully supersedes them. Do not leave both paths active.

### 3. Finish and test direction-preserving ranges

The semantic wrapper compiles, but it needs a complete regression pass.

Verify:

- rendering of finite and infinite `CanonicalIntegerLimitRange` values;
- `range 0 to 10` contains `range 3 to 8`;
- `range 0 to 10` does not contain `range 8 to 3`;
- `range 10 to 0` contains descending subranges;
- singleton subranges work in ascending and descending outers;
- reversed finite ranges are not equivalent federations;
- `range 0 to Infinity` and `range Infinity to 0` are distinct;
- `range -Infinity to Infinity` and its reverse are distinct;
- ordinary integers are still members of the appropriate underlying range;
- range access and slicing continue to use the intended insertion order.

Audit every exhaustive `ValueSemantics` and `CanonicalResult` match after the
new constructors. A normal `-Wall` build already exposed missing cases in
`ToString.Injectivity` and `Access.RangeSelection`; those were updated, but a
repository-wide audit is still required.

Also verify that transformations such as specification, assignment,
coalization, presentation stripping, and function result validation do not
silently erase `IntegerLimitRangeSemantics` before a range-to-range comparison.
If the wrapper cannot survive those operations reliably, promote oriented
limit ranges to an explicit evaluated form/federation primitive rather than
adding isolated semantic-pattern exceptions.

### 4. Continue Std, Numbers, module, and export migration

Once `numbers.datra` loads, run focused groups in this order:

1. parser bundled-library tests;
2. standard-library interpreter tests;
3. module/import tests;
4. function-closure tests;
5. dependent-declaration interpreter tests;
6. integration and CLI fixture tests.

Audit these known boundaries:

- `scopeDependentDeclarationLayers` versus `scopeNamedMapLayers`: their only
  legitimate distinction is unevaluated lexical declaration families versus
  evaluated named-map values. Merge duplicated lookup/overlap behavior.
- `DatraHost.namedMembers` still calls `finiteOrdinalPositions`. A finite
  external module boundary may reject a transfinite map explicitly, but
  internal declaration lookup and visibility must not silently cross that
  boundary.
- `public` currently accepts `List (InhabitedStr; Any; $val?)`. Confirm that
  this type can represent every declaration map it is required to filter. If
  declaration maps can be transfinite, use the appropriate general ordered
  map type rather than materializing them into a finite list.
- `$val` is the optional third field of an exported row. Local `let` status is
  not export metadata.
- direct, qualified, aliased, and `with` imports must preserve both named-map
  capability and syntax metadata.
- `public this` removes only names beginning with `_`.

Do not change `public` to work around a host lookup bug. Its Datra definition
is authoritative.

### 5. Migrate stale syntax-declaration tests and fixtures

The removed feature was the old infix `%` syntax-type operator. Do not delete
valid quoted interpolation tests merely because they contain `%`.

Classify each remaining `%` occurrence into one of these categories:

1. greedy prefix syntax, which is current;
2. quoted string interpolation, which is current;
3. an escaped literal percent character, which is current;
4. a stale syntax declaration or expectation tied to the removed operator,
   which must be migrated or deleted.

Syntax declarations intended to exercise the current whitespace-aware path
should use greedy templates. Examples:

```datra
%($double; Nat) := ...
%($prefix; _Expr) := ...
%(_Expr; $otherwise; _Expr) := ...
%($step; Int; $next) := ...
```

Quoted declarations should remain only where the test specifically exercises
quoted literal whitespace, quoted interpolation, evaluated declaration heads,
or coexistence between quoted and greedy declaration families.

Known files containing declarations or fixtures that require classification
include:

- `test/Datra/Interpreter/IntegrationTests.hs`
- `test/Datra/Interpreter/StandardLibraryTests.hs`
- `test/DatraInterpretingTests.hs`
- `test/DatraParsingTests.hs`
- `test/fixtures/modules/library_one.datra`
- `test/fixtures/modules/explicit_exports.datra`
- `test/fixtures/modules/multiple_exports.datra`
- `test/fixtures/modules/dependent_declarations.datra`

Do not mechanically rewrite string templates used as values, such as
`"from %Int to %Int"`, lookup queries such as `~"arg%Nat"`, or output strings
such as `"sum=%(value)"`.

Add explicit greedy-template regressions for:

- flexible spaces, tabs, and line breaks between components;
- exact whitespace in quoted templates;
- `%$hello` without parentheses;
- parenthesized greedy templates remaining on the greedy path;
- optional components contributing no doubled space;
- `Either` inside a greedy component;
- more-specific branch selection independent of declaration order;
- `$hard` remaining literal even when an ordinary declaration named `hard`
  exists;
- interactions with optional names, `~>` / `<~`, and `of`, as required by the
  repository guidance.

### 6. Remove obsolete paths completely

Run targeted searches after each cleanup. The final tree must not contain:

- `SyntaxType` or `SyntaxTypeOperator`;
- compatibility rule builders for the removed infix `%` operator;
- old `%` evaluator or function-closure unwrapping;
- `standardBootstrapRules`;
- fabricated neutral witness identifiers;
- NUL-prefixed syntax-capture sentinel names;
- special handling keyed on `val`, `in`, `'datra.val`, `assert`, `hard`, or
  any other standard-library spelling;
- fallback from an unresolved greedy component identifier to a literal word;
- tracing or diagnostic dumps added during this migration;
- duplicate quoted-template and greedy-template matching engines where the
  same federation operation can be shared.

The expected remaining percent-related implementation points are the greedy
prefix parser/operator and quoted string-template interpolation/escaping.

### 7. Complete declaration-family correctness regressions

Before the full suite, ensure focused tests cover all of the following:

#### Recognition

- `abc := 123` declares literal `abc`.
- `(abc) := 123` evaluates `abc` as a declaration template.
- `(abc) : Nat` evaluates a dependent-identifier template.
- declaration recognition depends on block position as well as AST shape.
- `SyntaxBoundary` is transparent under `let` and `val`.
- empty declaration names are rejected.
- declaration names cannot be optional; optional dependent identifiers remain
  valid where intended.

#### Scope and recursion

- use-before-`let` works for an entire dependent family;
- an unused failing `let` implementation remains lazy;
- an early `let` does not capture a later ordinary declaration;
- recursive typed functions use a demanded family member rather than a static
  singleton-name shortcut;
- ordinary declarations and dependent families shadow through the same
  rules.

#### Disjointness and greedy selection

- overlapping ordinary/dependent name families conflict;
- equal template shapes with disjoint capture federations coexist;
- ordinary quoted template alternatives still obey `Either` distinctness;
- overlapping greedy branches select the most specific viable branch;
- branch selection does not depend on declaration insertion order.

#### Export and lookup

- direct `~` lookup reaches dependent declarations;
- exported dependent declarations remain accessible with `~`;
- `$val` survives export/import;
- `let` status does not appear in exported rows;
- `public this` removes only `_`-prefixed rows;
- finite, `omega`, and at least one higher transfinite family retain canonical
  foliage ordering.

### 8. Verification order and resource limits

Use focused serial runs while the rewrite fixed point is still changing. A
broken recursive scope can allocate very large amounts of memory; stop and
narrow a run that stops making progress.

Suggested sequence:

```sh
cabal build datra-parsing-test -f-liquid

cabal test datra-parsing-test \
  --test-option=-p \
  --test-option='bundled module block shape' \
  -f-liquid

cabal test datra-interpreting-test \
  --test-option=-p \
  --test-option='standard library and declarative syntax' \
  -f-liquid
```

Use the test binaries' `--list-tests` output to select smaller exact patterns
when necessary. Do not repeatedly give a known-divergent smoke test a long
timeout.

After focused suites are stable, run the complete suite once with
LiquidHaskell disabled:

```sh
cabal test all -f-liquid
```

Run LiquidHaskell verification separately only when explicitly needed.

## Completion criteria

The PR is complete only when all of these are true:

- Std, Numbers, every bundled module, and every fixture load through the
  dependent-declaration pipeline.
- No old infix `%` implementation or compatibility representation remains.
- Greedy templates and quoted templates remain separate first-class forms and
  share generic federation operations where appropriate.
- Ordinary declarations do not use a parallel static-name lookup path.
- `let` families are block-wide, lazy, and capture the correct lexical scope.
- `val` injectivity is established without a zero-capture bypass, fabricated
  witnesses, string-specific dispatch, or applying pointwise primitives to
  whole type federations.
- `from` and oriented `range` have sound executable preimages.
- Declaration-family disjointness and greedy branch choice match the settled
  semantics.
- Named maps preserve direct lookup, membership, ordinal access, and foliage
  order without eager finite materialization.
- `public` remains Datra code and the sole private-name filter.
- `$val`, syntax metadata, named-map capability, and dependent lookup survive
  every module boundary.
- Stale tests are migrated, tests of removed behavior are deleted, and tests
  of still-valid quoted interpolation remain.
- The full non-Liquid test suite passes without tracing, probes, compatibility
  shims, hardcoded standard-library names, or dead migration helpers.
