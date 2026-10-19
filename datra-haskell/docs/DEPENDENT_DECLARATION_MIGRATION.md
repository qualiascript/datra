# Finalizing the dependent-declaration migration

## Goal

Finish replacing the old declaration model with `_DependentDeclaration` through
one cutover that migrates all standard-library syntax declarations and removes
the `%` syntax-type operator and its compatibility implementation at the same
time.

The target is one declaration pipeline. A literal declaration such as
`x := 2`, a declaration whose template is evaluated with `(template) := value`,
and a dependent string-template declaration must differ only in the family of
names they denote. They must not take separate lookup, scope, export, or
evaluation paths.

`_DependentDeclaration` and `_DependentIdentifier` are a semantic pair. A
dependent identifier uses the value on its right to determine bindings on its
left. A dependent declaration uses captures from its left-hand string template
to provide `it` and named captures to its right-hand implementation.

## Decisions that must not be revisited

- A declaration is recognized by its position in a block as well as by its AST
  form. Surface syntax alone is not the semantic distinction.
- `abc := 123` declares the literal name `"abc"`. `(abc) := 123` evaluates
  `abc` as the declaration's string template. The equivalent distinction must
  remain available for dependent identifiers.
- A dependent declaration cannot make its name optional with `?`.
  `_`-prefixed declarations may be private and `'`-prefixed declarations may
  be scope-protected.
- Ordinary declarations use the dependent-declaration pipeline. There must be
  no static-name evaluation or lookup path beside it.
- `let` makes the whole declaration family visible throughout its block, even
  before its source position. Its implementation remains lazy and captures
  only the lexical environment that it is entitled to capture.
- Declaration families in the same function-body block must be disjoint. The
  check is over their possible string values and uses federation operations.
- `val` accepts a dependent declaration only when the mapping from left-hand
  names to right-hand values is injective. This is also a federation property.
- Every declaration name is an `InhabitedStr`; the empty string is not a valid
  declaration name.
- A materialized declaration is a two- or three-slot row:
  `(InhabitedStr; Any; $val?)`. The optional third slot is exactly the `$val`
  marker. Whether the declaration was locally introduced with `let` is not
  export data.
- `public` has exactly one policy: filter out rows whose first name character is
  `_`. It does not interpret `_this`, scope protection, `let`, or any host-side
  visibility metadata.
- A declaration family's local ordinal order is the foliage-map order. Code
  must not enumerate a possibly transfinite order merely to recover names.
- Exported declaration maps must remain usable through `~` lookup.
- When removing the old feature, remove obsolete implementation paths
  aggressively. Delete obsolete tests; migrate tests that still express valid
  behavior.

## Standard-library migration

Migrate `libs/std.datra` and remove the infix `%` implementation as one coherent
change. Do not stabilize either a mixed Std or a fully migrated Std that still
retains the old operator. Convert every remaining infix-`%` declaration,
including overloaded alternatives and precedence-sensitive rules, as part of
the same cutover that deletes the compatibility machinery.

Keep public types and templates expressed in Datra. Keep the corresponding
`'datra` hooks as function bodies, not as declarations or hidden host
registrations. This lets Std continue to expose the types explicitly while the
host supplies only primitive behavior. Do not retain compatibility names such
as `'from` merely because the old `%` declaration needed a callable name.

Overloaded rules should become ordinary dependent-declaration families and be
accepted or rejected by the same disjointness machinery as every other family.
Do not reproduce the old union-of-`SyntaxType` representation in a new wrapper.

The same cutover must migrate every fixture and test helper that still defines
valid syntax using `%`, and delete those that test only the removed feature.
There should be no privileged exception for Std.

### The `val` bootstrap and `in`

The `in` in the bootstrap declaration of `val` is required and is not legacy
syntax. It applies the `val` effect to the declaration that introduces `val`
itself. The direct dependent-declaration form must preserve that contextual
self-application.

There are two distinct inputs in this expression:

1. the contextual adapter supplied by `'datra.val_body in it`; and
2. the capture-side `it` introduced when a particular dependent declaration
   name is matched.

They must remain distinct in the rewrite representation. Declaration discovery
must not extract the nested declaration and discard its enclosing `in`
context. Conversely, the capture-side `it` must not rebind the adapter captured
by that context.

Fix this at the syntax-rule boundary. The general rewrite pass must not contain
special cases for the spellings `val`, `in`, or `'datra.val_body`.

## Syntax rewriting work

The final rule representation needs only two executable meanings:

1. invoke an explicit rewrite-time adapter expression; or
2. perform a dependent runtime lookup of the declaration row selected by the
   matched string.

A direct dependent declaration normally uses the second meaning. A declaration
whose body supplies syntax control through a `'datra` hook must retain the
first meaning at the rewrite boundary. Its typed body still belongs to the
declaration; the host hook must not become a separate generic “implementation”
field that recreates the old abstraction.

Complete the following work in `SyntaxDefinitions.hs` and
`SyntaxRewriting.hs`:

- Preserve enclosing `In` context when discovering and compiling a declaration
  rule, including the `val` self-bootstrap.
- Rewrite a left-associated application spine as one syntax boundary. A prefix
  must not execute while the unconsumed tail could still complete a longer
  infix or template match.
- Resolve competing templates from their structural match, not by identifiers
  and not by incidental insertion order. Longer/more specific viable templates
  must not be preempted by a zero-hole literal declaration.
- Do not extend the temporary `%` frontend while preparing the cutover. Any
  behavior needed by both forms belongs in the dependent-declaration path.
- Remove the temporary zero-capture injectivity bypass. A literal declaration
  is injective because its domain is a singleton; establish that through the
  same federation/cardinality reasoning used for other declarations.
- Keep disjointness at block-family admission. It is not merely parser-rule
  overlap and must not compare only rendered template shapes.
- Ensure diagnostics are localized compiler errors. No partial name extractor
  or runtime `error` is permitted for a dynamic declaration family.

The current `DependentSyntaxLookup`/adapter distinction is close to this target,
but fields and branches that exist only to serve `%` should disappear when `%`
is removed.

## Scope and evaluation work

`DatraLanguage.DependentDeclaration` should remain the sole semantic recognizer
for executable declarations. Parsing may construct literal or template AST
forms, but later stages should consume one `DependentDeclaration` model.

Audit and simplify the scope builder with these requirements:

- All block declarations become `ScopedDependentDeclaration` values, including
  zero-capture literal declarations.
- Visibility is derived from source position plus the declaration's `let`
  property. Do not build a parallel table of ordinary names.
- A `let` family is available before its declaration, but no member is evaluated
  until demanded. An unused family whose body fails must remain harmless.
- An early `let` family must not accidentally capture a later ordinary binding.
- Recursive function preparation must work on demanded family members rather
  than requiring a static singleton name.
- Shadowing and consistency checks must query declaration families. They must
  not recover a static name as a shortcut.

In particular, remove or redesign `dependentDeclarationSingletonName` and its
use in eager-`let` preparation. It is a surviving static-name boundary and
cannot represent an arbitrary dependent family. The replacement should retain
the declaration family itself and demand the required member through its named
map projection.

Also audit `scopeDependentDeclarationLayers` and `scopeNamedMapLayers`. If both
remain, their distinction must be between an unevaluated lexical declaration
family and an evaluated named-map value, not between “new declarations” and an
older ordinary-name mechanism. Merge any operations that perform the same
lookup or overlap decision.

## Named maps, ordinals, and exports

The authoritative operations on a named map are:

- its ordinal order type;
- checked lookup by ordinal position;
- checked lookup by name; and
- checked name membership.

Do not add cached finite member lists, finite-name projections, special empty
views, or special singleton views. Empty and singleton cases should be ordinary
instances of the ordinal machinery.

Use foliage-map traversal to give each dependent family a canonical local
ordering. Preserve symbolic/transfinite order through lookup, concatenation,
scope construction, and `public`. Materialization into a Haskell list is valid
only at a genuinely finite external boundary.

Audit the remaining uses of `finiteOrdinalPositions`, especially in
`DatraHost.namedMembers`. A module/export API may reject a transfinite value if
its external representation is explicitly finite, but declaration lookup and
visibility may not cross that boundary. The failure must be explicit rather
than silently truncating or eagerly scanning.

Likewise, check whether the current Std type
`List (InhabitedStr; Any; $val?)` admits every declaration map `public` must
accept. If `List` is finite-only, use the general ordinal-map type instead.
Never make `public` materialize a transfinite declaration family as a finite
list.

An exported value must retain the named-map capability and any syntax metadata
needed after crossing a module boundary. Do not rescan source text to recreate
it. Module aliases, `with`, qualified Std, and ordinary imports must transport
the evaluated capability itself.

`CanonicalValueImportPresentation` and other host presentation tags should be
reviewed after `$val` rows work end to end. The row already contains the
canonical-value fact; presentation code must not become a second semantic
source of truth.

## `public`

Keep `public` implemented in `libs/std.datra`, not as a `'datra.public` hook.
Keep its current role as a standalone typed filter over declaration rows.
Adjust the collection type if the ordinal audit requires it, but do not add
host visibility behavior. Indexing the first character is total because
declaration names are `InhabitedStr`.

Every visibility path must flow through this function. Delete producer-side
“is public” fields, special `_this` stripping, leading-underscore predicates,
and alternate export filters. A module that wants all declarations can yield
`this`; a module that wants the public subset yields `public this`.

## Removing `%`

Migrate Std and remove `%` in one atomic cutover. That change must remove the old
feature completely:

- `SyntaxType` and `SyntaxTypeOperator` AST cases;
- parser precedence, lexer, rendering, normalization, and traversal support;
- `%` template compilation and `compatibilityRules`;
- evaluator and function-closure branches that unwrap `SyntaxType`;
- projection/matching helpers used only by the compatibility frontend;
- host behavior and diagnostics that can be reached only from `%`; and
- obsolete fixtures and assertions.

Do not remove `%` inside string templates: `%(` interpolation remains part of
string-template syntax. Search results must distinguish the infix operator from
interpolation and from ordinary percent characters.

Delete the AST constructor early in the cutover and let compiler errors reveal
residual old flows rather than preserving adapters to keep old tests green. The
branch need not remain green halfway through this local change; it must be green
when the complete cutover is committed.

## Required regressions

### Parsing and declaration recognition

- `abc := 123` declares literal `"abc"`.
- `(abc) := 123` evaluates the template stored in `abc`.
- `(abc) : Nat` evaluates a dependent-identifier template.
- The same expression outside declaration-bearing block position is not
  silently treated as a declaration.
- Empty declaration templates are rejected.
- `?` is rejected for dependent declarations and remains supported where valid
  for dependent identifiers.

### Rewriting and Std bootstrap

- `val` introduces itself through the contextual `in` form.
- Every migrated Std rule rewrites without `%`.
- Longer infix/template rules beat callable prefixes structurally.
- Overloaded forms select the correct template without relying on declaration
  names or rule insertion order.
- Typed `'datra` hook bodies expose the same public function types as Std does
  today.

### Scope, `let`, disjointness, and injectivity

- A use before a `let` dependent declaration resolves.
- An unused `let` dependent declaration does not evaluate a failing body.
- A `let` dependent declaration does not capture a later ordinary declaration.
- Ordinary and dependent declarations with overlapping name families conflict.
- Equal template shapes with disjoint capture federations coexist.
- `val` accepts identity/injective families and rejects many-to-one families.
- Zero-capture `val` declarations pass by the singleton proof, not a special
  condition.

### Export and lookup

- `public this` removes only `_`-prefixed declaration rows.
- `$val` survives export and import; local `let` status does not.
- Direct, qualified, aliased, and `with` imports preserve named-map and syntax
  capabilities.
- A dependent declaration exported by a module is accessible with `~`.
- Finite, `omega`, and at least one higher transfinite family retain foliage
  ordering without eager enumeration.

Migrate existing tests when they still express these semantics. Delete tests
whose only purpose is the `%` operator or another removed representation.

## Recommended execution order

1. Fix declaration discovery so the `val` bootstrap retains its enclosing
   contextual `in` adapter.
2. Make direct dependent syntax bodies invoke the correct rewrite-time adapter
   without adding identifier-specific logic.
3. Replace the static singleton eager-`let` path with lazy family scheduling.
4. In one cutover, migrate all Std syntax declarations, migrate or delete `%`
   fixtures and tests, and remove the operator and all compatibility code.
5. Use the resulting compiler errors to remove every residual old flow rather
   than adding compatibility shims.
6. Get focused parsing and StandardLibrary tests green, including module export
   and `~` regressions.
7. Complete the finite/transfinite and obsolete-path audits.
8. Run the full suite once the focused suites are stable.

Use serial or narrowly filtered test runs while iterating. The rewrite and
interpreter suites can consume substantial memory when a broken fixed point
expands recursively; stop a run that stops making progress rather than starting
additional concurrent runs.

## Completion criteria

The migration is complete when:

- Std contains no infix `%` declarations;
- the `%` operator has no AST, parser, evaluator, renderer, or test-only path;
- every declaration uses the `DependentDeclaration`/named-map pipeline;
- `val` self-bootstrap still uses and tests its contextual `in` application;
- disjointness and injectivity are federation checks;
- `let` families are pre-visible and demand-driven;
- `public` is ordinary typed Datra code and the sole visibility filter;
- declaration maps preserve ordinal order and transfinite lookup;
- module boundaries preserve named-map and syntax capabilities;
- exports are reachable with `~`; and
- there are no partial static-name assumptions, duplicate declaration
  recognizers, cached finite declaration lists, or obsolete compatibility
  abstractions left in affected files.
