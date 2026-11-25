# `datra` Bootstrap Module

## Status

This document is the implementation handoff for replacing the remaining
`DatraHost`/runtime-singleton bootstrap with an ordinary built-in module. It
also records the native `datra.*` declarations which the current branch lost.

The intended result is:

- `datra` is a `def val` declaration backed by a built-in `PreparedModule`;
- its members are ordinary dependent declarations with native bodies;
- the module is visible only while the canonical bundled standard library is
  prepared;
- `Std` exports its own ordinary `datra` declaration through
  `def val datra := datra`; and
- all later source obtains `datra` through the normal standard-library import.

## Current failure

`libs/std.datra` currently begins with:

```datra
(datra.begin (()
  Std := datra.begin ((
    ...
  )
  public this))
)
```

The current `DatraHost.datraHostValue` still supplies constants, types,
runtime functions, `parse_natural`, and range bodies, but it no longer supplies
`datra.begin`. The hook refactor renames these two body declarations to
`datra.parse_natural_body` and `datra.begin_body`. Until the opening reference
is renamed and `begin_body` is restored, the application cannot rewrite to a
resource block. Module preparation reaches `resourceBlock` with an application
and reports:

```text
ModuleEvaluationFailed ModuleRequiresBlock
```

This is the first blocker exposed by the current cleanup.

## Current split-brain bootstrap

The implementation currently has three partially overlapping entry points:

1. `installDatraHost` in `Evaluation/Expression.hs` constructs a host atlas map
   and installs it as a `RuntimeSingletonPayload` named `datra`.
2. `parsedDefaultModule` installs that singleton while rewriting the bundled
   `std.datra` source.
3. `moduleBaseScope` installs it for every module whose basename is
   `std.datra`.

`standardModuleScope` also prepares and installs `Std` on top of the same base
scope containing the host singleton. This couples the private bootstrap value
to the resulting standard-library environment.

The current representation has two kinds of declarations inside the same
scope layers:

- `ScopedDatraDependentDeclaration`, representing source dependent
  declarations and optionally carrying a runtime payload; and
- `ScopedRuntimeSingletonDeclaration`, representing a runtime-created name
  through `RuntimeSingletonPayload`.

Although scope lookup now uses common declaration layers, runtime singletons
still carry a parallel declaration model: name, `def` flag, value,
presentation, origin, definition, public scope, and reevaluation policy.
`DatraHost` builds a host map on top of that model instead of producing a
module of ordinary declarations.

## Target module identity

`PreparedModule.preparedModuleIdentity` is currently a `FilePath`. Replace it
with an explicit identity type so built-in and source modules cannot be
confused:

```haskell
data ModuleIdentity
  = SourceModuleIdentity FilePath
  | BuiltinModuleIdentity BuiltinModuleName
```

The exact constructors may vary, but the built-in `datra` identity must be
stable, distinct from every file path, and used by the normal prepared-module
deduplication and diagnostics.

Module identity does not define lookup semantics. Lookup continues through the
dependent declaration layer retained by the prepared module. Qualified access
such as `datra.begin_body` is the ordinary application/access of the `datra`
declaration followed by the `begin_body` declaration in its public scope.

## The built-in `datra` module

Construct `datra` directly as a `PreparedModule` whose namespace layer contains
an ordinary scoped declaration equivalent to:

```datra
def val datra := <native namespace value>
```

The `datra` declaration retains a public declaration scope containing its
members. Those members use the same dependent declaration representation,
matching, overlap handling, captures, type checking, protection, presentation,
and import behavior as source declarations. There is no host-map member lookup
and no special handling for simple identifiers.

Native and source modules are two producers of the same prepared module form:

```text
source declarations ─┐
                     ├─> PreparedModule ─> installPreparedModule
native declarations ─┘
```

The existing `installPreparedModule` remains the installation boundary.

## Native declaration bodies

A native member is a normal dependent declaration whose implementation is
supplied by Haskell rather than an `Expression`. Refactor the scoped
declaration representation around a function-body capability, for example:

```haskell
data ScopedDeclarationBody
  = SourceDeclarationBody Scope Expression
  | NativeDeclarationBody NativeBody
  | EvaluatedDeclarationBody InterpretedValue
```

This sketch describes the ownership boundary, not a required constructor
layout. The important properties are:

- the declaration itself owns its head, modifiers, capture schema, and body;
- `def` and `val` are declaration modifiers rather than booleans in a runtime
  payload;
- every native function-body value uses the existing `functionBodyType`, whose
  Datra category is `FunctionBodyAST`;
- `functionBodyType` classifies the body value and is distinct from a function
  signature;
- a function body owns behavior and closure state, with no function domain or
  codomain;
- applying a function signature to a body constructs the typed function;
- native invocation uses the ordinary dependent-declaration application path;
- a body may retain bidirectional implementation capability which becomes a
  typed federation insertion when a compatible signature is applied;
- the declaration's public scope and evaluated cache remain attached to the
  declaration/module rather than forming a second node kind; and
- after signature application, native syntax-valued bodies return typed syntax
  values through ordinary function evaluation.

The current `DatraHost.runtimeBody` embeds an `EvaluatedFunction` with
`anyTypeValue` as both domain and codomain. Replace those placeholder function
types with a body value classified by `functionBodyType`. Reuse the existing
type value rather than introducing a second native-body category. This applies
to every `datra` hook member implemented as a function body, regardless of
whether its exported name ends in `_body`.

Once source and native declarations share this representation, remove
`ScopedRuntimeSingletonDeclaration` and `RuntimeSingletonPayload`. Runtime
caches and contextual evaluation capabilities can remain internal fields of a
prepared declaration; they no longer define another declaration language.

## Required `datra.*` declarations

The hook module requires these eight native bodies:

1. `datra.let_body`
2. `datra.def_body`
3. `datra.val_body`
4. `datra.begin_body`
5. `datra.do_body`
6. `datra.fun_body`
7. `datra.if_body`
8. `datra.with_body`

Update every standard-library reference from `datra.begin` to
`datra.begin_body`, including the two bootstrap applications and the surface
`begin` declaration implementation.

The current `DatraHost` member `datra.parse_natural` is renamed to
`datra.parse_natural_body`. Its value has `functionBodyType`, while its domain
and codomain belong to the function signature which consumes it.

The standard declaration:

```datra
def val $"%(_NaturalLiteral)" :=
  (_NaturalLiteral -> Nat) datra.parse_natural_body
```

applies the signature to the body, producing the typed function used by the
declaration implementation.

The eight restored bodies are also ordinary native declaration bodies. Their
implementations may manipulate typed syntax values, but their discovery and
invocation come from the declaration stored in the `datra` module. Reintroduce
the transformations themselves without restoring the removed
`DatraHost.Syntax`, `DatraHostSyntaxDefinition`, syntax-definition registry, or
a parallel syntax-context lookup.

The body behavior to preserve is:

| Declaration | Result |
| --- | --- |
| `let_body` | adds the `let` declaration modifier |
| `def_body` | adds the `def` declaration modifier |
| `val_body` | adds the `val` declaration modifier |
| `begin_body` | constructs a block expression from entries and a result |
| `do_body` | constructs a function body from entries and a result |
| `fun_body` | constructs `Fun` from its expression |
| `if_body` | constructs a conditional, with an optional else branch |
| `with_body` | constructs scoped evaluation from module operands and a body |

`parse_natural_body`, once paired with the signature above, converts the
supplied natural-literal value to `Nat`.

That conversion is total over the applied `_NaturalLiteral -> Nat` signature.
The typed function validates membership before invoking the body, and the body
recovers the unique retained `Nat` witness. It does not reparse an arbitrary
string or report `NoApplicableFunctionAlternative` for a valid
`_NaturalLiteral`. Canonical string decoding remains at the construction and
membership boundary of `_NaturalLiteral`.

All currently retained `datra` constants, types, boolean/ordinal operations,
range bodies, and other native functions must migrate into this module as
ordinary declarations before the host map is deleted.

## Standard-library bootstrap lifecycle

The built-in hook has one authority boundary: preparation of the canonical
bundled `libs/std.datra`.

The lifecycle is:

1. Create a clean root scope for the canonical bundled standard-library
   source.
2. Install the built-in `datra` prepared module into a private bootstrap scope.
3. Rewrite and prepare `libs/std.datra` using that scope.
4. Evaluate the standard-library declaration:

   ```datra
   def val datra := datra
   ```

   The right-hand side resolves the private built-in declaration. The
   left-hand side creates the normal `Std.datra` declaration retained by the
   prepared standard module.
5. Discard the bootstrap scope.
6. Install the prepared `Std` module into the caller's clean scope with the
   requested qualified or open visibility.

As a result, ordinary source sees `datra` only through `Std`. Source evaluated
with `NoStandardLibrary` has no `datra` binding unless a module explicitly
provides one.

The bootstrap decision belongs to the trusted standard-library loading entry
point. The current trusted-source check in `Interpreting/Source.hs` already
compares the source with `requiredBundledLibrarySource`; consolidate this into
one canonical loader/identity boundary. Remove the basename check from
`moduleBaseScope`, so an unrelated file named `std.datra` receives no built-in
authority.

## Parsing, rewriting, and evaluation modes

The bootstrap crosses three ordinary execution phases:

1. **Raw parsing** produces an unresolved AST and does not consult declarations.
2. **Syntax rewriting** derives visible rules from the declaration layers in
   `Scope`. During standard-library bootstrap, this is where native bodies such
   as `datra.begin_body` and `datra.val_body` become available through their
   ordinary declarations and receive their signatures from `std.datra`.
3. **Evaluation/module preparation** evaluates declaration bodies, retains
   public scopes, and produces the `PreparedModule` installed by later scopes.

The same declaration identity must survive all three phases. The bootstrap
module supplies declarations to `Scope`; it does not populate a separate
syntax context or evaluator-only host map.

## Relationship to injective `val`

The built-in namespace declaration and the bridge
`def val datra := datra` are zero-capture values, so their injectivity proof is
the singleton case described in `DEPENDENT_DECLARATION_INJECTIVITY.md`.

Native bodies are `functionBodyType` values without intrinsic function
signatures. When `std.datra` applies a compatible signature to a bidirectional
body such as `parse_natural_body`, `from_body`, or `range_body`, the resulting
typed function receives the shared
forward/preimage insertion capability. The hook module must not retain the
current forward-only `RuntimeFunctionInsertion` as a private exception.

For `parse_natural_body`, applying `_NaturalLiteral -> Nat` yields an
isomorphism. The inverse maps each `Nat` to its canonical natural-literal value.
The body itself is neither a typed function nor an isomorphism until that
signature is applied. Its forward operation is total for every member admitted
by that signature.

The internal `$val` modifier remains present on `val` declarations. The
injectivity proof is separate evidence retained by their prepared value.

## Implementation sequence

1. Add explicit module identity and construct a minimal built-in `datra`
   `PreparedModule` containing `datra.begin_body`; update the standard-library
   bootstrap and declaration references to that name.
2. Move standard-library parsing/preparation to the private bootstrap lifecycle
   and remove the basename-triggered installation.
3. Restore the remaining seven missing syntax-valued bodies and rename the
   retained natural-literal body to `parse_natural_body`; construct every
   body-valued member with the existing `functionBodyType`.
4. Migrate every remaining `DatraHost` constant and function into native
   declarations within the same module.
5. Replace runtime singleton declarations with the unified scoped declaration
   body representation; migrate contextual and cached runtime declarations.
6. Delete `DatraHost`, `datraHostValue`, `installDatraHost`,
   `ScopedRuntimeSingletonDeclaration`, and `RuntimeSingletonPayload` after
   their call sites use prepared declarations.
7. Audit syntax rewriting, module imports, and evaluation for host-map,
   filename, and runtime-singleton branches.

Prepare the built-in module once and retain its declaration layer. Installation
must push that retained layer without rebuilding the module, re-evaluating
members, or rematerializing a host map.

## Required tests

### Bootstrap visibility

- the canonical bundled standard library rewrites and prepares with the
  private built-in module;
- an unrelated file named `std.datra` receives no bootstrap binding;
- `NoStandardLibrary` source cannot resolve `datra`;
- qualified standard-library mode exposes the ordinary declaration as
  `Std.datra`, while open standard-library mode imports it as `datra`;
- the private built-in module is absent from the final caller scope.

### Native declarations

- all eight restored bodies resolve through dependent declaration lookup;
- every body-valued hook member has `functionBodyType` and no intrinsic
  function signature;
- applying `_NaturalLiteral -> Nat` to `parse_natural_body` produces a total
  typed function and a true isomorphism with canonical natural literals;
- valid natural literals never take a partial body-failure path;
- `from_body` and `range_body` retain their true insertion capability;
- aliases and complex dependent heads follow the same lookup path as simple
  identifiers;
- declaration overlap and import-layer behavior is identical for native and
  source modules.

### Cleanup and performance

- source search finds no `DatraHostSyntaxDefinition`, syntax-definition
  registry, host atlas-map bootstrap, basename authority check, runtime
  singleton node, or separate host syntax context;
- the built-in module is prepared once and installed by layer reuse;
- lookup does not enumerate or reevaluate unrelated native declarations;
- standard-library preparation does not externally normalize or rematerialize
  declaration values.

## Completion criterion

The refactor is complete when the canonical standard library can bootstrap
from a private built-in `datra` `PreparedModule`, export `datra` through its own
ordinary `def val`, and leave no hidden hook in later scopes. Every `datra.*`
member must be an ordinary dependent declaration, including all nine native
bodies used by `libs/std.datra`, and the runtime-singleton/host-map declaration
model must be gone.
