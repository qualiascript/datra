# Scoped Module Access Implementation Plan

## Objective

Give module loading and lexical scope opening separate meanings:

- `import "numbers"` loads a module and binds only its qualified exported name,
  such as `Numbers`.
- `.` is the module scope operator. `value.(expression)` evaluates `expression`
  as its own expression in a fresh lexical scope populated from `value`'s public
  named members.
- If `value` is an imported module, the fresh scope also receives that module's
  exported syntax rules.
- `import all` is removed.
- Standard executable programs behave as though their complete source were
  wrapped in `Std.(...)`, unless standard-library loading is disabled.
- Library modules open `Std` explicitly around the part of the module that needs
  the standard scope. `std.datra` never opens or imports itself.

The implementation must not recognize `Std`, `import`, `all`, or any other
surface spelling in the neutral parser. Surface import syntax remains declared
by the standard library.

## Language semantics

### Qualified import

The only import operation is:

```datra
import "numbers"
```

When used as an entry in an executable lexical scope, it creates a new immutable
scope for the entries that follow it. The new scope adds the imported module's
qualified exported binding and does not add the module's members individually.

An import never changes the visibility of an earlier entry. Repeated imports of
the same module are idempotent, and conflicting qualified names remain errors.

### Module scope operator

The module scope operator has the general form:

```datra
source.(body)
```

It performs these steps:

1. Evaluate `source` in the enclosing scope.
2. Extract its public named members.
3. Enter a fresh child scope containing those members.
4. Reject any non-identical collision between an opened public member and an
   outer apostrophe-prefixed identifier.
5. Add syntax rules associated with `source` to the rewrite environment for
   `body`.
6. Rewrite and evaluate `body` in that child scope.
7. Return the value of `body`, applying the ordinary child-scope handoff rules.

The child scope is lexical. Its values, declarations, imports, and syntax rules
do not leak into the enclosing scope.

The RHS is always interpreted as its own expression in the newly opened module
scope; it is not a field name attached to the LHS. Thus:

```datra
a.x
```

lowers to `ScopeAccess a (IdentifierReference x)` and evaluates the identifier
expression `x` inside the scope opened from `a`. Likewise, `a.(expression)`
evaluates the complete `expression` there. This one rule covers both the short
identifier spelling and arbitrary parenthesized RHS expressions.

The short form:

```datra
source.member
```

is the module scope operation with an identifier-reference RHS. Its canonical
source spelling remains the short form. A non-identifier RHS is rendered with
explicit parentheses.

Opening a module scope must also enforce the existing consistency policy for
apostrophe-prefixed identifiers. If a public module member would shadow an
outer-scope apostrophe identifier and the two bindings do not have identity,
compilation fails with an inconsistent-shadowing diagnostic. An identical
binding is permitted. Reuse the existing consistent-shadowing identity test and
report `InconsistentShadowing name`; do not introduce a separate definition of
identity for modules. This check happens when constructing the module scope,
before interpreting the RHS.

Opening a scope exposes only public exported names. It must not expose a
module's private evaluation scope merely because that scope is available to the
module loader.

### Maps are still maps

The module scope operator does not turn its RHS into a statement block. For
example:

```datra
my_map := Std.(
  a := 1
  b := 2
)
```

evaluates to the ordinary map `(a := 1; b := 2)`.

Imports have effects only when they occur as entries of an executable lexical
scope, such as a program, `begin` block, or function body. Merely placing an
import-shaped expression in a literal map does not hoist it or make the map a
statement block. Existing block-forming syntax remains responsible for deciding
whether a sequence is executable.

This distinction allows a library to open Std around its complete executable
module body:

```datra
Std.(
  import "numbers"

  -- declarations and expressions

  yield Example := (...)
)
```

Once Std's rules are active on the RHS, `yield` forms the executable program
scope in the normal declarative-syntax pass. Imports in that program affect only
the entries that follow them inside the scoped RHS.

### Standard executable scope

The default executable entry path supplies a qualified `Std` module and opens
it around the complete source expression. This is a semantic source boundary,
not a textual insertion and not an `import all` operation.

Consequently, a normal executable continues to use standard values and syntax
without a prefix:

```datra
yield if true then 1 else 0
```

`--no-std` disables both the qualified Std binding and the implicit opening.

Module files do not receive the implicit opening. Non-Std modules receive the
qualified `Std` binding so they can explicitly write `Std.(...)`. The Std module
is parsed and evaluated without any Std binding or self-reference.

## Representation changes

### AST

Generalize named access into an explicit scoped-access node:

```haskell
ScopeAccess Expression Expression
```

Both `source.member` and `source.(body)` lower to this node. Remove
`NamedAccess` once all projection-specific behavior has moved to the general
scope operation.

Update every shared AST operation together:

- normalization;
- canonical lowering and parsing;
- canonical and surface rendering;
- child traversal and generic transformations;
- equality-based round trips;
- source precedence.

Canonical notation must preserve both operands rather than encoding the RHS as
a string. Surface rendering may use `source.member` only when the RHS is a
single identifier reference; otherwise it must use `source.(body)`.

### Module scope metadata

Keep one module descriptor for each loaded module containing:

- its stable identity/path;
- its exported value;
- bindings for its public exported members;
- its exported syntax rules;
- its dependency context.

The qualified module binding must retain a reference to this descriptor. Value
scope opening and syntax scope opening must consult the same descriptor, so the
two views cannot be reconstructed independently or disagree about exports.

Do not re-evaluate a module or reparse function source when using the module
scope operator. Module loading computes the descriptor once and the existing
per-load cache reuses it.

For non-module values, the module scope operator may derive bindings from
ordinary public named map members. Such values have no associated imported
syntax rules unless syntax metadata is explicitly present on the value; no
module name or Std-specific fallback should be inferred.

## Parser and syntax rewriting

### Neutral parsing

Extend postfix module-scope parsing as follows:

- `.name` parses a single identifier-reference RHS.
- `.(...)` parses the contents with the ordinary parenthesized map/expression
  grammar.
- Empty and multi-member maps follow the normal map grammar rather than an
  operator-specific list-of-names grammar.

Remove the specialized `namedAccessNames` expansion for the module scope
operator. Value lookup syntax such as `~(a, b)` may retain its own
identifier-list grammar because it denotes identifier selection, not scoped
evaluation.

### Scoped rewrite environments

Add an explicit rewrite operation for `ScopeAccess`:

1. Rewrite the LHS in the enclosing rewrite environment.
2. Resolve any associated exported syntax-rule set from the LHS module
   descriptor.
3. Create a child rewrite environment containing those rules.
4. Rewrite the RHS exactly once in that child environment.
5. Discard the child rule environment after the RHS.

Within an executable RHS block, imports continue to extend the rewrite
environment left-to-right for subsequent entries. Within an ordinary map, map
rewriting remains ordinary map rewriting and must not invent executable import
effects.

Refactor the rewrite-scope callback so it distinguishes:

- rules introduced after an executable scope entry; and
- rules introduced while entering the RHS of a scoped-access expression.

This should be one general scope-transition abstraction rather than separate
Std handling or a second syntax pass.

### Dependency discovery

Dependency discovery must follow the same scoped syntax visibility rules as the
real rewrite:

- entering `Std.(...)` makes Std's declared import syntax visible inside;
- leaving it removes that visibility;
- discovering an import records the requested path but does not perform a full
  source rewrite;
- each source is neutrally parsed once and fully rewritten once.

The discovery walk must understand executable block boundaries and must not
treat import-shaped data inside an ordinary literal map as an executed import.

## Interpreter and lexical scopes

Evaluate `ScopeAccess source body` by entering a real child `Scope` containing
the public bindings derived from `source`. Use the existing activation and
handoff machinery so generic protection, closures, and function returns cross
the boundary correctly.

Before installing those public bindings, run the ordinary consistent-shadowing
check against outer apostrophe-prefixed identifiers. A non-identical collision
must be surfaced as a compiler error rather than silently masking the outer
binding or deferring the failure until the colliding name is referenced.

Remove projection-only special cases after the general module scope
implementation can preserve:

- qualified canonical names;
- modular presentation dependencies;
- lazy or recursive named fields;
- contextual `this` access;
- ordinary map-field diagnostics.

The scope opened by the module scope operator must preserve the enclosing
function's actual return receiver. A `yield` in a function body nested beneath
one or more module/import scopes must still return from the function activation,
not from the nearest child scope.

Imports remain scope-building events. Simplify the import representation from:

```haskell
Import Bool String
```

to:

```haskell
Import String
```

Then simplify all related APIs from `(Bool, String)` to `String`, including
dependency discovery, module loading, scope construction, and test helpers.

## Standard-library changes

Replace the overloaded declaration:

```datra
'import :=
  ("import %("all") %Str" %
    ($all; Str -> ()) !~"datra.importAll") |
  ("import %Str" % (Str -> ()) !~"datra.import")
```

with the single qualified-import declaration:

```datra
'import := "import %Str" % (Str -> ()) !~"datra.import"
```

Remove:

- the `datra.importAll` syntax adapter;
- the `datra.importAll` external implementation;
- the import-kind Boolean and all branches controlled by it;
- import-all collision behavior that can no longer be expressed;
- tests and diagnostics that exist only for importing every member directly.

Retain validation of module exports because module scope opening still needs a
well-defined public named-member set.

## Source migration

1. Replace `libs/numbers.datra` with the module-scope form (and remove its
   `Std.'import($all; "std")` entry):

   ```kotlin
   Std.(
     yield Numbers := begin

       max := {Args IntLimit,} -> IntLimit? do
         yield it !? it in fun {candidate? : IntLimit; remaining? : List IntLimit} -> IntLimit do
           yield if candidate = Infinity or remaining = () or
             candidate >= (next : this remaining[0; 1..]) then
               candidate else next

       min := {Args IntLimit,} -> IntLimit? do
         yield it !? it in fun {candidate? : IntLimit; remaining? : List IntLimit} -> IntLimit do
           yield if candidate = -Infinity or remaining = () or
             candidate <= (next : this remaining[0; 1..]) then
               candidate else next

     yield public this
   )
   ```
2. Wrap `libs/ordinals.datra` the same way.
3. Convert every fixture or library beginning with
   `Std.'import($all; "std")` into an explicit `Std.(...)` scope around the
   relevant executable body.
4. Replace every `import all "module"` use with a qualified import and an
   explicit module scope around the consumer:

   ```datra
   import "library_one"
   LibraryOne.(
     yield increment 4
   )
   ```

5. Leave sources that require no standard names unwrapped.

## Regression coverage

### Parsing and rendering

- `a.b` and `a.(b)` lower to the scoped-access representation.
- the RHS is a distinct expression: `a.x` resolves the identifier expression
  `x` inside the scope opened from `a`, rather than using projection-specific
  lookup.
- `a.(b, c)` uses an ordinary concatenation map on the RHS.
- multiline RHS maps parse without operator-specific member restrictions.
- arbitrary RHS expressions parse, including function applications,
  specification, and subfederation.
- canonical AST and source render/parse round trips preserve scoped access.

### Scope behavior

- `Std.(if true then 1 else 0)` receives Std syntax only inside the RHS.
- standard syntax used immediately after the expression is unavailable unless
  the enclosing source already opened Std.
- a local declaration shadows an opened member according to ordinary lexical
  rules.
- opening a module scope fails with an inconsistent-shadowing compiler error
  when a public module member would shadow an outer apostrophe identifier with
  a non-identical binding, and succeeds when the binding has identity.
- private module members remain inaccessible.
- nested module scopes compose and restore the outer scope on exit.
- a function `yield` beneath a module scope reaches the true function boundary.
- closures created inside the RHS retain the opened values they actually use.

### Ordinary maps

- `Std.(a := 1; b := 2)` returns the same named map as `(a := 1; b := 2)`.
- ordinary map assignments do not become declarations visible to sibling map
  members.
- an import-shaped map member is not hoisted into an executable scope.

### Imports and modules

- imports bind only qualified module names.
- an import affects only later entries in its executable scope.
- imports inside a module-scope RHS do not escape that RHS.
- transitive imports and cycle diagnostics remain correct.
- repeated qualified imports are idempotent.
- module aliases retain their associated exported syntax rules.
- Std does not import or open itself.

### Type interactions

Cover opened values and syntax through:

- optional names;
- forward and reverse specification;
- subfederation;
- generic function domains and codomains.

The module scope must not strip or weaken any scope-protection metadata carried
by these operations.

### Executable entry behavior

- default CLI programs have standard values and syntax through the implicit
  outer Std scope.
- `--no-std` exposes neither the `Std` binding nor unqualified standard names.
- library modules receive qualified Std only.
- numbers and ordinals load through their explicit Std scopes.

## Implementation order

1. Add `ScopeAccess` throughout the AST, canonical parser, traversals, and
   renderers while preserving existing short-form behavior.
2. Change surface module-scope parsing so the parenthesized RHS is an ordinary
   expression/map.
3. Introduce the shared module descriptor and move public value bindings plus
   syntax rules onto it.
4. Teach syntax rewriting and dependency discovery to enter and leave scoped
   rule environments for `ScopeAccess`.
5. Implement interpreter evaluation with an explicit child scope and verify
   handoff behavior.
6. Reduce imports to qualified-only semantics and remove `import all` from the
   AST, standard library, loader, and interpreter.
7. Implement the implicit Std scope at executable source boundaries.
8. Migrate bundled libraries and fixtures.
9. Run focused parser, scope, module, numbers, ordinals, closure, specification,
   and subfederation tests.
10. Run `git diff --check`, build with LiquidHaskell disabled, and run the full
    test suite once with `-f-liquid`.

## Acceptance criteria

The change is complete when:

- no `import all` syntax or `datra.importAll` implementation remains;
- no import-kind Boolean remains in the AST or module-loading APIs;
- `.` is consistently described and implemented as the module scope operator;
- the module scope operator opens both public values and associated syntax rules
  for exactly its RHS;
- its RHS is evaluated as its own expression, including the identifier
  expression in the short `a.x` form;
- it works with any ordinary RHS expression or map without spelling-specific
  parser logic;
- opening a module scope reports an inconsistent-shadowing compiler error when
  it would shadow an outer apostrophe identifier with a non-identical binding;
- standard executables behave as an implicit outer `Std.(...)`;
- modules use qualified imports plus the explicit module scope operator;
- Std has no self-import or self-opening path;
- syntax rewriting and dependency discovery do not duplicate full rewrites;
- module descriptors and syntax rules are cached and reused;
- all focused regressions and the complete non-Liquid test suite pass.
