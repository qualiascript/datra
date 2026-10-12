# New Module Scoping Plan

## Objective

Give module loading and lexical scope opening separate meanings:

- `import <List String> <function body>` loads the listed modules, federates all
  of their public exported identifier binders into an anonymous function
  domain, and eagerly invokes that function on the import body.
- `.` is the module scope operator. `value.(expression)` evaluates `expression`
  as its own expression in a fresh lexical scope populated from `value`'s public
  named members.
- `'with` opens several module values at once. `with Std; Numbers do ...`
  federates their public bindings and syntax metadata, then evaluates the
  function body in that combined module scope.
- If `value` is an imported module, the fresh scope also receives that module's
  exported syntax rules.
- `_AST` and `datra.AST` are removed. Every standard-library syntax hole and
  adapter signature uses the narrowest structural category, such as `_Expr`,
  `_Block`, `_IdenExp`, or `_FunctionBody`.
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

The only import operation has the form:

```datra
import <List String> <function body>
```

For one module:

```datra
import "numbers" do
  maximum := Numbers.max (1; 2; 3)
yield maximum
```

The same form accepts multiple strings:

```datra
import "numbers"; "ordinals" do
  maximum := Numbers.max (1; 2; 3)
yield (maximum; Ordinals)
```

In particular, import and the module scope operator must compose directly:

```javascript
import "numbers" do Numbers.(... yield ...)
```

Here import supplies the qualified `Numbers` value as the synthesized
function-domain binding, `Numbers.(...)` opens that module for its RHS, and the
`yield` inside the module scope returns from the eagerly invoked anonymous
import function. The module scope must not capture or replace that function's
return receiver.

`'import` evaluates its `List String` operand in the enclosing scope and loads
each named module. It then constructs a domain value from every public
identifier binder in each module's yielded value. A conventional module that
yields one `Numbers` binder contributes `Numbers`; importing two conventional
modules may contribute both `Numbers` and `Ordinals`. Every imported binder
retains its source module descriptor and associated exported syntax metadata.

Conceptually, the one-module domain has the value
`(Numbers := <loaded numbers module>)`; the multiple-module domain is the
corresponding named concatenation, such as
`(Numbers := <loaded numbers module>; Ordinals := <loaded ordinals module>)`.
This is the value used both as the anonymous function's domain and as the eager
call's argument.

A module is not required to yield exactly one identifier binder. For example,
this is a valid module result:

```go
yield (Numbers1 := ...; Numbers2 := ...)
```

Importing that file contributes both `Numbers1` and `Numbers2` to the synthesized
function domain. Module identity remains the stable file/path identity; the
loader must not invent or require one distinguished namespace for the file.

Dependent identifier binders are valid exports as well. Combine all exported
binders with the ordinary federation operation used for function domains and
argument routing. Existing federation rules decide whether simple and dependent
identifier fibers are disjoint and unambiguous. If they overlap, or their
disjointness cannot be established where the ordinary rules require it, report
the existing federation ambiguity/refutation diagnostic. Do not add a stricter
import-only requirement for total maps of simple identifiers, and do not choose
one matching dependent binder arbitrarily.

The `FunctionBody` operand becomes the body of a synthesized anonymous
function whose domain is that federated exported-binder value. The implementation
then eagerly invokes the function with the same domain value. Consequently
import scope is ordinary function-application scope: argument binding,
activation, `yield`, closures, protection, and result handoff all use the
existing function machinery instead of a second import-specific evaluator.
Imported modules do not add their public members individually.

The imported bindings exist only for the function body operand. They do not
affect an earlier expression, a later sibling expression, or the enclosing
scope. To keep an import active across several declarations, those declarations
belong in the import's function body.

Repeated paths in one import list are idempotent. Exports contributed by
different paths are combined by the same federation rules as exports from one
path, rather than by a separate import-specific name-collision policy.

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

### Multiple module scopes with `'with`

The standard library declares a multi-module scope form:

```datra
with Std; Numbers do
  ...
yield ...
```

`'with` evaluates each module-valued operand in the enclosing scope, constructs
a new federation from those module values, and evaluates the supplied
`FunctionBody` in the module scope opened from that federation. The resulting
scope contains the public members and associated syntax rules contributed by
both `Std` and `Numbers`; the qualified `Std` and `Numbers` values themselves
remain ordinary enclosing bindings.

Semantically, `with modules body` is the multi-source spelling of the module
scope operation: federate `modules`, retain all contributing module descriptors,
then use that federation as the LHS of `ScopeAccess` with `body` as its RHS. The
implementation should lower to the shared scope machinery rather than creating
a second evaluator for `'with`.

Federation construction is atomic. The ordinary federation and syntax-overload
rules must prove that the contributed public binder fibers and syntax rules are
unambiguous. If the combination overlaps or its required disjointness is
undecidable, compilation fails before the body is rewritten or evaluated. There
is no left-to-right precedence between modules. Repeating an identical module
value is idempotent under the ordinary federation rules.

As with direct `source.(body)` access, a `yield` under `'with` continues to
target the actual enclosing function activation. The temporary combined module
scope and its syntax rules disappear after the function body.

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

An import is an expression whose scope is exactly its `FunctionBody` operand.
Placing an import expression in a literal map does not hoist its qualified
bindings into sibling map members or turn the map into a statement block.
Existing block-forming syntax remains responsible for deciding whether a
sequence is executable.

This distinction allows a library to open Std around its complete executable
module body:

```datra
Std.(
  import "numbers" do
    -- declarations and expressions using the qualified Numbers binding
  yield Example := Numbers.(...)
)
```

Once Std's rules are active on the RHS, `yield` forms the executable program
scope in the normal declarative-syntax pass. The import adds `Numbers` only to
its function body and returns that body's result; it does not mutate the
surrounding `Std.(...)` scope.

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

Refactor import into an expression that retains both operands:

```haskell
Import [String] Expression
```

The `Expression` must be a `FunctionBody`, as guaranteed by the standard
library's `_FunctionBody` syntax hole. Canonical parsing, rendering, traversal,
normalization, and round trips must preserve the complete path list and body.
If sharing the body representation requires factoring the existing
`FunctionBody` fields into a common payload, both functions and imports should
use that payload rather than copying body-evaluation logic.

### Specific syntax categories

Remove the catch-all standard-library binding and external type:

```datra
_AST := !~"datra.AST"
```

This removes the public external symbol `datra.AST`, the `AnyAST` meta-type
constructor, `astTypeValue`, and the rule that treats every syntax category as a
subtype of a universal AST category. It does not remove the compiler's internal
Haskell `Expression` data type; it removes only the dynamically exposed
catch-all syntax value/type.

Every syntax template must use the most specific category that matches the
captured or returned structure:

- `%_Expr` has type `_Expr`;
- `%_Block` has type `_Block`;
- `%_IdenExp` has type `_IdenExp`;
- `%_FunctionBody` has type `_FunctionBody`;
- an adapter returning an ordinary expression returns `_Expr`;
- `datra.do`, or any other adapter that constructs a function-body node,
  returns `_FunctionBody`.

For example, standard-library signatures should become:

```datra
'begin :=
  "begin %_Block yield %_Expr" %
    (_Block; _Expr -> _Expr) !~"datra.begin"

'do :=
  "do %_Block yield %_Expr" %
    (_Block; _Expr -> _FunctionBody) !~"datra.do"

'if :=
  "if %_Expr then %_Expr else %_Expr" %
    (_Expr; _Expr; _Expr -> _Expr) !~"datra.if"
```

Audit every declaration in `std.datra` and every syntax-control adapter rather
than limiting this change to import. If an operation consumes or produces a
structural category not represented above, introduce another narrow private
category; do not restore a renamed universal AST escape hatch.

### Module scope metadata

Keep one module descriptor for each loaded module containing:

- its stable identity/path;
- its exported value;
- the federation of its public exported identifier binders, including dependent
  binders;
- bindings or routing information for those exported binder fibers;
- its exported syntax rules;
- its dependency context.

Every imported binder contributed by a module must retain a reference to this
descriptor. A descriptor belongs to the file identity, not to a presumed single
module name. Value scope opening and syntax scope opening must consult the same
descriptor, so the two views cannot be reconstructed independently or disagree
about exports.

A federation created for `'with` or a multi-file import must retain the complete
set of contributing descriptors. Do not collapse it into an ordinary map and
then attempt to rediscover syntax metadata from member names. Its public binder
federation, combined syntax rules, and provenance must be constructed and
validated together.

Do not re-evaluate a module or reparse function source when using the module
scope operator. Module loading computes the descriptor once and the existing
per-load cache reuses it.

For non-module values, the module scope operator may derive bindings from
ordinary public named map members. Such values have no associated imported
syntax rules unless syntax metadata is explicitly present on the value; no
module name or Std-specific fallback should be inferred.

## Parser and syntax rewriting

### Neutral parsing

Expose the neutral function-body syntax category beside the existing `_Expr`,
`_IdenExp`, and `_Block` external types:

```datra
_FunctionBody := !~"datra.FunctionBody"
```

`_FunctionBody` denotes an already parsed function-body node and is available
to standard-library syntax declarations. It does not teach the neutral parser
the spellings `import` or `with`; both remain entirely in `std.datra`.

There is deliberately no `_AST` fallback. Syntax capture and application must
reject a value of the wrong structural category at the typed adapter boundary,
rather than accepting it through `AnyAST` and failing later.

The hole must capture the whole body in the required composition form:

```javascript
import "numbers" do Numbers.(... yield ...)
```

In particular, parsing must not require the body-closing `yield` to appear
outside the module-scope RHS, and the preceding path-list hole must not consume
any part of the function body.

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

The `'with` adapter lowers its module-list expression and `_FunctionBody` to
this same operation. Before rewriting the body, resolve all contributing module
descriptors, form and validate their public binder/syntax federation, and make
that combined metadata available to the ordinary `ScopeAccess` rewrite. Reject
an ambiguous federation before rewriting the body, and discard the combined
environment afterward.

Add a scoped rewrite operation for `Import paths body`:

1. Resolve and discover every path retained in the import node.
2. Construct a new federation from every loaded file's public exported
   identifier binders, retaining each fiber's descriptor.
3. Validate that federation with the ordinary ambiguity and disjointness rules;
   fail before rewriting or evaluating the body if construction is refuted or
   undecidable.
4. Use the validated federation as the synthesized anonymous-function domain.
5. Rewrite the `_FunctionBody` exactly once in the function rewrite environment
   associated with that domain.
6. Do not add the imported modules' public members or syntax rules directly;
   syntax rules become active only within the RHS of an explicit module scope
   operation such as `Numbers.(...)`.
7. Discard the import/function rewrite environment after the body.

An import therefore does not extend an executable block left-to-right. Its
qualified bindings are visible only in its explicit function body. Within an
ordinary map, rewriting remains ordinary map rewriting and must not invent
effects outside that operand.

Refactor the rewrite-scope callback so it distinguishes:

- imported binder federations and their module descriptors introduced for a
  synthesized import function; and
- rules introduced while entering the RHS of a scoped-access expression.

This should be one general scope-transition abstraction rather than separate
Std handling or a second syntax pass.

### Dependency discovery

Dependency discovery must follow the same scoped syntax visibility rules as the
real rewrite:

- entering `Std.(...)` makes Std's declared import syntax visible inside;
- leaving it removes that visibility;
- entering `with Std; Numbers do ...` makes the validated federation of their
  syntax rules and public members visible only in that function body;
- leaving a `'with` body discards its combined descriptors and rules;
- discovering an import records every path in its `List String` operand and
  makes the resulting exported binder federation and descriptors available
  while discovering its `_FunctionBody`, but does not perform a full source
  rewrite;
- leaving the import body removes those imported binder descriptors;
- each source is neutrally parsed once and fully rewritten once.

The discovery walk must understand import function-body boundaries. An import
expression nested in an ordinary literal map discovers its own dependencies but
must not expose them to sibling members.

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
function's actual return receiver. A `yield` beneath one or more module scopes
must still return from the current function activation, not from the nearest
module scope.

Evaluate `Import paths body` by desugaring it semantically into eager anonymous
function application:

1. Resolve every path and obtain each file's public exported binder federation.
2. Construct a new cross-file federation from those results using the ordinary
   federation operation.
3. If the cross-file federation is ambiguous, refuted, or insufficiently
   disjoint under the usual rules, return the established federation diagnostic
   without constructing or invoking the function.
4. Use the validated federation as one domain/argument value, containing such
   binders as `Numbers`, `Ordinals`, or multiple binders from a single file.
5. Construct an anonymous function with that domain and the supplied
   `FunctionBody`.
6. Immediately apply the function to the constructed domain value.
7. Return the eager invocation's result as the value of the import expression.

The import body's `yield` belongs to this synthesized function activation.
Closures created by the body retain only the imported binder fibers they
capture, exactly as they would retain ordinary function arguments. Multiple
paths and multiple exports from one path produce one federated domain and one
eager invocation, not nested bespoke import scopes.

This removes the current semantic exception in which an import-shaped surface
function is a no-op value and executable-scope machinery notices it out of band.
The new `datra.import` syntax adapter constructs a real, value-producing
`Import` expression. Evaluation of that expression performs the eager
anonymous-function call above and returns its result. Dependency discovery may
inspect the node to arrange module loading, but it must not be the mechanism
that gives the expression its runtime meaning.

The callable `datra.import` external must use the same implementation when
invoked through the `'import` function value: it accepts the path list and
function body, performs the eager invocation, and returns the body result. The
syntax adapter and direct function invocation must converge on one semantic
path; neither may retain the old empty-map/unit result.

Replace the old import representation:

```haskell
Import Bool String
```

with:

```haskell
Import [String] Expression
```

The expression is structurally required to be a `FunctionBody`. Change related
APIs from a single `(Bool, String)` request to a list of paths plus the retained
body, including dependency discovery, module loading, rendering, interpretation,
and test helpers. Remove the old executable-entry and left-to-right scope
mutation paths rather than preserving them beside eager function application.

## Standard-library changes

Replace the overloaded declaration:

```datra
'import :=
  ("import %("all") %Str" %
    ($all; Str -> ()) !~"datra.importAll") |
  ("import %Str" % (Str -> ()) !~"datra.import")
```

with a single value-producing import declaration:

```datra
_FunctionBody := !~"datra.FunctionBody"

'import :=
  "import %_Expr %_FunctionBody" %
    (List Str; _FunctionBody -> _Expr) !~"datra.import"

'with :=
  "with %_Expr %_FunctionBody" %
    (_Expr; _FunctionBody -> _Expr) !~"datra.with"
```

Place `_FunctionBody` with the other narrow syntax-category external types so
`std.datra` can use it in syntax templates. Place `'import` after `List` and
`Str` are available, or otherwise arrange equivalent forward visibility for its
signature. The `datra.import` adapter validates the `List Str`, extracts all
paths, preserves the matched `FunctionBody`, and constructs the new `Import`
node. It is not a surface no-op and no executable-scope callback may reinterpret
its result as an import instruction. No `import` spelling is added to neutral
parsing.

Update the callable external implementation of `datra.import` at the same time.
It must delegate to the same import-node/eager-function evaluator and return the
body's result, so calling the standard-library `'import` function cannot fall
back to the former empty-map/unit behavior.

The surface adapter collects the one-or-more path-string expression into the
`List Str` operand, so both `import "numbers" do ... yield ...` and
`import "numbers"; "ordinals" do ... yield ...` reach the same list-based
implementation.

The `datra.with` adapter validates the semicolon-separated module-value
expression, builds the descriptor-preserving federation, rejects ambiguity, and
lowers the result to the shared `ScopeAccess` implementation. It must preserve
the complete `_FunctionBody` and return `_Expr`. Direct invocation through the
standard-library `'with` function value must converge on the same semantics;
neither form may flatten the operands into a metadata-free map.

Replace `_AST` in every other `std.datra` syntax signature at the same time.
Inputs use the category named by their syntax holes, and outputs use the actual
node category returned by the adapter. Delete the leading `_AST` binding rather
than leaving it unused or private.

Remove:

- the `datra.importAll` syntax adapter;
- the `datra.importAll` external implementation;
- the import-kind Boolean and all branches controlled by it;
- `_AST`, `datra.AST`, `AnyAST`, and universal-AST subtype/coercion behavior;
- the old single-path/unit-return `datra.import` contract;
- the surface-no-op import result and its out-of-band executable-scope
  interpretation;
- executable-entry-only import validation and left-to-right import scope
  mutation;
- import-all collision behavior that can no longer be expressed;
- tests and diagnostics that exist only for importing every member directly.

Replace the old single-module-name and simple-export validation with validation
that the yielded value is a public identifier-binder federation. Accept multiple
simple binders and dependent binders. Remove assumptions and diagnostics that
require `yieldedIdentifier`, `declaredModuleName`, one simple namespace, or a
total map containing only simple identifier types. Domain construction must use
the ordinary federation operation so its established overlap, refutation, and
undecidable-disjointness diagnostics remain authoritative.

Module scope opening still validates the public named members of whichever
imported binder value appears on the LHS. That member validation is distinct
from, and must not reintroduce, a one-binder-per-file restriction.

## Source migration

1. Remove `_AST := !~"datra.AST"` from `libs/std.datra` and replace every
   `_AST` input or result in its syntax declarations with `_Expr`, `_Block`,
   `_IdenExp`, `_FunctionBody`, or another purpose-built narrow category.
2. Replace `libs/numbers.datra` with the module-scope form (and remove its
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
3. Wrap `libs/ordinals.datra` the same way.
4. Convert every fixture or library beginning with
   `Std.'import($all; "std")` into an explicit `Std.(...)` scope around the
   relevant executable body.
5. Replace every old entry-form `import "module"` or `import all "module"` with
   an import function body. Move the complete consumer region into that body,
   and use the module scope operator when unqualified members are wanted:

   ```datra
   import "library_one" do LibraryOne.(
     yield increment 4
   )
   ```

6. Combine adjacent imports into one list and one eager function call where they
   share a consumer region:

   ```datra
   import "numbers"; "ordinals" do
     -- Numbers and Ordinals are qualified bindings in this function body.
   yield (...)
   ```

7. Replace nested module scopes that intentionally open several modules for the
   same body with the direct form where clearer:

   ```datra
   with Std; Numbers do
     ...
   yield ...
   ```

8. Leave sources that require no standard names unwrapped.

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
- `_FunctionBody` is exposed as a narrow neutral syntax category without making
  `import` a neutral-parser keyword.
- `import "numbers" do ... yield ...` retains both the path list and complete
  function body in the import AST.
- `import "numbers" do Numbers.(... yield ...)` is captured as one complete
  `_FunctionBody`, including its module-scope-wrapped `yield`.
- multiple path strings parse as one import operand and one function body.
- canonical and surface import render/parse round trips preserve path order and
  the complete body.
- `with Std; Numbers do ... yield ...` retains both module operands and the
  complete `_FunctionBody`, while `with` remains standard-library-declared
  syntax rather than a neutral keyword.

### Syntax category typing

- `std.datra` contains no `_AST` binding or `_AST` signature operand.
- resolving `!~"datra.AST"` fails because the universal external type no longer
  exists.
- `AnyAST`, `astTypeValue`, and universal-AST subtyping are absent from the
  interpreter and type representation.
- `_Expr`, `_Block`, `_IdenExp`, and `_FunctionBody` accept only their matching
  captured structures.
- `datra.do` returns `_FunctionBody`; ordinary expression-producing adapters,
  including `datra.import` and `datra.with`, return `_Expr`.
- every standard syntax rule still rewrites with its narrowed signature.
- `_AST` remains available as an ordinary user identifier spelling when a user
  explicitly binds it; it has no built-in meaning.

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
- `with Std; Numbers do ... yield ...` exposes both modules' public members and
  syntax rules only within its body.
- an ambiguous `'with` federation fails before its body is rewritten or
  evaluated, with no left-to-right winner.
- a function `yield` beneath a module scope reaches the true function boundary.
- closures created inside the RHS retain the opened values they actually use.

### Ordinary maps

- `Std.(a := 1; b := 2)` returns the same named map as `(a := 1; b := 2)`.
- ordinary map assignments do not become declarations visible to sibling map
  members.
- an import expression nested in a map eagerly evaluates only its own function
  body and does not expose qualified bindings to sibling members.

### Imports and modules

- imports bind only the public identifier binders yielded by their modules; they
  do not open the members inside those binder values.
- a one-path, one-binder import constructs a domain containing that qualified
  value and eagerly invokes its anonymous function exactly once.
- a file yielding `(Numbers1 := ...; Numbers2 := ...)` contributes both binders
  to the same synthesized function domain.
- dependent identifier binders are accepted and routed by the ordinary
  federation rules.
- overlapping or insufficiently disjoint simple/dependent export fibers produce
  the existing federation ambiguity diagnostic rather than an arbitrary import
  choice.
- a multi-path import constructs one combined domain and still performs one
  eager invocation.
- a multi-path import explicitly constructs a new cross-file federation before
  function construction; an ambiguous federation fails before invocation.
- `import "numbers" do Numbers.(... yield ...)` composes import-function scope
  with module scope, and the nested `yield` returns from the synthesized import
  function.
- an import affects only its explicit `FunctionBody`; earlier and later sibling
  expressions retain their original scope.
- the import expression returns its eager function invocation's result rather
  than a no-op/unit marker.
- no executable-scope callback interprets a surface no-op as an import.
- imports inside a module-scope RHS do not escape their own function bodies or
  that RHS.
- transitive imports and cycle diagnostics remain correct.
- repeated paths in one import operand are idempotent.
- every imported binder retains its originating module descriptor and associated
  exported syntax rules.
- exported syntax rules become active only through an explicit module scope
  such as `Numbers.(...)` inside the import body.
- closures returned by an import body retain captured imported binders through
  ordinary function closure behavior.
- Std does not import or open itself.

### Type interactions

Cover opened values and syntax through:

- optional names;
- simple and dependent identifier binder federations;
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
3. Add the narrow `_FunctionBody` category, replace every `_AST` use with a
   specific syntax category, then remove `_AST`, `datra.AST`, `AnyAST`, its
   external resolver, and universal-AST subtyping.
4. Introduce the shared path-identity module descriptor and move the public
   exported binder federation plus syntax rules onto it without assuming one
   namespace per file.
5. Teach syntax rewriting and dependency discovery to enter and leave scoped
   rule environments for `ScopeAccess`.
6. Implement interpreter evaluation with an explicit child scope and verify
   handoff behavior.
7. Change `'import` to accept `List Str` plus a function body, replace the
   no-op/entry-form import with a value-producing import AST, federate all simple
   or dependent exports across all requested files into one validated domain,
   fail on federation ambiguity, and evaluate it as one eager anonymous function
   application.
8. Add the standard-library `'with` function and syntax adapter, preserving
   module descriptors while lowering its validated multi-module federation to
   the shared `ScopeAccess` machinery.
9. Remove `import all`, the import-kind Boolean, and out-of-band executable-scope
   import handling from the AST, standard library, loader, and interpreter.
10. Implement the implicit Std scope at executable source boundaries.
11. Migrate bundled libraries and fixtures.
12. Run focused parser, syntax-category, scope, module, numbers, ordinals,
    closure, specification, and subfederation tests.
13. Run `git diff --check`, build with LiquidHaskell disabled, and run the full
    test suite once with `-f-liquid`.

## Acceptance criteria

The change is complete when:

- no `import all` syntax or `datra.importAll` implementation remains;
- no import-kind Boolean remains in the AST or module-loading APIs;
- `_AST`, `datra.AST`, `AnyAST`, `astTypeValue`, and universal-AST subtype or
  coercion behavior no longer exist;
- every syntax template and control adapter uses a specific input and output
  category, with no universal replacement for `_AST`;
- `_Expr`, `_Block`, `_IdenExp`, and `_FunctionBody` reject structurally
  mismatched captures at their typed boundary;
- `_FunctionBody` is exposed to `std.datra` without recognizing `import` or
  `with` in the neutral parser;
- `'import` accepts a `List Str` and `_FunctionBody`, constructs a real import
  AST expression, and never produces a surface no-op instruction;
- each import creates one anonymous function whose domain contains all requested
  exported identifier binders, eagerly invokes it, and returns its result;
- every multi-file import first constructs one new federation from the files'
  exported binder federations and fails before body rewriting or invocation if
  that combination is ambiguous;
- a single imported file may contribute multiple simple identifier binders;
- dependent identifier exports are accepted, and all cross-file and within-file
  ambiguity is decided by the ordinary federation rules;
- module identity and caching use the source path rather than a required single
  exported namespace;
- `import "numbers" do Numbers.(... yield ...)` parses and evaluates with the
  nested `yield` returning from that eager anonymous function;
- import scope is exactly the synthesized function body and uses ordinary
  function activation, closure, `yield`, and handoff behavior;
- executable scopes contain no out-of-band import interception or left-to-right
  import mutation;
- `'with` is declared in `std.datra`, accepts several module values plus a
  `_FunctionBody`, and lowers to the shared module-scope implementation;
- `with Std; Numbers do ...` opens the validated federation of both modules'
  public members and syntax rules for exactly its body;
- an ambiguous `'with` federation produces the ordinary federation diagnostic
  without choosing a module by source order;
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
- modules use qualified imports plus the explicit module scope operator or
  `'with` for a validated multi-module scope;
- Std has no self-import or self-opening path;
- syntax rewriting and dependency discovery do not duplicate full rewrites;
- module descriptors and syntax rules are cached and reused;
- all focused regressions and the complete non-Liquid test suite pass.
