# Replace the external operator with the `'datra` host value

## Purpose

Remove the `~~` source operator and expose the Haskell implementation boundary
through an ordinary Datra value named `'datra`.

The standard library is the only bootstrap consumer of a host-introduced
`'datra`. It republishes that exact value with:

```datra
'datra := 'datra
```

Consequently, importing `Std` makes the bridge available through normal module
semantics. A default import exposes `'datra`; a qualified import exposes
`Std.'datra`. No program-level loader should inject a second implicit binding.

Host capabilities use normal scope access:

```datra
'datra.begin
'datra.Any
'datra.ordinal.sum
```

Thus every current occurrence such as `~~"datra.begin"` becomes
`'datra.begin`. There is no compatibility spelling for `~~`, and structured
external descriptors such as
`~~(backend:"haskell";symbol:"datra.add")` are removed rather than translated.

## Required semantics

### `'datra` is an ordinary Datra value

The bridge is a total named map built with the same evaluated assignment and
Atlas-map constructors used for Datra-defined values. Its top-level shape is:

```text
'datra
├── Any, never, Ordinal, Char, Template, SyntaxTemplate
├── Expr, IdenExp, Block, FunctionBody
├── NatRange, IntRange, NatValRange, IntValRange
├── public, len, from, range, add, abs
├── let, assert, assertHard, begin, do, fun, if, ifThen
├── import, with, in, modular, of, and, or, not
└── ordinal
    ├── sum, prod, minus, exp
    └── lt, lte, gt, gte
```

Each field is an ordinary named member. The `ordinal` field is itself an
ordinary named map, so arbitrary-depth access continues to use existing
`ScopeAccess` evaluation. The bridge must not add a special AST node for a host
lookup, a magic rule for each dotted symbol, or a general string-to-Haskell
dispatch function.

Construct named fields through the existing identifier-assignment semantics and
combine them with the existing map constructors. This ensures that access,
canonical rendering, specification, subfederation, scope opening, privacy, and
module export all see the same value shape as they do for Datra-authored maps.

### Host hooks have typed identities

Replace dotted string symbols with an internal Haskell hook identity. One
closed sum type should cover runtime hooks and syntax-control hooks; a tree of
named bridge members maps Datra paths to those identities. Rendering a path is
presentation only, not lookup policy.

Runtime hooks are `InterpretedValue` functions or meta-types. Function values
retain their hook identity so an unlinked implementation can be refined by a
source-declared signature. Rename metadata such as `functionExternalSymbol` to
describe this host-hook role.

Syntax-control hooks are also represented as bridge members, but their
implementation consumes unevaluated syntax captures. They must remain
non-callable at the ordinary runtime boundary. The syntax rewriter recognizes
a bridge access structurally, retrieves its typed hook identity, and applies
the registered `SyntaxFunctionBody`. It must never recover a hook by rendering
an arbitrary expression and comparing strings.

The following division remains explicit:

- runtime hooks implement values such as `Any`, `len`, `from`, and ordinal
  arithmetic;
- syntax hooks expand captures into AST such as `Begin`, `FunctionBody`,
  `Conditional`, `Import`, and `Subfederation`; and
- the Datra declarations in `std.datra` continue to own public names,
  signatures, syntax templates, and export policy.

### Function implementation attachment is narrow

A bridge member may follow an explicit function or syntax-function signature
in the same position currently occupied by the external operator:

```datra
{x? : OrdValue; y? : OrdValue} -> OrdValue 'datra.ordinal.sum
"begin %_Block yield %_Expr" % (_Block; _Expr -> _Expr) 'datra.begin
```

The neutral parser should recognize only a complete access rooted at the
bootstrap identifier `'datra` in this implementation position. The member path
itself remains the existing `IdentifierReference` plus `ScopeAccess` AST; the
parser does not validate individual hook names. Unknown members therefore fail
through ordinary identifier/scope access rather than through an external-symbol
error.

Do not retain the inferred form `Nat ~~"symbol"`. A host implementation must
either have an explicit function signature or already be a complete function
value that can be aliased, as in:

```datra
public := 'datra.public
```

A leading bridge access remains a standalone ordinary expression, and direct
syntax-hook application such as the bootstrap use of `'datra.begin` is handled
by the shared syntax-hook recognizer.

### `Std` owns propagation

Seed `'datra` only in the base scope used to evaluate the module whose identity
is `std.datra`. Both the embedded standard-module path and an explicitly loaded
`std.datra` module must use that same bootstrap function.

Within the `Std` declaration block, add `'datra := 'datra`. The declaration's
captured right-hand scope resolves the host seed, while the apostrophe naming
policy requires the new binding to denote the same value. Because apostrophe
names are public, the existing `public modular this` result exports it without
changes to `public`, `modular`, module loading, or import-all behavior.

The standard module's exported value is then the only route by which other
modules receive the bridge:

- `AllStandardLibrary` opens the exported `'datra` member;
- `QualifiedStandardLibrary` makes it available as `Std.'datra` and through a
  `Std.(...)` scope; and
- `NoStandardLibrary` has no `'datra` binding unless a program imports `Std`
  explicitly.

This restriction prevents closed evaluation and unrelated root scopes from
silently acquiring host authority.

## Implementation plan

### 1. Introduce the host-hook model and bridge builder

Create one application-layer module for the host bridge rather than leaving
registries split between `Interpreting.hs` and `SyntaxDefinitions.hs`. It should
own:

- the typed hook identity and its path segments;
- the nested capability tree;
- construction of the evaluated `'datra` map;
- construction of unlinked runtime-function hook values;
- lookup of syntax-control bodies by typed identity; and
- structural recognition of a `'datra` access expression.

Keep hook implementations in their focused modules where useful, but require
the bridge module to be the single inventory. Building the nested map should
detect duplicate sibling names and reject a runtime/syntax classification
mismatch during Haskell construction, rather than relying on source tests to
notice an unreachable hook.

Move `syntaxFunctionBodyForSymbol` away from dotted strings. The new lookup
takes a typed hook. Consolidate `registeredExternal` into the same inventory,
and replace `resolveExternal` with direct bridge construction or typed hook
resolution. `backend` and `symbol` descriptor parsing has no successor.

Refactor internal helper signatures so they consume evaluated host values
directly when possible. Where an AST expression is genuinely required, use the
structural `'datra.<member>` expression and ensure it is evaluated only in a
scope that owns the standard-library bridge; do not create a private external
AST escape solely for Haskell-generated expressions.

### 2. Bootstrap `std.datra` through the host value

Add a helper which extends a module base scope with:

```text
"'datra" -> EvaluatedBinding datraHostValue
```

Call it exactly when evaluating `std.datra`, identified by the existing
standard-library filename logic. Apply it in the shared module-evaluation path
so the cached embedded standard library and a normally imported standard
library cannot diverge.

Update `libs/std.datra` as one coherent change:

1. replace every `~~"datra.*"` with the corresponding `'datra.*` access;
2. add `'datra := 'datra` inside the `Std` block before its value is exported;
3. retain private names such as `_Expr` and all source-declared signatures;
4. keep `public modular this` responsible for the export set; and
5. leave all public surface syntax owned by the existing declarations.

Update `libs/ordinals.datra` to use the nested
`'datra.ordinal.{sum,prod,minus,exp,lt,lte,gt,gte}` members. It must obtain
`'datra` from `Std`, demonstrating that optional libraries need no bootstrap
injection of their own.

### 3. Replace external parsing with bridge implementation attachment

In `Parsing.hs`:

- remove `externalExpression`, `externalTermAtom`, the `~~` prefix path, and
  external-specific incomplete-prefix handling;
- parse `'datra.begin` solely through the existing identifier and scope-access
  grammar;
- replace `attachExplicitExternalImplementation` with an attachment step for a
  structurally complete `'datra` access after an explicit function or syntax
  signature; and
- keep standalone and leading bridge accesses as ordinary expressions.

In `SyntaxRewriting.hs` and `SyntaxDefinitions.hs`:

- replace `externalSymbol` with the shared structural hook recognizer;
- replace external-only function-body and inferred-body cases with explicit
  bridge-hook cases;
- remove inferred external implementation attachment;
- use typed syntax-hook identities for direct control expansion and rule
  adapters; and
- retain the existing post-expansion normalization for control forms.

The structural recognizer should accept the canonical nested access shape and
parentheses that normalize to that shape. It should reject computed access,
map indexing, aliases, and arbitrary roots at bootstrap time. Aliases remain
valid at runtime because they denote ordinary function values, but they are not
a way to introduce a new compile-time AST adapter.

### 4. Link signatures by value capability

In `Interpreting.hs`, replace tests of `External {}` in specification and
function construction with tests of the evaluated source value's host-hook
capability.

An explicit signature followed by a runtime hook should:

1. evaluate the bridge member through normal scope access;
2. evaluate the source-declared signature;
3. link the hook's preparation/invocation behavior to that exact domain and
   codomain; and
4. preserve the hook identity and canonical source path on the resulting
   function.

A syntax hook followed by a syntax-function signature should similarly retain
the syntax template metadata while leaving AST-capture execution to the syntax
rewriter. Ordinary specification must remain the fallback for values without a
host-hook capability. This makes the special behavior a property of the value,
not of a removed AST constructor.

Recursive-function seeding and trailing-function-body detection should use the
same capability predicate. Do not introduce parallel predicates for parser,
rewriter, evaluator, and recursion; expose one structural AST recognizer and
one evaluated-value capability query.

### 5. Remove `External` from the language model

Delete the construct across the public AST and operator layers:

- `External` from `Expression`;
- `ExternalValue` from `OperatorExpression`;
- `ExternalOperator` and its `~~` spellings;
- normalization, traversal, lowering, pretty-printing, and source-rendering
  cases; and
- generators and AST round-trip fixtures for external expressions.

Canonical strings for host meta-types and host-backed functions must use
`'datra` access paths. In particular, update the hard-coded canonical forms in
`DatraTypes/Evaluation/Value.hs`, function-source metadata, serialized closure
expectations, and any AST fixture output that currently contains `~~`.

Remove `ExternalFailure`, `ExternalEvaluationFailed`, descriptor diagnostics,
and their English and Romanian messages once no caller remains. If an escaped
syntax hook reaches ordinary application, report a focused function failure
stating that the host syntax hook requires unevaluated captures; this is a
runtime misuse of a real value, not an external-descriptor error.

Finish with a repository-wide `~~` scan. The only permissible occurrences are
tests asserting that the removed token is rejected and, if needed, prose in
this plan. Production Datra, Haskell source, canonical output, and fixtures
must contain none.

## Test plan

### Bridge structure and access

Add focused interpreter tests proving:

- default `Std` visibility resolves `'datra.Any`, `'datra.begin`, and
  `'datra.ordinal.sum`;
- qualified visibility resolves `Std.'datra.Any` and
  `Std.('datra.ordinal.sum)` without opening `'datra` globally;
- explicitly importing `Std` provides the same value;
- `NoStandardLibrary` rejects an unimported `'datra` with
  `UnknownIdentifier`; and
- `'datra.missing` fails as an ordinary missing member, with no registry-string
  diagnostic.

Inspect the exported `Std` map to confirm that `'datra` is public, `_Expr` and
the other private helpers remain private, and the exported bridge is
semantically equal to the bootstrap seed. Add a shadowing test showing that a
different later value cannot replace `'datra`, while rebinding it to itself is
accepted.

### Runtime hooks

Migrate each external function test to its bridge path. Cover standalone
aliasing, explicit signature linking, ordinary calls, named and positional
arguments, nested ordinal hooks, function closure serialization, and canonical
render/parse round trips.

For specification and subfederation, cover both host types and functions:

```datra
'datra.Expr of Any
('datra.add ~> ({a? : Int; b? : Int} -> Int)) of
  ({a? : Nat; b? : Nat} -> Int)
```

Include positive and negative cases so linking cannot bypass contravariant
function inputs, covariant outputs, or the shared Datra type-family decision
procedures. Exercise optional names explicitly: a hook signature with `a?` and
`b?` must accept positional or matching named arguments but must continue to
reject an incompatible required/private-name shape.

### Syntax hooks

Run the existing standard-syntax suite after converting declarations and
expectations to `'datra`. In particular, retain coverage for:

- direct `'datra.begin` bootstrap expansion;
- block and function-body captures for `begin` and `do`;
- lazy branch behavior for `if`, `and`, and `or`;
- hard and soft assertions;
- `import` and `with` scope construction;
- `of` using the normal subfederation decision procedure;
- optional-name syntax parameters; and
- qualified calls such as `Std.(if ...)`.

Add a failure case for ordinary runtime invocation of an escaped syntax hook,
and prove that an alias cannot be mistaken for a compile-time adapter. These
tests keep AST-capture authority confined to the structural `'datra` bridge
path.

### Parser and removal coverage

Update parser tests to establish that:

- `'datra.begin` is an ordinary nested scope access;
- a complete bridge access attaches after an explicit function or syntax
  signature;
- the same expression remains standalone at an expression boundary;
- arbitrary scope access does not acquire implementation semantics;
- `~~"datra.Any"`, structured descriptors, a bare `~~`, and legacy external
  spellings are rejected; and
- AST and source-rendering round trips contain no external node.

Keep the existing whole-`std.datra` neutral parse and syntax-admissibility
checks. They are the main guard against changing attachment precedence while
rewriting every standard declaration.

## Delivery sequence

Implement in vertical slices so each stage has a focused validation target:

1. add typed hook identities, the nested bridge builder, and direct unit tests;
2. teach syntax discovery and evaluation to consume bridge hook capabilities;
3. seed and re-export `'datra` from `Std`, then migrate `std.datra` and
   `ordinals.datra`;
4. replace parser attachment and canonical rendering;
5. delete the external AST, descriptor machinery, diagnostics, and obsolete
   tests; and
6. run focused parsing, standard-library, function, module, closure, and CLI
   tests, followed by the full suite once with LiquidHaskell disabled as the
   repository guidance requires.

## Completion criteria

The work is complete when all of the following hold:

- `~~` is not a recognized Datra token and no external AST constructor exists;
- `std.datra` evaluates from one host-introduced `'datra` value;
- `Std` exports `'datra` through the ordinary declaration and module pipeline;
- every shipped Haskell hook is reachable at exactly one typed bridge path;
- `ordinals.datra` receives its hooks through `Std`, without host injection;
- syntax hooks still receive unevaluated captures and runtime hooks retain their
  declared signature checks;
- canonical source and serialized closures use `'datra` paths and round-trip;
- optional names, specification, and subfederation behave identically for
  bridge values and Datra-authored values; and
- focused and full test suites pass without restoring string descriptors or a
  second implicit program-level bridge.
