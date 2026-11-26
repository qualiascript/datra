# `datra` Bootstrap and Native Capability Design

## Status

This document defines the boundary between work whose direction is settled and
work that still requires architectural design.

The settled direction is:

- public `datra.*` members are ordinary dependent declarations;
- Haskell supplies only narrow, typed capabilities required by those
  declarations;
- syntax representations remain private to the language subsystem that owns
  them;
- bootstrap authority belongs to canonical bundled sources rather than a file
  basename; and
- prepared modules are installed through ordinary retained declaration layers.

A bundled `libs/datra.datra` module is the leading proposal for the declaration
layer between Haskell capabilities and `libs/std.datra`. Its bootstrap grammar,
capability reference mechanism, and exact public declarations remain open
design work.

## The `begin` bootstrap constraint

`libs/std.datra` currently begins by calling `datra.begin` twice:

```datra
(datra.begin (()
  Std := datra.begin ((
    ...
  )
  public this))
)
```

Both calls require a callable operation before `_Block`, `_Expr`, and the
surface `begin` declaration exist.

A value of `functionBodyType` is not a callable function. It has no domain or
codomain until a signature is applied. Consequently, a `begin_body` value
cannot occupy these call sites by itself. The bootstrap design must provide a
callable block operation and must establish its signature before either call is
rewritten.

This constraint is part of the broader design. The final design may expose
`begin`, `begin_body`, both, or a different bootstrap form, but the name and
classification must follow from the chosen staging model.

## Settled architecture

### Ordinary dependent declarations

Native-backed and source-backed members use the same dependent declaration
representation and the same:

- head and capture matching;
- overlap handling;
- type checking;
- optional-name behavior;
- specification and subfederation behavior;
- protection and presentation;
- import precedence; and
- public-scope retention.

The declaration owns its head, modifiers, captures, implementation, public
scope, and evaluated cache. A Haskell capability supplies implementation
behavior without defining a second declaration model.

### Typed capability boundary

Each Haskell capability accepts and returns typed semantic values owned by the
relevant subsystem. Dependent declaration, block, function-body, conditional,
function, and scoped-evaluation representations remain opaque across this
boundary.

The boundary preserves:

- lexical scope and capture state;
- declaration order and visibility;
- optional names;
- specification and subfederation evidence;
- insertion and preimage capability where semantically required; and
- structured failures for the phase that invokes the capability.

Raw parser and rewriter nodes do not cross the capability boundary. Syntax
category labels such as `FunctionBodyAST` classify Datra values; they do not
expose their Haskell representation.

### Prepared module installation

`installPreparedModule` remains the installation boundary. Every prepared
bootstrap or standard module retains an ordinary declaration layer.
Installation pushes that retained layer without rebuilding a namespace value,
rematerializing declarations, or reevaluating unrelated members.

### Explicit module identity

Module identity distinguishes canonical source modules from private built-in
capability providers, for example:

```haskell
data ModuleIdentity
  = SourceModuleIdentity FilePath
  | BuiltinModuleIdentity BuiltinModuleName
```

The exact representation may vary. It must provide stable identity, ordinary
prepared-module deduplication, and unambiguous diagnostics.

If `libs/datra.datra` is adopted, it has a canonical bundled source identity
distinct from the private capability provider used while preparing it.

### Bootstrap authority and visibility

The trusted bundled-source loader is the only authority that exposes private
Haskell capabilities. Authority is determined by canonical source identity.

The private provider exists only while the canonical declaration layer is
prepared. The resulting `datra` declaration is then available while
`libs/std.datra` is prepared. `Std` retains its own ordinary `datra`
declaration, and caller scopes obtain it through normal qualified or open
standard-library imports.

Source evaluated with `NoStandardLibrary` has no `datra` binding unless an
explicit module supplies one. Private capability identities and bootstrap
scopes are absent from the final prepared `Std` module and caller scope.

## Proposed `datra.datra` layer

The leading bootstrap structure is:

```text
private typed Haskell capabilities
               │
               ▼
prepare canonical libs/datra.datra
               │
               ▼
PreparedModule containing ordinary datra declarations
               │
               ▼
prepare canonical libs/std.datra
               │
               ▼
Std exports its ordinary datra declaration
```

Under this proposal, `libs/datra.datra` owns:

- dependent declaration heads and function signatures;
- public `datra.*` names;
- `def`, `val`, and other declaration modifiers;
- the distinction between a function body and a callable function;
- composition of smaller capabilities into public operations; and
- the public namespace made available to `Std`.

Haskell owns:

- capabilities that cannot be expressed in Datra;
- typed implementation state and evaluator access;
- representation invariants of opaque semantic values; and
- bidirectional insertion behavior intrinsic to a capability.

This proposal becomes an implementation plan only after the open design
questions below have precise answers.

## Open design questions

### Bootstrap grammar for `datra.datra`

`datra.datra` cannot depend on the complete declaration and syntax surface it
defines. Its preparation needs a cycle-free minimal grammar or staging layer.
That layer must be sufficient to declare the `datra` namespace, attach typed
capabilities, and produce the resource consumed by `PreparedModule`.

### Source reference to Haskell capabilities

Selected declarations need a structural, typed, and unforgeable reference to a
Haskell capability. The design must specify:

- the representation of capability identity;
- how a declaration receives that identity;
- which phase resolves it;
- how its input and output types are checked;
- how bidirectional behavior is retained; and
- why ordinary source cannot access or forge it.

### Callable bootstrap block operation

The staging model must establish how the initial block applications are
rewritten. The possibilities include a block form in the minimal grammar, an
early callable dependent declaration, or another core resource representation.

The choice determines the final classification and name of the block
capability. It also determines where `_Block` and `_Expr` first become
available for signature checking.

### Semantic values at the native boundary

Each syntax-facing behavior needs an opaque typed interface. The design must
decide whether that interface is:

- an operation over existing `InterpretedValue` forms;
- a new semantic value owned by the relevant subsystem; or
- a phase-owned evaluator capability used during declaration invocation.

The answer may differ by behavior. A single universal syntax capability is not
required.

### Classification of each public operation

Each public operation must be classified independently as a value, function
body, callable function, dependent declaration, or phase-owned capability.
Names ending in `_body` are appropriate only for values that actually require
a signature to become callable.

`parse_natural`, `from`, and range behavior have meaningful bidirectional body
capabilities. Their classification does not determine the classification of
block, conditional, function, or scoped-evaluation behavior.

### Phase ownership

For each capability, the design must identify one owning phase among parsing,
syntax rewriting, declaration preparation, and evaluation. Its contract must
state which typed values, scope, and capture evidence are available in that
phase and how failures are reported.

## Required behavior contracts

These observable semantics are fixed even though their exported names and
native interfaces are not.

| Behavior | Required semantics | Open design work |
| --- | --- | --- |
| `let` modifier | Normalize an assigned dependent declaration, apply only `let`, and preserve its optional name, head, captures, implementation, specification, and subfederation behavior. | Define the opaque declaration operation and its owning phase. |
| `def` modifier | Normalize an assigned dependent declaration, apply only `def`, and preserve all unrelated declaration semantics, including recursive definition behavior. | Define the opaque declaration operation and definition-scope ownership. |
| `val` modifier | Normalize an assigned dependent declaration, apply only `val`, and retain the required injectivity evidence. | Define the declaration and injectivity operation. |
| block expression | Execute declarations in source order and block scope, then yield the result; preserve empty and singleton-entry behavior. | Define the bootstrap form, callable declaration, and semantic block interface. |
| function body | Retain declarations, result, lexical scope, and deferred invocation behavior. | Define construction and closure capture. |
| function expression | Produce ordinary function behavior from its body expression and preserve lexical capture. | Define whether source composition or a Haskell capability owns construction. |
| conditional | Evaluate only the selected branch and use the ordinary empty result when the else branch is absent. | Define lazy branch values and phase ownership. |
| scoped evaluation | Open module operands in order, evaluate a body with ordinary import precedence, and end the opened scope afterward. | Define the prepared-module/body interface and scope-lifetime capability. |

Natural-literal conversion is total for values admitted by the
`_NaturalLiteral -> Nat` signature. It recovers the retained `Nat` witness and
does not parse an arbitrary string. Its final declaration name and whether it
is exposed as a body are determined with the rest of the declaration layer.

Boolean, ordinal, length, subfederation, range, and other native operations
receive the same declaration-layer audit. Stable value-level operations retain
their semantics while their declaration ownership and namespace move.

## Certain cleanup work

The following outcomes are required independently of the open design choices:

1. `PreparedModule` uses explicit source and built-in identities.
2. Trusted bootstrap loading uses canonical source identities in one loader
   boundary.
3. `moduleBaseScope` no longer grants capability access by basename.
4. Bootstrap and standard modules install retained dependent declaration
   layers through `installPreparedModule`.
5. Public `datra.*` names, signatures, modifiers, and scopes belong to ordinary
   dependent declarations.
6. Stable constants, types, Boolean and ordinal operations, range behavior,
   and other value-level capabilities move out of the current host namespace
   without semantic changes.
7. The current host namespace, runtime-singleton declaration path, and parallel
   runtime payload representation are removed after the replacement module
   supplies all required members.
8. Private capability values and bootstrap scopes are absent from the prepared
   `Std` module and caller scopes.

Items 6 and 7 depend on a working replacement declaration layer. The other
items may be developed independently when they do not change bootstrap
behavior.

## Design-dependent work

The following work begins only after the corresponding open questions are
resolved:

- creating `libs/datra.datra`;
- changing the initial `std.datra` block form;
- choosing `begin` or `begin_body` as a public declaration;
- defining the source syntax or preparation API for capability references;
- classifying each syntax-facing operation;
- implementing opaque semantic interfaces for those operations; and
- moving syntax-facing behavior into the new declaration layer.

The design is implementation-ready when it provides:

1. a cycle-free preparation sequence for `datra.datra` and `std.datra`;
2. typed, unforgeable capability references;
3. an explicit classification and owning phase for every operation;
4. representation-hiding semantic interfaces;
5. scope, capture, optional-name, specification, and subfederation behavior for
   every syntax-facing operation; and
6. exact failure and diagnostic behavior at each boundary.

## Verification

### Cleanup verification

- unrelated files named `datra.datra` or `std.datra` receive no bootstrap
  authority;
- `NoStandardLibrary` source cannot resolve private capabilities or the
  standard `datra` declaration;
- qualified and open modes expose `Std.datra` and `datra` through ordinary
  declaration imports;
- native-backed and source-backed declarations share lookup, capture,
  overlap, protection, and import behavior;
- private capability identities and scopes are absent from the prepared
  standard module and caller scopes;
- prepared modules install by retained layer reuse; and
- standard-library preparation does not reevaluate unrelated native
  declarations.

### Behavior verification

- bootstrap preparation never treats a function body as a callable function;
- modifier behavior preserves optional names, specification, and
  subfederation;
- block and function-body behavior preserves entry order, lexical scope,
  declaration visibility, empty entries, and result behavior;
- function construction preserves lexical capture;
- conditional behavior evaluates only the selected branch;
- scoped evaluation preserves module order, import precedence, and scope
  lifetime;
- natural-literal conversion is total for `_NaturalLiteral` and retains its
  inverse; and
- native capability implementations operate only through their typed semantic
  interfaces.

Exact test locations and declaration names depend on the completed design.

## Completion criteria

The design phase is complete when the open questions have one coherent,
cycle-free answer and the `datra.datra` proposal is either specified precisely
or replaced by an equally explicit declaration layer.

The implementation is complete when canonical bootstrap preparation produces
an ordinary `datra` module, `Std` exports it through ordinary dependent
declarations, every native capability uses a typed representation-hiding
boundary, and the current host namespace and runtime-singleton declaration
path are no longer needed.
