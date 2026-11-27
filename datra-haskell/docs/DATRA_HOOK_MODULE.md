# `datra` Bootstrap and Native Capability Design

## Status

The old singleton `datra` hook is removed from the active evaluator.

`app/DatraHost.hs` remains as an inert placeholder for a future typed native
capability boundary. It:

- exports no value;
- constructs no AST;
- constructs no host namespace map;
- creates no runtime singleton declaration; and
- is not imported or installed by `Evaluation.Expression`.

There is no `installDatraHost` path. Standard-library parsing, rewriting, and
module preparation begin from an empty root scope. Consequently the bundled
standard library is not currently bootstrappable; this is intentional while
the replacement design is unresolved.

The general `RuntimeSingletonPayload` and
`ScopedRuntimeSingletonDeclaration` types remain because they also represent
ordinary evaluated bindings, captures, contextual values, and retained module
members. They no longer provide a privileged `datra` namespace.

## Ownership boundary

Public `datra.*` members must eventually be ordinary dependent declarations.
Haskell may supply narrow typed capabilities required by those declarations,
but it must not construct a parallel namespace or declaration system.

The declaration layer owns:

- heads and capture matching;
- modifiers;
- type checking;
- overlap handling;
- specification and subfederation behavior;
- public scope and import precedence; and
- presentation derived from retained semantic evidence.

The native boundary owns only behavior which cannot be expressed in Datra. It
must accept and return typed semantic values owned by the relevant subsystem.
Parser nodes, rewriter nodes, and arbitrary `Expression` values do not cross
that boundary.

Evaluation also no longer normalizes an AST a second time or reconstructs an
AST by rendering, parsing, and rewriting an evaluated value. Syntax rewriting
owns normalization; retained declarations and typed semantic evidence must
carry what later phases need.

Evaluation and closure rewriting also do not resolve standard-library names
such as `Str` or `Maybe` to implement intrinsic name-family or optional syntax
rules. Those rules require structural capabilities owned by their semantic
subsystems.

## Proposed bootstrap shape

A bundled `libs/datra.datra` declaration layer remains the leading design:

```text
private typed Haskell capabilities
               |
               v
prepare canonical libs/datra.datra
               |
               v
PreparedModule containing ordinary datra declarations
               |
               v
prepare canonical libs/std.datra
               |
               v
Std exports its ordinary datra declaration
```

The private provider exists only while the canonical `datra` source is being
prepared. The resulting declaration is then installed through the same
`PreparedModule` and declaration-layer path as every other module.

Source evaluated with `NoStandardLibrary` must have no `datra` binding unless
an explicit source module supplies one. Private capability identities and
bootstrap scopes must not leak into the final `Std` module or caller scopes.

## The `begin` constraint

`libs/std.datra` currently starts by calling `datra.begin` before the surface
block declarations exist. A value of `FunctionBodyAST` is not callable until a
signature supplies its domain and codomain. The replacement bootstrap must
therefore establish the initial callable block operation without relying on
the complete declaration surface it is bootstrapping.

This constraint must be solved by the bootstrap grammar or staging design. It
must not be bypassed by installing a host atlas map named `datra`.

## Required design work

Before `DatraHost` becomes active again, the design must specify:

1. a cycle-free minimal grammar for `libs/datra.datra`;
2. an explicit module identity distinguishing canonical bundled sources from
   private capability providers;
3. an unforgeable typed reference from a source declaration to one native
   capability;
4. the phase which resolves and invokes each capability;
5. how closure, scope, and capture evidence cross that invocation;
6. how callable bootstrap operations receive signatures;
7. how structural insertion and preimage evidence is retained where required;
   and
8. how the prepared declaration layer is installed without reconstructing a
   namespace value.

`DatraHost` should then expose typed capabilities only. It must not regain a
`datraHostValue`, an AST-based function source, a `hostMap`, or any helper that
injects a singleton declaration directly into a scope.

## Current verification boundary

The production library and executable must compile with `DatraHost` inert.
Interpreter tests which require the old `datra` singleton or completed `val`
injectivity remain historical expectations until the replacement architecture
is implemented; this cleanup does not rewrite them to bless the temporary
unavailable state.
