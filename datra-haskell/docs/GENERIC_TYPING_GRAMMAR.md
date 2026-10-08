# Generic Typing and Scope Protection

Status: implementation specification.

## Purpose

Generic typing adds dependent product and dependent sum binders to function
domains:

```datra
&_T :: Number
^T :: Any
```

Both forms become real prefix members of the domain map. They are not virtual
metadata and they are not erased before the function body runs.

The two polarities differ in how their values may be observed:

- `&` introduces a product value. A product that does not depend on a sum is
  ordinary and may participate in the codomain.
- `^` introduces a sum value whose concrete representation is available only
  in the dynamic scopes authorized to observe it.
- An `&` value that transitively depends on a `^` value has the same protected
  observation behavior as that `^` value.

Scope protection is a general evaluator property. Any operation involving a
protected value produces a protected result. It is not implemented as a list
of special cases for aliasing, conditionals, functions, or individual
operators.

## Surface grammar

Conceptually:

```text
generic-introduction := generic-polarity identifier-expression generic-bound?
generic-polarity     := "&" | "^"
generic-bound        := "::" expression
```

The bound defaults to `Any` when `::` is omitted.

Examples:

```datra
&_T
&T :: IntLimit
&(T?) :: Any

^_T
^T :: Number
^(T?) :: Any
```

Parentheses may delimit an identifier expression or the complete introduction
where ordinary precedence requires them:

```datra
Args (&_T :: IntLimit)
(a : T; b : &(T?))
```

The parser must use the existing identifier-expression grammar after `&` and
`^`. Generic names therefore inherit ordinary identifier behavior instead of
being classified by a parallel generic-specific mode.

For a simple identifier, the three important forms are:

| Identifier expression | Argument-map behavior |
| --- | --- |
| `_T` | private and inferred |
| `T` | public, required, and never inferred |
| `T?` | public and required as a value, but its name is optional |

The `?` in `T?` controls whether the name may be omitted. It does not make the
generic value optional. `_T?` remains invalid wherever private argument names
cannot be optional under the existing identifier rules.

This reuse is also what permits dependent identifier expressions. The AST
must preserve the complete identifier expression even when the first
bootstrap evaluator only resolves the simple `_T`, `T`, and `T?` cases.

## Function ownership

A generic introduction is owned by the nearest enclosing function type. The
collector searches that function's domain but does not cross into a nested
function type.

```datra
outer := {
  value? : (&T :: Any)
  inner? : ({item? : (&U :: T)} -> U)
} -> T
```

`T` belongs to `outer`; `U` belongs to `inner`. The nested function may refer
to the enclosing `T`, but its own introductions do not join the outer prefix.

A generic introduction without an owning function domain is invalid. A plain
identifier occurrence is a reference, not another declaration. Repeating the
same declaration in one function domain is an error.

## Prefix normalization

Before domain evaluation, collect every `&` and `^` introduction owned by the
function in source order and move the resulting bindings to the beginning of
the enclosing domain map. At the marked source position, retain an ordinary
reference to the introduced value.

For example:

```datra
(a : _T; b : (&_T :: IntLimit))
```

normalizes conceptually to a product prefix binding followed by the ordinary
members:

```datra
(_T : IntLimit; a : _T; b : _T)
```

The semantic prefix entry retains its product polarity. During bootstrapping,
the same entry may lower internally to `for _T of IntLimit`.

Likewise:

```datra
{Args (&_T :: IntLimit),}
```

has the prepared layout:

```text
[_T : IntLimit; Args _T]
```

and:

```datra
(a : T; b : &(T?))
```

has the prepared layout:

```text
[T? : Any; a : T; b : T]
```

This ordering is observable. Generic prefix members participate in map
position, projection, argument matching, `it`, and any later map operation.

The same prefix rule applies to ordered `AtlasMap` values and unordered
`ArgumentMap` values, with their existing naming rules:

- In an argument map, private `_T` product values are inferred and inserted
  into the prepared prefix. Public `T` values must be supplied. `T?` values
  may be supplied by position or name.
- In an ordered map, every prefix member remains a positional map member. A
  leading underscore does not remove that member or turn an ordered map into
  an argument-inference boundary.

Collection happens before resolving ordinary domain entries. An ordinary
entry may therefore refer to a declaration whose marker appeared later in the
written domain:

```datra
(a : _T; b : &_T)
```

The collected prefix is an ordered telescope. A generic bound may refer only
to earlier prefix binders. Product and sum binders may alternate:

```datra
{
  source? : (^_Source :: Any)
  target? : (&Target :: Any)
  proof? : (^_Proof :: Target)
  convert? : _Source -> Target
}
```

This is one mixed prefix, not a container that must be classified as wholly
product or wholly sum.

## Static dependency and taint

Taint records which values require protected observation.

1. Every `^` binder is a taint root.
2. A later generic binder is tainted when its identifier expression, bound, or
   construction transitively depends on a tainted binder.
3. An ordinary prepared domain value is tainted when its annotation,
   selection, or construction transitively depends on a tainted binder.
4. An expression result is tainted when evaluating it touches a tainted or
   dynamically protected value.

Consequently, an `&` binder may be either clean or tainted:

```datra
^T :: Number
&U :: Any       # clean
&V :: Family T  # tainted through T
```

Taint is computed by binder identity, not identifier spelling. Nested
functions and shadowed names cannot merge dependency graphs accidentally.

Static taint has two jobs:

- decide which product binders the codomain may use; and
- decide which prepared body bindings begin as scope-protected values.

After body evaluation begins, the general runtime propagation rule handles
all further derived values.

## Scope table

| Binding | Domain resolution | Codomain direct binding | Codomain `_it` | Function-body direct binding | Function-body `it` |
| --- | --- | --- | --- | --- | --- |
| ordinary domain identifier | yes | no | no | yes | yes |
| clean `&` | yes | yes for a simple bindable identifier | yes | yes | yes |
| tainted `&` | yes | no | no | yes, protected | yes, protected |
| `^` | yes | no | no | yes, protected | yes, protected |
| ordinary value dependent on taint | yes | no | no | yes, protected | yes, protected |

The codomain and body are different scopes:

- The codomain receives every clean product prefix member. A simple identifier
  such as `_T` or `T` is available directly.
- The codomain also receives `_it`, containing the clean product prefix in its
  prepared map order. Private inferred products are included.
- The codomain does not receive ordinary domain arguments, sums, tainted
  products, or tainted ordinary values.
- A codomain whose expression transitively depends on protected evidence is
  rejected.
- The function body receives all prepared prefix members and all ordinary
  domain members.
- Body `it` is the complete prepared domain map: generic prefix first,
  followed by ordinary arguments. It is not an erased suffix.

If any member used to construct body `it` is protected, construction protects
the aggregate `it` value under the universal lifting rule. Clean members also
remain available through their direct bindings, so protection of the aggregate
does not retroactively taint an unrelated direct binding.

Complex identifier expressions participate through the normal map binding
and contextual-access machinery. Only a simple bindable identifier implies a
same-spelling direct scope entry.

## Product semantics

A clean `&` binder denotes an ordinary selected value within its bound.

For an argument-map function domain:

- `&_T :: P` is inferred from dependent arguments and inserted into the
  prepared prefix;
- `&T :: P` must be supplied explicitly and cannot be inferred; and
- `&(T?) :: P` must be supplied, but may be supplied positionally or by name.

The selected value must satisfy `P`. All dependent domain members are then
checked against the same selected value.

Example:

```datra
max := {Args (&_T :: IntLimit),} -> _T do
  # `_T` is available both directly and through body `it`.
```

During codomain evaluation, `_T` is available directly and in codomain `_it`.
During body evaluation, it is an ordinary unprotected value unless its own
bound or construction is tainted.

## Sum semantics

A `^` binder introduces concrete evidence that may be observed only by its
authorized dynamic scopes.

```datra
{
  ^T :: Number
  x : T
  render : T -> Str
} -> Str
```

The function body may use `T`, `x`, and `render` together. Their concrete
relationship is valid inside that activation. Values whose preparation
depends on `T`, including `x` and `render`, begin protected as well.

The codomain cannot refer to `T`, because codomain evaluation is not the
function-body activation. A result derived from `T` can still be yielded, but
the returned wrapper becomes `Absurd` when an unauthorized caller attempts to
observe it.

Public/private/optional-name behavior is inherited from the same identifier
expression rules used by products. The polarity changes scope protection, not
identifier parsing.

## `Absurd`

`Absurd` is the empty federation: conceptually, an `Either` with zero
alternatives. It has no ordinary inhabitants and is a subfederation of every
type.

The surface language currently cannot spell an empty `Either`, so the
implementation must add:

```datra
Absurd := !~"datra.absurd"
```

to `std.datra`, together with the external symbol `datra.absurd` that produces
the canonical empty-federation value.

`Absurd` is the single fallback for every inaccessible protected value. There
is no per-value widened fallback and no need to calculate a union of possible
results. In particular, an inaccessible `Number`, `Str`, or function does not
appear as its declared upper bound; it appears as `Absurd`.

The type laws must include:

- `Absurd of X` for every `X`;
- no ordinary value specifies to `Absurd`;
- `Absurd` has no selectable member;
- `X | Absurd` canonicalizes to `X`; and
- rendering and canonicalization preserve the name `Absurd` without exposing
  an internal encoding.

An operation on an unauthorized protected value returns `Absurd` before the
ordinary operation runs. Thus comparing two inaccessible protected values
does not reveal that their fallbacks are the same; the comparison result is
itself `Absurd`.

## Dynamic scope identities

Every dynamic scope introduction receives a fresh internal natural number.
The counter starts at zero for an evaluation and increases monotonically each
time evaluation enters a new scope. Function calls are one source of scopes,
but they are not privileged: blocks, closure activations, and every other
runtime scope use the same allocator.

These identities:

- are dynamic activation identities, not lexical source locations;
- are never rendered or otherwise exposed to Datra code;
- are never reused during one evaluation; and
- cannot be forged or compared by user code.

Re-entering the same function or closure creates a new identity. Retaining a
closure cannot reactivate an expired activation merely because it originated
from the same lexical body.

## Protected values

A scope-protected value stores:

```text
actual value
authorized scope identities
```

It does not store a custom fallback. The fallback is always `Absurd`.

When `^T` is introduced in a body activation, its actual witness is protected
with that activation's identity. Every initially tainted prepared value is
protected in the same way.

When an accessible protected value is deliberately bound, passed, or captured
into a child scope, the child identity is added to its authorization set.
Only a currently authorized scope can delegate access. Copying a wrapper from
an unrelated scope cannot grant authority.

The wrapper may physically cross a scope boundary while preserving its actual
value and authorization set. The actual value is used only when the current
scope identity is authorized. An unauthorized observation produces `Absurd`.

## Universal protection lifting

Every evaluator operation follows one rule:

1. If none of its operands is protected, evaluate normally.
2. If every protected operand authorizes the current scope, evaluate the
   ordinary operation using their actual values.
3. Protect the result with the intersection of the protected operands'
   authorization sets.
4. If any protected operand does not authorize the current scope, do not run
   the ordinary operation; return `Absurd`.

The current scope is in every operand set during an authorized multi-operand
operation, so the intersection remains usable there. Intersection prevents a
result from gaining authority that one of its inputs did not possess.

This rule applies to all value-producing and value-observing operations,
including:

- assignment and identifier evaluation;
- function application and closure capture;
- map construction, access, and concatenation;
- equality, ordering, arithmetic, and Boolean operations;
- `~>`, `<~`, and `of`;
- conditional selection; and
- rendering or other final observation.

No operation needs its own fallback-type calculation. Operations continue to
implement only their ordinary behavior; a shared evaluator boundary unwraps
authorized operands and wraps the result.

Aliasing is therefore not a special case:

```datra
actual := T
```

Evaluating `T` and binding the result creates a new protected value with the
same actual value and effective authority. Nothing is unwrapped permanently.

Control flow follows the same rule:

```datra
actual := if T of Nat then "Nat" else "NotNat"
```

Inside an authorized scope, the actual `T` selects the branch and `actual`
becomes a protected string. Outside an authorized scope, attempting the
operation produces `Absurd`. There is no need to calculate
`"Nat" | "NotNat"` as a fallback.

Function application is also ordinary lifting. Given protected values:

```datra
x : T
render : T -> Str
```

`render x` is valid in an authorized scope and produces a protected `Str`.
That result may be used in authorized descendant scopes. Unauthorized
observation produces `Absurd`.

Before a function body activation ends, result validation runs while that
activation is still authorized, so it checks the actual protected payload
against the clean codomain. The returned wrapper then retains its authority;
it does not disclose the payload to the caller.

## Required AST representation

The generic AST retains full identifier expressions and stable binder
identity:

```haskell
data GenericPolarity
  = GenericProduct
  | GenericSum

newtype GenericBinderId = GenericBinderId Natural

data GenericIntroduction expression = GenericIntroduction
  { genericIntroductionPolarity :: GenericPolarity
  , genericIntroductionIdentifier :: expression
  , genericIntroductionBound :: expression
  , genericIntroductionSource :: Maybe SourceSpan
  }

data GenericBinder expression = GenericBinder
  { genericBinderId :: GenericBinderId
  , genericBinderPolarity :: GenericPolarity
  , genericBinderIdentifier :: expression
  , genericBinderBound :: expression
  , genericBinderSource :: Maybe SourceSpan
  }

data GenericReference = GenericReference
  { genericReferenceBinderId :: GenericBinderId
  , genericReferenceRole :: GenericReferenceRole
  }

FunctionTypeExpression
  :: [GenericBinder Expression]
  -> Expression
  -> Expression
  -> Expression
```

The identifier stays as `Expression`; privacy and optional naming remain
properties of the normal identifier-expression AST. Stable binder IDs, rather
than text, drive reference resolution, taint, shadowing, and diagnostics.

The declaration occurrence and every use are represented as references to the
same binder. Rendering may reconstruct the declaration marker from its
reference role and the owning function's telescope.

## Bootstrap implementation plan

### 1. Add the bottom value

Implement the zero-alternative federation as `datra.absurd`, bind it as
`Absurd` in `std.datra`, and add its specification, subfederation, projection,
canonicalization, and rendering laws. This value is required before protected
fallback behavior can be tested.

### 2. Parse with the shared identifier machinery

Parse `&` and `^` into `GenericIntroductionExpression` using the existing
IdenExp parser. Preserve optional-name wrappers and dependent identifier
expressions. Default the missing bound to `Any`.

### 3. Collect and normalize the prefix

While constructing a function type:

1. collect owned introductions from its domain without entering nested
   function types;
2. allocate stable binder IDs in source order;
3. replace marked occurrences with binder references;
4. insert the binders as real prefix members of the domain map;
5. resolve bounds from left to right; and
6. resolve ordinary domain entries against the complete collected prefix.

Apply the transformation to both `AtlasMap` and `ArgumentMap`. Record enough
layout information to preserve prefix positions through matching and body
construction.

### 4. Unify the dependent-map engine

For bootstrapping, product binders may reuse the current `ForBinding`
evaluation behavior and sum binders may reuse the current `WithBinding`
behavior. This is a lowering strategy, not the language grammar.

Refactor their separate whole-container paths into one ordered dependent-map
engine. Each prefix entry carries its own polarity, identifier expression,
bound, binder identity, and taint. Remove the mixed-container classification
and `MixedDependentBinders` rejection; mixed prefixes execute from left to
right.

The adapter must not collapse a generic identifier to a parallel name-mode
enum.
If the legacy nodes cannot carry the complete IdenExp, refactor their internal
descriptor rather than losing identifier structure.

### 5. Implement product and sum matching

Use existing map matching for public names and positions. Add private product
inference for argument maps, insert inferred values into the prepared prefix,
and require non-optional public products explicitly. Open sum evidence into
the same prepared prefix.

All witness checks use ordinary specification and subfederation operations.
Bounds and dependent entries are evaluated in telescope order.

### 6. Compute taint and codomain scope

Compute transitive taint from every sum binder through later generic bounds
and prepared domain dependencies. Build the codomain environment from only
clean product binders. Bind simple identifiers directly and construct
codomain `_it` from the same clean prefix.

Reject a codomain expression that references a sum, a tainted product, or any
other protected dependency.

### 7. Add dynamic scope identities and protected values

Thread a fresh-scope counter through evaluation. Add a runtime protected-value
form containing an actual `InterpretedValue` and an authorization set. Protect
sums, tainted products, and tainted prepared ordinary values when the function
body activation is created.

Centralize child-scope delegation so captures, arguments, and bindings add a
fresh child identity only when the parent scope is authorized.

### 8. Lift evaluator operations

Put authorization checking, operand unwrapping, result wrapping, and authority
intersection at the common evaluator-operation boundary. Individual
operations keep their existing implementation and receive ordinary actual
values only after the common check succeeds.

Audit lazy values and closures so deferred evaluation retains protection and
cannot accidentally execute an actual payload in an unauthorized scope.

### 9. Build the body environment

Bind every generic prefix member and every ordinary domain member in the
function body. Construct body `it` from the complete prepared domain map.
Apply initial wrappers according to taint rather than deleting or widening any
members.

Validate a yielded payload before leaving the authorized activation, then
return the protected wrapper unchanged.

### 10. Remove bootstrap duplication

Once generic prefixes drive all dependent-map evaluation, make the generic
binder descriptor the canonical internal path. Keep `ForBinding` and
`WithBinding` only where still required by existing surface syntax, lowering
them into the same engine rather than maintaining parallel semantics.

## Diagnostics

Errors should identify the binder identity and source location when possible.
Required structured failures include:

- a generic introduction outside a function domain;
- a duplicate declaration in one function telescope;
- a bound that refers forward or forms a dependency cycle;
- a required public generic that was not supplied;
- failed, ambiguous, or conflicting private inference;
- a supplied witness outside its bound;
- a codomain dependency on protected evidence; and
- an invalid identifier expression under the ordinary IdenExp rules.

Unauthorized runtime observation is not a bespoke escape error. Its value is
`Absurd`, and subsequent behavior follows the ordinary bottom-type laws.

## Test plan

### Parsing and normalization

- Parse `_T`, `T`, and `T?` for both polarities through the shared IdenExp
  machinery; reject invalid private optional names consistently.
- Preserve explicit bounds and default omitted bounds to `Any`.
- Verify precedence for `Args (&_T :: IntLimit)` and `&(T?)`.
- Preserve dependent identifier expressions in the AST.
- Collect introductions without crossing nested function types.
- Normalize both regular and argument maps to a real generic prefix.
- Verify `(a : _T; b : &_T)` has prepared order `[_T; a; b]`.
- Verify `{Args (&_T :: IntLimit),}` has prepared order `[_T; Args _T]`.
- Permit alternating `&` and `^` binders and reject forward bound
  dependencies.

### Identifier and matching behavior

- Infer a private product in an argument map and insert it into the prefix.
- Require `&T`; accept `&T?` by position and by name.
- Keep every generic member positional in a regular ordered map, including
  identifiers beginning with `_`.
- Apply the same existing optional-name behavior to sum binders.
- Check bounds and all dependent entries against one consistent witness.

### Codomain and body scopes

- Expose every clean product directly in the codomain when it has a simple
  identifier.
- Include clean private and public products in codomain `_it` in prefix order.
- Exclude ordinary arguments, sums, and tainted products from the codomain.
- Reject direct and transitive protected codomain dependencies.
- Expose all generic and ordinary identifiers in the body.
- Construct body `it` as the full prepared map, with prefix first.
- Protect sums, tainted products, and tainted ordinary prepared values.

### Scope protection

- Allocate distinct identities for repeated activations of the same lexical
  scope.
- Delegate an accessible protected value to an entered child scope.
- Refuse delegation from an unauthorized scope.
- Preserve protection through `actual := T` without a special alias branch.
- Protect conditional, arithmetic, comparison, map, access, function, and
  closure results whenever any operand is protected.
- Use authority intersection for operations with multiple protected operands.
- Return `Absurd` without running the underlying operation when any protected
  operand is unauthorized.
- Keep lazy and captured computations from observing payloads after their
  authority expires.
- Validate yielded actual payloads while the body activation remains
  authorized.

### `Absurd` laws

- Resolve `Absurd` from `std.datra` and `datra.absurd` directly.
- Prove it is a subfederation of representative scalar, map, function, union,
  and meta types.
- Refute attempts to supply an ordinary inhabitant of `Absurd`.
- Refute projection of any member from `Absurd`.
- Render the canonical value as `Absurd`.
- Ensure equality or another operation on inaccessible protected values
  produces `Absurd` instead of leaking fallback equality.

### Required language interactions

Exercise clean and protected generics with:

- forward specification using `~>`;
- reverse specification using `<~`;
- subfederation using `of`;
- optional names independently from optional values;
- regular maps and argument maps;
- nested closures and recursive calls; and
- mixed product/sum telescopes.

## Completion criteria

The bootstrap is complete when:

1. `&` and `^` use the shared identifier-expression grammar and retain full
   IdenExp structure;
2. every owned generic becomes a real, ordered domain-prefix member;
3. mixed product/sum prefixes evaluate through one dependent-map engine;
4. private/public/optional-name matching follows the existing map rules;
5. static taint correctly distinguishes clean and protected products;
6. the codomain receives only clean products, both directly and through
   `_it`;
7. the body receives all prefix and ordinary members through names and full
   `it`;
8. dynamic scope identities and delegation control access to protected actual
   values;
9. every evaluator operation propagates protection through the common lifting
   rule;
10. inaccessible observation produces the canonical `Absurd` value;
11. `Absurd` is available as `datra.absurd` and from `std.datra` and obeys the
    empty-federation laws;
12. `~>`, `<~`, `of`, optional names, nested scopes, closures, recursion, lazy
    evaluation, and mixed telescopes have focused regression coverage; and
13. the full non-Liquid test suite passes serially.
