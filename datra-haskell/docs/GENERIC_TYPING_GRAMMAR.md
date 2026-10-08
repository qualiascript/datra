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
generic-introduction := generic-polarity generic-identifier generic-bound?
generic-polarity     := "&" | "^"
generic-identifier   := private-name
                     | required-public-name
                     | optional-public-name
generic-bound        := "::" expression
```

The bound defaults to `Any` when `::` is omitted.

Examples:

```datra
&_T
&T :: IntLimit
&T? :: Any

^_T
^T :: Number
^T? :: Any
```

The generic name is written directly after its polarity. Parentheses may
delimit the complete introduction where ordinary precedence requires them:

```datra
Args (&_T :: IntLimit)
(a : T; b : &T?)
```

The parser must reuse the simple-name cases of the existing identifier-
expression grammar after `&` and `^`. Generic names therefore inherit ordinary
privacy and optional-name behavior instead of being classified by a parallel
generic-specific mode.

For a simple identifier, the three important forms are:

| Identifier expression | Argument-map behavior |
| --- | --- |
| `_T` | private and inferred |
| `T` | public, required, and never inferred |
| `T?` | public and required as a value, but its name is optional |

The `?` in `&T?` or `^T?` belongs to the identifier name and controls whether
that name may be omitted at the call boundary. It does not construct
`Maybe T`, apply the optional-value operator to `T`, or make the generic value
optional. `_T?` remains invalid wherever private argument names cannot be
optional under the existing identifier rules.

A generic introduction may attach only to one simple identifier. Identifier
templates, identifier operations, and other dependent identifier expressions
are rejected. Parentheses and the existing optional-name wrapper do not make a
simple identifier dependent.

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

A generic introduction outside a function domain remains an unowned raw AST
node; parsing and generic collection do not fail merely because it has no
owner. A plain identifier occurrence is a reference, not another declaration.
Each simple name may be introduced only once in a function telescope:
repetitions are semantic errors even if they use different polarities, bounds,
or optional-name forms.

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
(a : T; b : &T?)
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

## Protection derivation in the domain

Protection is derived directly by evaluation; it does not require a separate
dependency analysis.

1. Every `^` binder is created as a value protected to the function-type
   domain scope.
2. Evaluating a later generic bound, selection, or construction through that
   value invokes universal protection lifting.
3. The resulting `&` or ordinary prepared value is therefore protected with
   the appropriate authority intersection.
4. Values whose evaluation never touches protected evidence remain ordinary.

Consequently, an `&` binder may be either unprotected or domain-protected:

```datra
^T :: Number
&U :: Any       # unprotected
&V :: Family T  # protected through T
```

There is no second dependency graph to maintain. Binder identity still
controls name resolution and shadowing, while the runtime wrapper records the
actual scope dependency. Codomain construction simply includes unprotected
products and excludes domain-protected products.

## Function-type evaluation scopes

Function-type evaluation uses ordinary scope protection rather than a second
codomain-specific dependency mechanism.

1. Evaluate and match the prepared domain in a fresh domain scope. This scope
   does not synthesize `it` or `this` bindings.
2. Introduce every `^` witness as protected to the domain scope. An `&` witness
   becomes protected automatically if evaluating it touches a domain-protected
   value.
3. Evaluate the codomain in its own fresh scope. Bind into that scope every
   `&` identifier whose value is not protected to the domain scope. Do not
   delegate domain-protected values to the codomain scope.
4. After the type boundary has been prepared, enter the function-body scope.
   Bind all ordinary arguments and all generic identifiers there, delegating
   protected values from the still-authorized domain preparation into the new
   body scope.

The handoff allocates the body identity and extends accessible protected
values while the domain scope is still current. The domain and codomain scopes
are then removed before body evaluation begins, so they do not appear as the
receiving outer block at `yield`.

The domain and codomain scopes are implementation scopes for the function
type, not user-facing maps. The codomain receives no contextual bindings. Its
only domain-derived bindings are the unprotected `&` identifiers.

This makes codomain visibility a direct consequence of scope protection. A
clean product is an ordinary value and can be rebound in the codomain scope. A
sum, or a product derived from a sum, remains protected to the domain scope and
cannot be observed from the codomain scope.

## Scope table

| Binding | Domain scope | Codomain scope | Function-body direct binding | Function-body `it` |
| --- | --- | --- | --- | --- |
| ordinary domain identifier | yes | no | yes | yes |
| clean `&` | yes | yes | yes | yes |
| domain-protected `&` | yes, protected | no | yes, protected | yes, protected |
| `^` | yes, protected | no | yes, protected | yes, protected |
| ordinary value dependent on protection | yes, protected | no | yes, protected | yes, protected |

The codomain and body are different scopes:

- The codomain receives every unprotected product prefix member directly under
  its simple identifier, including private inferred products such as `_T`.
- The codomain does not receive ordinary domain arguments, sums,
  domain-protected products, or protected ordinary values.
- A direct codomain reference to an excluded generic is unresolved because no
  binding for it exists in the codomain scope. If a protected wrapper reaches
  codomain evaluation through another in-scope value, ordinary protection
  still reduces an unauthorized observation to `Absurd`.
- The function body receives all prepared prefix members and all ordinary
  domain members.
- Body `it` is the complete prepared domain map: generic prefix first,
  followed by ordinary arguments. It is not an erased suffix.

If any member used to construct body `it` is protected, construction protects
the aggregate `it` value under the universal lifting rule. Clean members also
remain available through their direct bindings, so protection of the aggregate
does not retroactively protect an unrelated direct binding.

Every generic has a simple direct binding. No dependent identifier binding or
codomain contextual map is required.

## Product semantics

A clean `&` binder denotes an ordinary selected value within its bound.

For an argument-map function domain:

- `&_T :: P` is inferred from dependent arguments and inserted into the
  prepared prefix;
- `&T :: P` must be supplied explicitly and cannot be inferred; and
- `&T? :: P` must be supplied, but may be supplied positionally or by name.

The selected value must satisfy `P`. All dependent domain members are then
checked against the same selected value.

Example:

```datra
max := {Args (&_T :: IntLimit),} -> _T do
  # `_T` is available both directly and through body `it`.
```

During codomain evaluation, `_T` is available directly. During body
evaluation, `_T` is an ordinary unprotected value unless its own bound,
selection, or construction became protected through ordinary domain
evaluation.

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

The codomain cannot refer to `T`, because its separate scope is not authorized
for the domain-protected witness. A result derived from `T` may be computed in
the body, but `yield` checks it using the enclosing block's scope identity
rather than the body's identity. If the enclosing block is not authorized, the
candidate result becomes `Absurd` before codomain validation.

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

The empty federation being a subfederation of a codomain is not the same as
the `Absurd` value being accepted as that codomain's returned value. Result
validation normally rejects an `Absurd` candidate unless that particular
codomain accepts it. This distinction lets subfederation retain the ordinary
bottom law without turning every protected `yield` into a successful return.

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
time evaluation enters a new scope. The interpreter maintains the active
identities as a stack: entering a scope allocates and pushes its identity;
leaving the scope pops it. Function calls are one source of scopes, but they
are not privileged: blocks, type-domain evaluation, type-codomain evaluation,
closure activations, and every other runtime scope use the same allocator.

These identities:

- are dynamic activation identities, not lexical source locations;
- are never rendered or otherwise exposed to Datra code;
- are never reused during one evaluation; and
- cannot be forged or compared by user code.

Re-entering the same function or closure creates a new identity. Retaining a
closure cannot reactivate an expired activation merely because it originated
from the same lexical body.

The stack is required at scope-crossing operations. Ordinary evaluation uses
the top identity. `yield` deliberately checks the yielded value against the
next enclosing block identity instead, because that is the scope which would
receive the value.

## Protected values

A scope-protected value stores:

```text
actual value
authorized scope identities
```

It does not store a custom fallback. The fallback is always `Absurd`.

When `^T` is introduced in the function-type domain scope, its actual witness
is protected with that scope's identity. Products and ordinary prepared values
derived from it acquire protection through universal lifting. The body handoff
then adds the body identity to those existing wrappers.

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

## `yield` boundary

`yield` is an observation by the enclosing block, not by the block that is
yielding. Its boundary algorithm is:

1. evaluate the result expression normally in the current scope;
2. find the receiving outer block's identity on the scope stack;
3. attempt to observe the candidate using that outer identity;
4. use the actual value when that identity is authorized, otherwise use
   `Absurd`; and
5. validate that observed candidate against the function codomain.

A value protected only to the current function-body scope therefore cannot be
returned as its actual value. It normally produces a codomain error after
becoming `Absurd`. If the declared codomain accepts `Absurd`, the yield succeeds
with `Absurd`; the protected payload still does not cross the boundary.

Values protected to both the current scope and the receiving outer block can
cross normally. This can occur when authority was inherited from that outer
block and preserved by intersection. The check is about authorization, not
whether the value happens to be wrapped.

## Required AST representation

The generic AST retains a normalized simple identifier descriptor and a
stable binder identity:

```haskell
data GenericPolarity
  = GenericProduct
  | GenericSum

newtype GenericBinderId = GenericBinderId Natural

data GenericIdentifier = GenericIdentifier
  { genericIdentifierName :: IdentifierString
  , genericIdentifierNameOptional :: Bool
  }

data GenericIntroduction expression = GenericIntroduction
  { genericIntroductionPolarity :: GenericPolarity
  , genericIntroductionIdentifier :: GenericIdentifier
  , genericIntroductionBound :: expression
  , genericIntroductionSource :: Maybe SourceSpan
  }

data GenericBinder expression = GenericBinder
  { genericBinderId :: GenericBinderId
  , genericBinderPolarity :: GenericPolarity
  , genericBinderIdentifier :: GenericIdentifier
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

`GenericIdentifier` reuses `IdentifierString`, so privacy remains the ordinary
leading-underscore property. Its Boolean records whether the identifier name
is optional; it does not wrap the generic value in `Maybe`. Because the field
cannot contain an arbitrary expression, dependent generic identifiers are
unrepresentable after parsing. Stable binder IDs, rather than text, drive
reference resolution, shadowing, and diagnostics.

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
simple IdenExp parser cases. Preserve optional-name wrappers, reject dependent
identifier expressions, and default the missing bound to `Any`.

### 3. Collect and normalize the prefix

While constructing a function type:

1. collect owned introductions from its domain without entering nested
   function types;
2. allocate stable binder IDs in source order;
3. retain every declaration occurrence so semantic validation can diagnose a
   repeated simple name, regardless of polarity or name optionality;
4. replace marked occurrences with binder references;
5. insert the binders as real prefix members of the domain map;
6. resolve bounds from left to right; and
7. resolve ordinary domain entries against the complete collected prefix.

Apply the transformation to both `AtlasMap` and `ArgumentMap`. Record enough
layout information to preserve prefix positions through matching and body
construction.

### 4. Unify the dependent-map engine

For bootstrapping, product binders may reuse the current `ForBinding`
evaluation behavior and sum binders may reuse the current `WithBinding`
behavior. This is a lowering strategy, not the language grammar.

Refactor their separate whole-container paths into one ordered dependent-map
engine. Each prefix entry carries its own polarity, simple identifier, bound,
and binder identity. Remove the mixed-container classification and
`MixedDependentBinders` rejection; mixed prefixes execute from left to right.

The adapter must not collapse a generic identifier to a parallel name-mode
enum. Its identifier descriptor needs only a simple name plus the existing
privacy and optional-name structure; dependent names are rejected before
lowering.

### 5. Implement product and sum matching

Use existing map matching for public names and positions. Add private product
inference for argument maps, insert inferred values into the prepared prefix,
and require non-optional public products explicitly. Open sum evidence into
the same prepared prefix.

All witness checks use ordinary specification and subfederation operations.
Bounds and dependent entries are evaluated in telescope order.

### 6. Establish the codomain scope

Evaluate the prepared domain in its own scope and protect every sum witness
there. Let universal protection propagation mark later products and ordinary
values which depend on those witnesses. Evaluate the codomain in a separate
scope containing direct bindings for only the unprotected products. Do not
synthesize contextual bindings in that scope.

### 7. Add dynamic scope identities and protected values

Thread a fresh-scope counter and active-label stack through evaluation. Add a
runtime protected-value form containing an actual `InterpretedValue` and an
authorization set. Protect sums in the domain scope and use ordinary lifting
to protect products and ordinary values which depend on them.

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
Preserve and delegate wrappers already produced by domain evaluation rather
than deleting or widening any members.

At `yield`, select the receiving outer block label from the scope stack and
observe the result with that label before codomain validation. Replace an
unauthorized candidate with `Absurd`; report the ordinary codomain mismatch
unless the codomain accepts that value.

### 10. Remove bootstrap duplication

Once generic prefixes drive all dependent-map evaluation, make the generic
binder descriptor the canonical internal path. Keep `ForBinding` and
`WithBinding` only where still required by existing surface syntax, lowering
them into the same engine rather than maintaining parallel semantics.

## Diagnostics

Errors should identify the binder identity and source location when possible.
Required structured failures include:

- a repeated simple generic name in one function telescope;
- a bound that refers forward or forms a dependency cycle;
- a required public generic that was not supplied;
- failed, ambiguous, or conflicting private inference;
- a supplied witness outside its bound;
- a codomain attempt to use a generic unavailable in its scope; and
- a dependent or otherwise invalid generic identifier expression.

Unauthorized runtime observation is not a bespoke escape error. Its value is
`Absurd`, and subsequent behavior follows the ordinary bottom-type laws.

## Test plan

### Parsing and normalization

- Parse `_T`, `T`, and `T?` for both polarities through the shared simple
  IdenExp machinery; reject invalid private optional names consistently.
- Preserve explicit bounds and default omitted bounds to `Any`.
- Verify precedence for `Args (&_T :: IntLimit)` and `&T? :: Any`.
- Reject identifier templates, identifier operations, and every other
  dependent generic identifier.
- Preserve repeated generic names in the parsed telescope, then reject them
  during semantic compilation with a localized structured diagnostic,
  including repetitions with a different polarity or optional-name wrapper.
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

- Evaluate the function domain and codomain in distinct scopes.
- Give the type-domain scope no `it` or `this` binding.
- Expose every unprotected product directly in the codomain under its simple
  identifier.
- Give the codomain no contextual bindings.
- Exclude ordinary arguments, sums, and domain-protected products from the
  codomain.
- Confirm that a product computed from a domain-protected value remains
  unavailable in the codomain scope.
- Expose all generic and ordinary identifiers in the body.
- Construct body `it` as the full prepared map, with prefix first.
- Protect sums in the domain scope and verify that ordinary lifting protects
  dependent products and ordinary prepared values.

### Scope protection

- Allocate distinct identities for repeated activations of the same lexical
  scope.
- Push and pop those identities on an interpreter scope stack.
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
- At `yield`, check authorization with the receiving outer block label rather
  than the current block label.
- Reject a body-only protected result when the codomain does not accept
  `Absurd`.
- Permit that yield only when the codomain accepts `Absurd`, without exposing
  the actual protected payload.
- Permit a protected result whose authority already includes the receiving
  outer block.

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

1. `&` and `^` accept only unique simple identifiers parsed through the shared
   IdenExp rules;
2. every owned generic becomes a real, ordered domain-prefix member;
3. mixed product/sum prefixes evaluate through one dependent-map engine;
4. private/public/optional-name matching follows the existing map rules;
5. domain evaluation and universal lifting correctly distinguish unprotected
   and protected products without a separate dependency pass;
6. the codomain runs in its own scope and receives only unprotected products
   as direct identifier bindings;
7. the body receives all prefix and ordinary members through names and full
   `it`;
8. a stack of dynamic scope identities and delegation control access to
   protected actual values;
9. every evaluator operation propagates protection through the common lifting
   rule;
10. inaccessible observation produces the canonical `Absurd` value, and
    `yield` observes using the receiving outer block before codomain checking;
11. `Absurd` is available as `datra.absurd` and from `std.datra` and obeys the
    empty-federation laws;
12. `~>`, `<~`, `of`, optional names, nested scopes, closures, recursion, lazy
    evaluation, and mixed telescopes have focused regression coverage; and
13. the full non-Liquid test suite passes serially.
