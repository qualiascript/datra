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
  while its introducing scope activation remains in the active scope chain.
- An `&` value that transitively depends on a `^` value has the same protected
  observation behavior as that `^` value.

Scope protection is a general evaluator property. An operation involving a
protected value normally produces a protected result. The generic-sum policy
adds a checked exception: existential elimination may consume protected
operands and produce an ordinary result when its result contract proves that
the hidden representation cannot occur in that result. Other protection
policies need not permit that exception. The decision is made through the
common evaluator operation cycle, not by special cases in individual
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

Generic names must also be disjoint from every other identifier name introduced
in their function type's domain and codomain scopes. This is checked after
collection against both complete scopes, so moving a generic to the prefix
cannot introduce a name collision that was absent from the written order. The
rule applies to both `&` and `^`, even though a `^` binding is unavailable in
the codomain. The optional-name marker is not part of the name: `T` and `T?`
overlap.

For an ordinary simple identifier, disjointness is the existing identifier-
string overlap check. For a dependent identifier, the check is quantified over
its entire fiber domain: the generic's singleton identifier-string value must
not subtype the dependent identifier's string value at any fiber. Checking
only the fiber selected by one invocation is insufficient. If disjointness
cannot be established for every fiber, the function type is rejected. Ambient
outer bindings and function-body-local declarations are not part of this
collision set; their ordinary lexical shadowing rules remain separate. A
nested function type starts a new ownership boundary, so its locally
introduced names are checked against its own domain and codomain rather than
the enclosing function type's scopes.

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
   value invokes the common protection-lifting cycle.
3. The resulting `&` or ordinary prepared value is protected with the label of
   the scope in which that derived value is introduced unless a typed
   operation eliminates the existential through a protection-erasing result
   contract.
4. Values whose evaluation never touches protected evidence remain ordinary.
   Values returned by valid existential elimination are ordinary as well.

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

Function-type evaluation uses the interpreter's ordinary scope abstraction.
A scope introduces both bindings and one fresh activation label when it is
entered; there is no separate protection-scope stack alongside lexical scope.

1. Evaluate and match the prepared domain in a fresh domain scope. This scope
   does not synthesize `it` or `this` bindings.
2. Introduce every `^` witness as protected to the domain scope. An `&` witness
   becomes protected automatically if evaluating it touches a domain-protected
   value and no qualifying operation eliminates that dependency.
3. Prepare the function-body scope activation and install the domain scope's
   handoff stage. While the domain is still active, that stage asks the carried
   policies whether each protected binding may transfer to the body scope.
4. Leave the domain scope and evaluate the codomain in its own fresh scope.
   Bind into that scope every
   `&` identifier whose value is not protected to the domain scope. Do not
   copy domain-protected values into the codomain scope.
5. Enter the prepared function-body scope. Bind all ordinary arguments and all
   generic identifiers there, using the body-labeled protected copies produced
   by the authorized domain handoff.

The handoff replaces a domain-labeled wrapper with a newly introduced
body-labeled wrapper; it does not append another passcode. Preparing a target
scope may reserve its fresh label for a handoff, but that label becomes active
only when evaluation enters the target scope. The domain and codomain scopes
are not ancestors of the body scope, so their labels cannot authorize body
evaluation or appear in the receiving scope chain when the body exits.

The domain and codomain scopes are implementation scopes for the function
type, not user-facing maps. The codomain receives no contextual bindings. Its
only domain-derived bindings are the unprotected `&` identifiers.

This makes codomain visibility a direct consequence of scope protection. A
clean product is an ordinary value and can be rebound in the codomain scope. A
sum, or a product derived from a sum without valid existential elimination,
remains protected to the domain scope and cannot be observed from the codomain
scope.

## Scope table

| Binding | Domain scope | Codomain scope | Function-body direct binding | Function-body `it` |
| --- | --- | --- | --- | --- |
| ordinary domain identifier | yes | no | yes | yes |
| clean `&` | yes | yes | yes | yes |
| domain-protected `&` | yes, protected | no | yes, protected | yes, protected |
| `^` | yes, protected | no | yes, protected | yes, protected |
| non-eliminated value derived from protection | yes, protected | no | yes, protected | yes, protected |

The codomain and body are different scopes:

- The codomain receives every unprotected product prefix member directly under
  its simple identifier, including private inferred products such as `_T`.
- The codomain does not receive ordinary domain arguments, sums,
  domain-protected products, or protected ordinary values.
- A direct codomain reference to an excluded generic is unresolved because no
  binding for it exists in the codomain scope. If a protected wrapper reaches
  codomain evaluation through another in-scope value, ordinary protection
  still reduces an unauthorized observation to `Never`.
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
selection, or construction became protected through domain evaluation without
subsequent existential elimination.

## Sum semantics

A `^` binder introduces concrete evidence that may be observed only while its
introducing scope occurs in the active scope ancestry.

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

The codomain cannot refer to `T`, because the domain scope is not an ancestor
of the codomain and no binding for `T` is installed there. A result derived
from `T` normally remains protected, but a suitable typed operator or function
may eliminate the existential and return an ordinary value. For example,
`render x` may return an ordinary `Str` because the checked `Str` result cannot
retain `T`. A protected result which has not been eliminated is still checked
by the function-body handoff against the caller ancestry and becomes `Never`
when its introducing scope is absent.

Public/private/optional-name behavior is inherited from the same identifier
expression rules used by products. The polarity changes scope protection, not
identifier parsing.

## Two protection layers

Dynamic scope protection is a reusable runtime facility, not the definition
of existential generics. Keep these two layers explicit:

1. The **scope-protection substrate** reads activation labels from the
   interpreter's active scope chain and owns authorization, actual-value
   unwrapping, generic handoff mechanics, and `Never` as the universal result
   of unauthorized observation. It does not maintain a second scope stack.
2. A **protection policy** decides which values enter that substrate, how
   protection propagates through authorized operations, which checked
   operations may return an ordinary result, and whether or how a value may be
   transferred across a scope boundary.

Generic sums use an existential protection policy. Introducing `^T` protects
its witness, values derived from it lift that policy, and a qualifying closed
result contract may eliminate it. These are rules of the generic-sum policy,
not rules built into `ScopeProtected` itself.

This distinction leaves room for other dynamically scoped facilities. A
future mutable-region policy might share label authorization and the `Never`
fallback while forbidding existential-style elimination, requiring an
explicit ownership transfer, or imposing a stricter boundary rule. The exact
mutable-state policy need not be decided now; the substrate must merely avoid
assuming that every protected value follows generic-sum escape rules.

## `Never`

`Never` is the empty federation: conceptually, an `Either` with zero
alternatives. It has no ordinary inhabitants and is a subfederation of every
type.

The surface language currently cannot spell an empty `Either`, so the
implementation must add:

```datra
Never := !~"datra.never"
```

to `std.datra`, together with the external symbol `datra.never` that produces
the canonical empty-federation value.

`Never` is the single fallback for every inaccessible protected value. There
is no per-value widened fallback and no need to calculate a union of possible
results. In particular, an inaccessible `Number`, `Str`, or function does not
appear as its declared upper bound; it appears as `Never`.

The empty federation being a subfederation of a codomain is not the same as
the `Never` value being accepted as that codomain's returned value. Result
validation normally rejects a `Never` candidate unless that particular
codomain accepts it. This distinction lets subfederation retain the ordinary
bottom law without turning every protected `yield` into a successful return.

The type laws must include:

- `Never of X` for every `X`;
- no ordinary value specifies to `Never`;
- `Never` has no selectable member;
- `X | Never` canonicalizes to `X`; and
- rendering and canonicalization preserve the name `Never` without exposing
  an internal encoding.

An operation on an unauthorized protected value returns `Never` before the
ordinary operation runs. Thus comparing two inaccessible protected values
does not reveal that their fallbacks are the same; the comparison result is
itself `Never`.

## Unified scope activations and handoff

`Scope` is the interpreter's single runtime scope abstraction. Each activation
contains:

```text
bindings introduced by this scope
one fresh activation label
its active parent scope, if any
an optional handoff stage
presentation and source metadata
```

Entering a lexical scope creates one activation and allocates its fresh
internal natural-number label. Leaving that scope removes the same activation,
so lexical visibility and protection authority cannot diverge. Authorization
derives the ordered label chain by walking active scope parents; the evaluator
must not carry a separate active-label stack or create protection-only scopes.

The label counter starts at zero for an evaluation and increases monotonically.
A target scope whose label is needed by an authorized handoff may reserve its
activation before its body begins evaluation, but the reserved label is not
part of the active chain until that target is entered. Function calls are one
source of activations, but they are not privileged: blocks, type-domain
evaluation, type-codomain evaluation, closure calls, modules, and every other
runtime scope use the same constructor.

These labels:

- identify dynamic activations, not lexical source locations;
- are never rendered or otherwise exposed to Datra code;
- are never reused during one evaluation; and
- cannot be forged or compared by user code.

Re-entering the same function or closure creates a new label. Retaining a
closure retains its lexical bindings but not the active status of the scopes
in which it was created. Calling it creates a new activation beneath the
caller's current scope; it cannot reactivate an expired activation merely
because it originated from the same lexical body.

Every scope may install a handoff stage for values or bindings which leave it.
A handoff names a receiving scope activation and gives each carried protection
policy the opportunity to choose one of three dispositions:

- preserve the existing wrapper and introducing label;
- transfer the wrapper to the receiving scope's label; or
- reject the crossing, producing `Never`.

The source scope remains active while the policies decide, so its protected
payloads can be authorized without being exposed. All policies on a value must
agree on a compatible disposition. Preservation succeeds only when the old
introducing scope remains in the receiver's active ancestry. Transfer creates
one wrapper carrying only the receiving label; it never adds a second label.
An unprotected value passes through unchanged.

Without an installed stage, scope exit is conservative: unprotected values
pass, and a protected wrapper can only be preserved unchanged when its
introducing scope is already present in the receiving ancestry. No label
transfer or boundary-specific validation is implied.

Handoff is a generic scope-exit facility, not syntax attached specifically to
`yield`. Ordinary nested scopes, the type-domain-to-body transition, function
return, and future resource scopes all use the same mechanism while installing
different policy decisions and optional validation stages. A scope with no
handoff stage does not implicitly grant transfer authority.

## Scope-protection substrate

A scope-protected value has a policy-neutral runtime wrapper:

```text
actual value
introducing scope label
nonempty protection policy set
```

In implementation terms this can be an internal `ScopeProtected` value form:

```haskell
data ScopeProtected = ScopeProtected
  { scopeProtectedActual :: InterpretedValue
  , scopeProtectedLabel :: DynamicScopeLabel
  , scopeProtectedPolicies :: NonEmpty ScopeProtectionPolicy
  }

data ScopeProtectionPolicy
  = GenericExistentialProtection
  -- Future policies, such as mutable-region protection, belong here.
```

The normalized nonempty policy set is semantic data interpreted by centralized
protection operations; it is not a collection of function closures stored
inside each value. Initial protection uses a singleton set. A result derived
from values governed by different policies carries their normalized union
unless every policy approves another disposition. A future policy may acquire
small opaque policy-specific metadata if its semantics requires it, but
authorization still uses the one introducing label.

`ScopeProtected` does not store an authorization set or a custom fallback.
The fallback is always `Never`. The active scope ancestry already determines
the complete authorization label chain, so a per-value set is redundant.

A protected value is accessible exactly when its one introducing label occurs
anywhere in the current active scope chain. Descendant scopes therefore retain
access automatically while their introducing ancestor remains active; no
child-label delegation or passcode copying is necessary. Once that scope is
exited, the value may still physically exist, but observing it produces
`Never`.

Conceptually, substrate-level observation is only:

```text
observe(activeScope, ScopeProtected(actual, passcode, policies)) =
  if passcode is in labels(activeScope) then actual else Never
```

A handoff checks the receiving scope's ancestry rather than the source scope's
ancestry after the policies have selected preservation, transfer, or rejection.
The substrate does not decide that an authorized value should become
permanently ordinary, move to another label, or remain protected; it asks every
policy carried by the value.

The substrate exposes a small internal interface:

- authorize and unwrap operands against an active scope chain;
- return `Never` without evaluating the underlying operation when
  authorization fails;
- combine the policies of authorized operands for a derived result;
- ask those policies whether a checked result may become ordinary;
- rewrap a non-eliminated result with the current scope label; and
- run a scope's optional handoff stage and ask every carried policy whether the
  wrapper is preserved, transferred to the receiving scope, or rejected.

If several policies occur in one operation, every policy must authorize the
operation and agree to any declassification or transfer. Until explicit
cross-policy composition rules exist, the conservative result remains
scope-protected.

## Generic-sum existential policy

When `^T` is introduced in the function-type domain scope, its actual witness
is wrapped as `ScopeProtected` with the singleton
`GenericExistentialProtection` policy set and the domain label. Products and
ordinary prepared values derived from it acquire that policy and the label of
the scope where the derived value is introduced.

In particular, product polarity does not imply that a witness is unprotected.
Given a telescope such as `^T; &U :: T`, evaluating and validating `U` consumes
the protected `T`, so the resulting `U` witness is protected by the generic
existential policy as well. The same rule applies transitively to later
products, sums, and ordinary domain members. This propagation comes from the
shared authorized-operation cycle; it is not a special syntactic dependency
walk over product binders.

The generic existential policy authorizes transfer for the domain-to-body
handoff, creating protected body copies carrying only the prepared body label.
It also authorizes transfer from an ordinary nested continuation scope back to
an enclosing scope which remains inside the same existential lifetime. It does
not authorize a function-body result to transfer into the caller merely because
that result is being yielded.

## Shared operation cycle and policy-specific results

Every evaluator operation uses one shared evaluation cycle:

1. Record every protection policy carried by the operands.
2. For every protected operand, look up its introducing label in the complete
   label chain derived from the current scope activation.
3. If any lookup fails, do not run the ordinary operation; return `Never`.
4. Unwrap every authorized operand and run the ordinary operation using the
   actual values.
5. Obtain the operation's optional checked result contract. Function
   application uses the evaluated function codomain; a typed primitive
   operator supplies its semantic result type. An operation with no such
   contract supplies no elimination evidence.
6. If no operand was protected, return the ordinary result.
7. Ask the participating policies whether the checked operation and result
   contract permit an ordinary result or another policy-specific disposition.
8. If every policy permits an ordinary result, validate and normalize the
   result against the contract while all operand labels remain active, then
   return the validated result without a wrapper.
9. Otherwise, combine the participating policies conservatively and protect
   the result with the current scope's top label.

Steps 7 through 9 are the policy-specific result decision. Protection lifting
is the substrate default; existential elimination is one policy's checked
exception. Individual ordinary operation implementations do not unwrap
values, inspect scope labels, remove protection, select a policy, or choose
fallbacks.

Multiple protected operands require no label intersection. Every operand label
must occur in the ancestry of the current scope before the operation runs. A
lifted result needs only the current scope's label, which is the unique passcode
for that result's own lifetime. A policy may permit an ordinary or transferred
result only after every protected operand has passed the same authorization
check and every participating policy approves that disposition.

For `GenericExistentialProtection`, the default result decision is universal
lifting and the exception is existential elimination. Other policies are not
required to expose either rule. In particular, the existence of a qualifying
public result contract must not automatically declassify a future mutable or
linear resource.

### Generic existential protection-erasing contracts

For the generic-sum existential policy, a result contract is
protection-erasing only when all of the following hold:

- the contract evaluates to an ordinary, unprotected value;
- the contract is independent of every protected generic binder consumed by
  the operation, and its own construction did not observe protected evidence;
- the contract is closed and concrete enough to constrain the complete result
  to a public representation which cannot retain an arbitrary protected
  payload; and
- the produced result successfully validates and normalizes against the
  contract before protection is removed.

The initial implementation is deliberately conservative. `Any`, open or
dependent containers, function and closure results, lazy or deferred results,
and contracts containing protected members are not protection-erasing. Merely
specifying to an ineligible contract is insufficient: for example, `T -> Any`
must not expose a protected `T` under a wider name.

Protection-erasing eligibility belongs to the semantic result contract, not
to an allowlist of operator names. A protected callable may therefore be used
as an eliminator while it is authorized if its evaluated codomain qualifies.
A primitive operator may eliminate only when it exposes the same kind of
checked result contract. Operations without a contract automatically use
ordinary lifting.

Existential elimination adds no surface syntax, AST node, authorization set,
or additional field to a protected value. It reuses the result contract already
carried by an evaluated function or typed primitive and changes only the final
classification performed by the common operation boundary.

This cycle applies to all value-producing and value-observing operations,
including:

- assignment and identifier evaluation;
- function application and closure capture;
- map construction, access, and concatenation;
- equality, ordering, arithmetic, and Boolean operations;
- `~>`, `<~`, and `of`;
- conditional selection; and
- rendering or other final observation.

No operation needs its own fallback-type calculation. Operations continue to
implement only their ordinary behavior; a shared evaluator boundary checks
label membership, unwraps accessible operands, and applies the common
result-protection decision.

Assignment, aliasing, annotations, map construction, and `yield` are not
existential eliminators merely because a target type accepts their value. They
continue to lift protection unless they are themselves implemented as typed
operations with a qualifying result contract. In particular, an annotation of
`Any` cannot be used to discharge protection, and `yield` cannot infer
elimination after the operation which produced a value has been forgotten.

Aliasing is therefore not a special case:

```datra
actual := T
```

Evaluating `T` and binding the result creates a new protected value with the
same actual value and the binding scope's label. Nothing is unwrapped
permanently, and no additional label is stored alongside it.

Control flow follows the same rule:

```datra
actual := if T of Nat then "Nat" else "NotNat"
```

While `T`'s introducing scope is present in the current ancestry, the actual
`T` selects the branch and `actual` becomes a protected string carrying the
current scope's label. After that introducing scope has exited, attempting the
operation produces `Never`. There is no need to calculate
`"Nat" | "NotNat"` as a fallback.

Function application uses the same evaluation cycle. Given protected values:

```datra
x : T
render : T -> Str
```

`render x` is valid while both operand labels occur in the current scope
ancestry. Application uses the evaluated codomain `Str` as its result contract.
Because that contract is ordinary, binder-independent, concrete, and unable to
retain the protected payload, successful result validation eliminates the
existential and produces an ordinary `Str`.

By contrast, an identity function with codomain `T`, or a function with
codomain `Any`, does not have a protection-erasing contract. Its application
therefore produces a protected result carrying the current scope label. The
same is true for a function or lazy result which could retain an authorized
operand for later observation.

## Function-body handoff and `yield`

`yield` does not implement a separate protection boundary. It evaluates the
result expression normally and completes the current function-body scope. That
scope's handoff stage targets the caller scope and composes protection-policy
decisions with ordinary codomain validation.

The generic scope-handoff algorithm is:

1. evaluate the result expression in the source scope;
2. while the source scope remains active, authorize every protection wrapper
   and ask every carried policy for preserve, transfer, or reject;
3. combine those decisions conservatively, producing `Never` on rejection or
   disagreement;
4. for preservation, retain the original wrapper only if its introducing
   scope occurs in the receiving scope's ancestry;
5. for transfer, replace the source label with the receiving scope's label;
6. leave the source scope; and
7. run any validation stage installed on the handoff, such as function
   codomain validation.

The substrate supplies authorization, transfer plumbing, and the `Never`
fallback, but it does not define one universal escape rule. A policy may allow
an unchanged still-authorized wrapper, define a particular transfer, or reject
the boundary. No policy may expose the actual payload merely because its source
scope is absent from the receiving ancestry.

For `GenericExistentialProtection`, the function-body handoff does not offer a
transfer into the caller. A value protected only to the current body scope
therefore becomes `Never`. It normally produces a codomain error; if the
declared codomain accepts `Never`, the handoff succeeds with `Never`. The
protected payload still does not cross the boundary.

An ordinary value produced earlier by existential elimination needs no special
`yield` behavior and crosses this boundary normally. `yield` itself never
removes a protection wrapper: eligibility is decided at the typed operation
boundary, while the result contract and authorized operands are still known.

Under the generic existential policy, a protected value can cross unchanged
when its introducing scope remains an ancestor of the receiving scope—for
example, a value introduced by an outer scope and passed through without
deriving a new protected result. It remains wrapped, so later observation is
still checked. A value introduced in the function body carries the body label,
which is absent from the caller ancestry and therefore becomes `Never`.

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

Implement the zero-alternative federation as `datra.never`, bind it as
`Never` in `std.datra`, and add its specification, subfederation, projection,
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
   repeated or overlapping name, regardless of polarity or name optionality;
4. replace marked occurrences with binder references;
5. insert the binders as real prefix members of the domain map;
6. validate every generic name against all other simple and dependent
   identifier names introduced in the completed domain and codomain scopes,
   rejecting a dependent identifier whenever the generic name subtypes its
   string value at any fiber;
7. resolve bounds from left to right; and
8. resolve ordinary domain entries against the complete collected prefix.

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

The runtime argument schema retains each prefix member's binder identity,
polarity, identifier optionality/privacy, and evaluated bound. Ordinary slots
also retain the binder identities referenced by their written annotations, so
evidence is produced by completed matching rather than by rescanning the AST.
This metadata does not yet create protected body values; protection remains a
separate later phase.

Private product inference is constructive, not a search among candidate
witnesses. Matching a completed dependent argument contributes its evidence
to the private binder it depends on. The inferred witness is the federation
of that binder's evidence, with duplicate and subsumed alternatives removed.
This federation is the unique least value containing all of the evidence, so
private product inference has neither a "no minimal inference" case nor an
"ambiguous inference" case.

The declaration occurrence itself is a dependent domain member, so a
successfully completed call supplies evidence for every private product.
Defaults participate after completion just like explicitly supplied values.
If a required dependent member is absent, an input does not satisfy the
binder's bound, or the completed domain is inconsistent, report the ordinary
map-matching, specification, or bound error responsible for that condition.
Do not introduce a separate generic-inference failure category.

All witness checks use ordinary specification and subfederation operations.
Bounds and dependent entries are evaluated in telescope order.

A projected family contributes one evidence value per expanded slot only when
the family is a concatenated argument segment, as in `{Args (&_T :: Nat),}`.
Without concatenation the projected value occupies one ordinary slot and
therefore contributes only that slot's value.

### 6. Add the scope-protection substrate

Make the interpreter's lexical `Scope` the only runtime scope abstraction.
Every entered scope owns its bindings, fresh activation label, active parent,
and optional handoff stage. Derive authorization labels from that parent chain;
do not thread a parallel protection context or label stack through evaluation.

Add the policy-neutral `ScopeProtected` runtime form containing an actual
`InterpretedValue`, one introducing label, and a normalized nonempty policy
set. Implement authorization, temporary unwrapping, conservative policy-set
combination, generic handoff plumbing, and `Never` fallback without embedding
any generic-sum elimination or escape rule in this layer. Function invocation
must activate its body beneath the caller's current scope rather than retaining
the active authority of the function's defining scope. Closures retain lexical
bindings, not expired activations.

### 7. Install the generic-sum existential policy

Evaluate the prepared domain in its own scope and protect every sum witness
there with `GenericExistentialProtection`. Let ordinary policy lifting protect
later products—including dependent products whose bounds or validation consume
a protected sum—and ordinary values derived from protected evidence. Evaluate
the codomain in a separate scope containing direct bindings for only the
unprotected products. Do not synthesize contextual bindings in that scope.

Install a domain-scope handoff targeting the prepared body scope. During that
policy-authorized handoff, replace each protected domain wrapper with a body
wrapper carrying only the body label. This transfer is a rule of the generic
existential policy rather than a general capability of every `ScopeProtected`
value. Ordinary nested continuation scopes may install an analogous transfer
back into an enclosing scope that remains within the same existential lifetime.

### 8. Route evaluator operations through protection policies

Put active-scope-ancestry checking, operand unwrapping, result-contract
inspection, and the result-protection decision at the common evaluator
operation boundary. Function application contributes its evaluated codomain;
typed primitive operators contribute their semantic result type; operations
without a checked result contract contribute no elimination evidence.

After ordinary evaluation, ask every participating policy for the result
disposition. The generic existential policy validates a result against a
qualifying protection-erasing contract before returning it without a wrapper;
otherwise the policies are combined and the derived result is wrapped with
the current label. Individual operations keep their existing implementation
and receive ordinary actual values only after the common authorization check
succeeds.

Audit lazy values and closures so deferred evaluation retains protection and
cannot accidentally execute an actual payload in an unauthorized scope.

### 9. Build the body environment

Bind every generic prefix member and every ordinary domain member in the
function body. Construct body `it` from the complete prepared domain map.
Preserve unprotected members and use the body-labeled wrappers produced by the
authorized domain handoff rather than deleting or widening protected members.

Install the function return behavior as the body scope's generic handoff stage
targeting the caller scope. The stage consults every carried policy, preserves
only wrappers whose introducing scope remains in the caller ancestry, applies
only explicitly authorized transfers, and otherwise produces `Never`. Compose
ordinary codomain validation after that protection handoff. `yield` only
supplies the body's result expression; it does not contain its own label-stack
or existential-elimination algorithm. An already ordinary result produced by
existential elimination crosses without special treatment.

### 10. Remove bootstrap duplication

Once generic prefixes drive all dependent-map evaluation, make the generic
binder descriptor the canonical internal path. Keep `ForBinding` and
`WithBinding` only where still required by existing surface syntax, lowering
them into the same engine rather than maintaining parallel semantics.

## Diagnostics

Errors should identify the binder identity and source location when possible.
Required structured failures include:

- a repeated simple generic name in one function telescope;
- a generic name overlapping an ordinary identifier or any string-valued
  fiber of a dependent identifier in the same function type's domain or
  codomain scope;
- a bound that refers forward or forms a dependency cycle;
- a required public generic that was not supplied;
- a supplied witness outside its bound;
- a codomain attempt to use a generic unavailable in its scope; and
- a dependent or otherwise invalid generic identifier expression.

Unauthorized runtime observation is not a bespoke escape error. Its value is
`Never`, and subsequent behavior follows the ordinary bottom-type laws.
Under the generic existential policy, an ineligible result contract is not
itself an error; it simply provides no elimination evidence, so the result
remains protected. If a contract is eligible but the produced value does not
validate against it, report the ordinary result-type mismatch before any
protection could be removed.

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
- Reject a generic name that overlaps an ordinary identifier introduced in
  either the domain or codomain scope, treating optional and required
  spellings of the same name as overlapping.
- For each dependent identifier in either scope, test the generic name against
  every fiber's string value and reject the function type if the generic name
  subtypes any one of them or if all-fiber disjointness cannot be established.
- Collect introductions without crossing nested function types.
- Normalize both regular and argument maps to a real generic prefix.
- Verify `(a : _T; b : &_T)` has prepared order `[_T; a; b]`.
- Verify `{Args (&_T :: IntLimit),}` has prepared order `[_T; Args _T]`.
- Permit alternating `&` and `^` binders and reject forward bound
  dependencies.

### Identifier and matching behavior

- Infer a private product in an argument map and insert it into the prefix.
- Infer the unique federation of all evidence for a private product; do not
  search for candidate witnesses or diagnose phantom inference ambiguity.
- Route missing values, out-of-bound evidence, and inconsistent dependent
  members through their ordinary matching and specification diagnostics.
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
  non-eliminated dependent products and ordinary prepared values.

### Scope-protection substrate

- Allocate distinct labels for repeated activations of the same lexical
  scope.
- Give every entered lexical scope exactly one activation label and derive the
  active label chain from scope ancestry, with no separate protection stack.
- Confirm that blocks, function bodies, domain and codomain evaluation,
  modules, and closure calls all use the same scope activation constructor.
- Confirm that function calls activate beneath the caller scope and that a
  captured lexical environment cannot reactivate an expired defining scope.
- Store the actual value, one introducing scope label, and a normalized
  nonempty policy set in each `ScopeProtected` value.
- Let descendants access a protected value by finding that label anywhere in
  their active scope ancestry, without adding child labels to the value.
- Refuse observation after the introducing scope has exited.
- Return `Never` without running the underlying operation when any protected
  operand's label is absent from the current scope ancestry.
- Combine different policy sets conservatively and require every participating
  policy to approve declassification or label transfer.
- Preserve an accepted wrapper across a boundary instead of permanently
  unwrapping it merely because its label remains active.
- Exercise the generic handoff stage with preservation, transfer, rejection,
  policy disagreement, an unprotected value, and an inaccessible source value.
- Confirm that a scope with no handoff stage grants no implicit transfer.
- Exercise a dummy non-existential policy to prove that the substrate does not
  grant generic-sum elimination or handoff behavior automatically.
- Keep lazy and captured computations from observing payloads after their
  introducing scopes have exited.

### Generic-sum existential protection

- Protect every generic sum witness with
  `GenericExistentialProtection` in the domain scope.
- Preserve protection through `actual := T` without a special alias branch.
- Protect conditional, map, access, function, closure, and other results when
  a protected operand is used and no protection-erasing result contract is
  available.
- Protect a dependent product such as `&U :: T` when evaluating or validating
  it consumes a protected `^T`; propagate that policy transitively through
  later telescope members.
- Confirm that product polarity alone does not protect an independent product.
- Require every protected operand's label to occur in the current scope
  ancestry, then either eliminate through a qualifying result contract or
  label the derived result only with the current scope label.
- Implement function return through the body scope's ordinary handoff stage
  and check preserved labels against the caller scope ancestry.
- Transfer protected results from ordinary nested continuation scopes back to
  an enclosing scope within the same existential lifetime.
- Reject a body-only protected result when the codomain does not accept
  `Never`.
- Permit that yield only when the codomain accepts `Never`, without exposing
  the actual protected payload.
- Permit a protected result whose introducing scope remains in the caller
  ancestry.

### Generic existential elimination

- Return an ordinary `Str` for authorized application of a protected
  `render : T -> Str` to a protected `x : T`, and permit that result to cross
  `yield` normally.
- Return ordinary `Bool` and concrete numeric results from typed comparison,
  equality, and arithmetic operators whose semantic result contracts qualify.
- Eliminate only after all protected operands, including operands with
  different active labels, have passed authorization.
- Permit a protected callable to eliminate through its ordinary qualifying
  codomain while the callable's label is active.
- Keep the result of `identity : T -> T` protected.
- Keep the result of `T -> Any` protected even when its actual value happens
  to specify to `Any`.
- Reject protection-erasing eligibility for a contract which is itself
  protected or depends on a protected binder.
- Reject protection-erasing eligibility for open or dependent containers,
  functions, closures, lazy results, and values with protected members.
- Confirm that aliasing, assignment, a target annotation, map construction,
  and `yield` do not eliminate protection by themselves.
- Use ordinary lifting for an operator which has no checked result contract.
- Validate and normalize the produced value against the eligible contract
  before returning it as ordinary.
- Keep an ineligible result protected so that it still becomes `Never` at an
  unauthorized function-body handoff.

### `Never` laws

- Resolve `Never` from `std.datra` and `datra.never` directly.
- Prove it is a subfederation of representative scalar, map, function, union,
  and meta types.
- Refute attempts to supply an ordinary inhabitant of `Never`.
- Refute projection of any member from `Never`.
- Render the canonical value as `Never`.
- Ensure equality or another operation on inaccessible protected values
  produces `Never` instead of leaking fallback equality.

### Required language interactions

Exercise clean and protected generics with:

- forward specification using `~>`;
- reverse specification using `<~`;
- subfederation using `of`;
- optional names independently from optional values;
- regular maps and argument maps;
- nested closures and recursive calls;
- mixed product/sum telescopes; and
- protected function application and typed primitive existential elimination.

## Completion criteria

The bootstrap is complete when:

1. `&` and `^` accept only unique simple identifiers parsed through the shared
   IdenExp rules, and those names are disjoint from every simple or dependent
   identifier introduced in the function type's domain and codomain scopes;
2. every owned generic becomes a real, ordered domain-prefix member;
3. mixed product/sum prefixes evaluate through one dependent-map engine;
4. private/public/optional-name matching follows the existing map rules;
5. domain evaluation through the shared operation cycle leaves independent
   products ordinary and protects products whose bounds or witnesses consume
   a protected sum, without a separate dependency pass;
6. the codomain runs in its own scope and receives only unprotected products
   as direct identifier bindings;
7. the body receives all prefix and ordinary members through names and full
   `it`;
8. lexical scope activation is the interpreter's only runtime scope mechanism:
   every active scope owns its bindings, label, parent, and optional handoff,
   and authorization derives from that scope ancestry rather than a parallel
   protection stack; each `ScopeProtected` value stores one actual value, one
   introducing label, and one normalized nonempty policy set;
9. every evaluator operation authorizes and unwraps protected operands through
   the common operation cycle, combines their policies conservatively, and
   asks every policy to approve declassification or transfer;
10. the generic existential policy protects `^` witnesses and all values
    derived from them, authorizes the domain-to-body handoff, and permits
    function application or typed primitive operators to eliminate that
    protection only through a validated protection-erasing result contract;
11. `Any`, dependent or open containers, closures, lazy results, annotations,
    and untyped operations cannot become generic-existential escape paths, and
    no generic-existential rule is implicitly granted to another policy;
12. inaccessible observation produces the canonical `Never` value, and the
    function-body scope's generic handoff stage consults every carried policy
    against the caller ancestry before codomain checking, preserving or
    transferring wrappers only when those policies permit it;
13. `Never` is available as `datra.never` and from `std.datra` and obeys the
    empty-federation laws;
14. `~>`, `<~`, `of`, optional names, nested scopes, closures, recursion, lazy
    evaluation, and mixed telescopes have focused regression coverage; and
15. the full non-Liquid test suite passes serially.
