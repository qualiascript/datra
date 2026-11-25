# Injective `val` Values

## Status

This is an implementation plan. The current string-oriented injectivity path
is a deletion target and its replacement is a true injected value.

The central change is to replace the string-oriented approximation in
`Evaluation/ToString/Injectivity.hs` with genuinely injective values. A `val`
family is valid only when its semantic result retains enough information to
recover the unique capture witness which produced it. Its canonical name is
then derived from that witness.

For example, the value selected by:

```datra
from 2 to 5
```

must be distinguishable as that particular range. Given its semantic value,
the declaration machinery must be able to recover the capture witness
`(2, 5)` and therefore the canonical name `from 2 to 5`. Merely rendering the
value as that text, or observing that the text looks unambiguous, is not an
injectivity proof.

This work is separate from `def` consistency. `def` constrains replacement of
an existing declaration; it says nothing about whether a `val` family is
one-to-one.

## What is broken today

The present code has several disconnected substitutes for the missing
invariant:

- `Evaluation/ToString/Injectivity.hs` switches on `ValueSemantics`, guesses
  exact strings and alphabets, and returns `ProvenInjectiveToString`. These
  properties concern rendered strings, not whether a declaration result has a
  unique source witness.
- Unknown string properties still produce a value named
  `ProvenInjectiveToString`; this layer lacks a proved/refuted/undecidable
  decision boundary.
- `ToStringAtlasMapFederation`, `ProvenInjectiveToString`, and
  `ToStringInverseDecision` make this guessed string conversion look like a
  federation insertion.
- `RuntimeFunctionInsertion` contains only `applyRuntimeFunction`. It has no
  inverse and therefore is not an insertion. In particular,
  `declarationFamilyFunction` in `Evaluation/Expression.hs` manufactures one
  around every dependent declaration family merely to expose its forward
  application.
- `canonicalValueMarker = "val"` records the internal `val` modifier on a
  declaration descriptor. It remains declaration metadata, while injectivity
  and canonical identity move to retained proof evidence.
- `dynamicDependentDeclarationNamedView` gives a `val` family an ordinal
  collection projection, but does not validate that the implementation is
  injective.
- `NonInjectiveDependentDeclaration` exists, and a test expects it for a
  constant dependent `val`, but no production path currently constructs this
  diagnostic. `DependentDeclarationInjectivityUndecidable` does not exist.

The result is that the code can attach canonical presentation without proving
that two captures cannot collapse to one semantic value.

## Required semantic invariant

For one prepared declaration branch, let:

- `C` be the federation of valid capture tuples;
- `name : C -> Str` evaluate the declaration name template; and
- `value : C -> V` evaluate its implementation.

A `val` declaration requires both maps to be genuine insertions:

```text
name^-1(name(c)) = c
value^-1(value(c)) = c
```

The equality here is semantic equality after removing presentation. References,
module paths, markers, or different renderings do not make equal results
distinct.

Once both insertions are proved, canonical naming is composition rather than a
separate heuristic:

```text
canonicalName     = name . value^-1
canonicalName^-1  = value . name^-1
```

Thus each admitted value has exactly one capture witness and exactly one
canonical declaration name.

For a range declaration, `value^-1` recovers the endpoints from the semantic
range. This is what makes `from 2 to 5` a canonical unique value. For:

```datra
val `constant %(_x : Int)` := 1
```

distinct captures produce the same semantic integer, so no such inverse can
exist and the declaration is refuted.

A singleton capture federation is trivially injective. A finite or infinite
family is never accepted because a sample happened to contain no collision.

## A true injected federation value

DatraTypes needs one general representation for the image of an evaluated
insertion, shared by all target types:

```haskell
data EvaluatedFederationInsertion = EvaluatedFederationInsertion
  { insertionSource :: InterpretedValue
  , insertionTarget :: InterpretedValue
  , applyInsertion :: InterpretedValue
      -> Either InterpretingError InterpretedValue
  , selectPreimage :: InterpretedValue
      -> Decision InterpretedValue
  }
```

The exact record is illustrative. Its constructor is restricted to proof
rules. A successful decision carries the usable forward map and inverse; a
refutation carries a collision; undecidable means that no implemented proof
rule applies.

The federation image can then be represented conceptually as:

```haskell
InjectedAtlasMapFederation source target insertion
```

It retains the source federation and the inverse instead of reducing the image
to an ordinary target value plus presentation text. Selection of an image
member must:

1. select the target member;
2. recover its unique source with the insertion inverse; and
3. verify that the recovered source belongs to the source federation.

This retained source identity is the important property. Rendering and
parsing may implement part of an insertion, but neither is proof by itself.

At the typed core, `DomanialInsertion` remains the law-carrying abstraction.
The evaluated wrapper is built from a typed insertion, structural composition,
or an exhaustive finite decision. Every constructed wrapper therefore has an
executable inverse.

## Decision rules

The decision procedure should be structural and shared by declaration values,
canonical strings, and native invertible functions:

- identity is injective;
- a singleton source is injective after its one result evaluates;
- composition of proved insertions is injective;
- product/record constructors are injective when all varying components retain
  their source discriminators;
- an `Either` image is injective when both branches are injective and their
  target images are disjoint;
- map, argumentative-map, expansion, coalization, concatenation, and ordinal
  families compose their existing federation structure rather than flattening
  it;
- a finite source may be checked exhaustively, producing either an exact
  inverse table or two distinct sources with a common target;
- an infinite primitive is accepted only with a structural insertion supplied
  by that primitive; it is never sampled;
- function application preserves injectivity only when the selected function
  carries a real forward/inverse insertion;
- any unsupported case is undecidable.

The existing concatenation collision analysis can become one rule of this
general decision. String alphabets and delimiter facts remain properties of a
target string federation; they are not injectivity evidence for its source.

## Preparing a dependent `val`

Validation belongs to semantic declaration preparation. Syntax rewriting may
see the source declaration, while the semantic canonical `val` descriptor and
materialized members become available after the proof is constructed.

For every prepared branch:

1. Evaluate capture schemas and construct `C` without erasing ordinal/product
   structure or capture witnesses.
2. Evaluate the name template pointwise and decide `name : C -> Str`.
3. Evaluate the implementation pointwise while retaining the same source
   witnesses, producing the semantic target federation `V`.
4. Decide `value : C -> V` using the shared insertion rules.
5. On success, construct the injected value and its composed canonical-name
   insertion.
6. Only then expose the canonical descriptor and concrete projection.

The `$val` marker remains the internal declaration-modifier tag. The proof
lives on the prepared declaration/image and travels with it through
`ScopedDependentDeclaration`, declaration layers, module preparation, imports,
aliases, and projections. Simple identifiers and complex dependent heads use
the same path.

Non-`val` declarations retain the same lookup machinery without requiring
their implementations to be injective.

### Functions and native bodies

Callability and injectivity are separate capabilities. An ordinary function
may always be invoked when its type permits it. A containing `val` may use that
call as injectivity evidence only if the chosen function also carries a real
insertion with an inverse.

A function body value has the existing `functionBodyType` (`FunctionBodyAST`).
That category type does not provide a function domain or codomain: the body
owns evaluation behavior and closure state, while applying a function
signature constructs the typed function. Signature application is the point
where compatible forward/preimage behavior becomes insertion evidence. In
particular, `datra.parse_natural_body` becomes the isomorphism
`_NaturalLiteral -> Nat` only after `std.datra` applies that signature to the
body. Its forward operation is total on `_NaturalLiteral` and recovers the
retained `Nat` witness rather than reparsing the rendered text.

Range constructors are the motivating native case: their insertion must be
able to recover the endpoints from the range value. A native or source
function without that capability is still callable, but a `val` depending on
it is undecidable unless another structural rule proves the whole expression.

`declarationFamilyFunction` must stop manufacturing a forward-only
`RuntimeFunctionInsertion`. Its normal invocation belongs on the ordinary
function path.

## Canonical strings after the change

Canonical string conversion becomes a client of true injected values:

```text
canonicalString : T -> Str
```

- strings use identity;
- an accepted `val` uses `name . value^-1`;
- structural values compose their components' insertions;
- primitive families provide typed render/decode insertions where those laws
  genuinely hold;
- syntax values require their parser-backed inverse plus an exact canonical
  round trip;
- a function or host value with no canonical insertion fails explicitly.

`_StrExpr T` is the target image of this insertion. Specification against it
recovers the unique source member through the generic preimage operation. The
generic image replaces `ToStringAtlasMapFederation` and the semantic-constructor
table.

## Diagnostics

The decision has exactly three outcomes:

- proved: retain the insertion and admit the `val`;
- refuted: emit the existing
  `NonInjectiveDependentDeclaration String`, ideally with two distinct capture
  witnesses and their shared semantic result;
- undecidable: emit a new
  `DependentDeclarationInjectivityUndecidable` diagnostic identifying the
  unsupported operation.

The undecidable outcome uses its own diagnostic. A collision is required for
`NonInjectiveDependentDeclaration`.

## Current architecture and ownership

The scope refactor changes where this evidence must be retained:

- `Scope` owns ordered `DependentDeclarationLayer`s.
- `ScopedDatraDependentDeclaration` retains the declaration together with its
  family and captured scopes.
- `PreparedModule` retains a declaration layer rather than flattening exports
  to a host map.
- syntax rewriting obtains declaration rules from those same scope layers.

The implementation should build on that structure. A new DatraTypes federation
insertion module should own decisions and composition; the current
`Evaluation/Expression.hs` declaration preparation path should consume it
until that responsibility is moved into a focused declaration-evaluation
module. `Scope` remains the single context and every declaration head uses the
same validation path.

## Removal plan

1. Introduce the general evaluated insertion decision and generic injected
   federation image, with no dependency on string rendering.
2. Give existing genuinely invertible primitives, especially range
   constructors, typed forward/preimage implementations.
3. Change dependent `val` preparation to decide and retain `value : C -> V`,
   then derive canonical naming from the proof.
4. Route canonical string conversion and `_StrExpr` through the generic image.
5. Remove the obsolete implementation completely:
   - delete `Evaluation/ToString/Injectivity.hs`;
   - delete `StringConversionProperties`, `ProvenInjectiveToString`, and
     `ToStringInverseDecision`;
   - delete `ToStringAtlasMapFederation` and its special cases in
     specification, projection, `Either`, access, and subfederation;
   - retain `$val` as declaration metadata, but remove every branch which
     treats that marker as sufficient injectivity or canonical-name evidence;
   - remove the forward-only `RuntimeFunctionInsertion` abstraction after real
     native insertions have migrated;
   - remove `CanonicalStringImplementation` where it is being used as alleged
     proof evidence; type-family routing may remain only as routing;
   - remove obsolete identifier-string projection primitives once their
     consumers use the generic injected image;
   - remove stale string-only injectivity diagnostics and tests.
6. Audit exports, locale entries, and comments and remove the semantic
   hardcoding table.

Land the generic proof path and switch its consumers in the same implementation
series, then delete `Injectivity.hs` and its representations.

## Tests

### Core insertion behavior

- identity and composition satisfy the executable left-inverse law;
- finite images construct exact preimages;
- finite collisions report both sources and their common target;
- infinite identity families are proved structurally;
- infinite constant families are refuted structurally;
- unsupported infinite transformations are undecidable;
- structural products, `Either`, maps, and concatenation preserve or reject
  insertions correctly.

### `val` behavior

- an `it`-preserving dependent family is accepted;
- a constant dependent family is rejected with
  `NonInjectiveDependentDeclaration`;
- syntactically different captures producing the same semantic result collide;
- `from 2 to 5` retains and recovers `(2, 5)` and has that canonical name;
- distinct range endpoints remain distinct canonical values;
- a proved native insertion is accepted;
- a forward-only or otherwise unsupported function is undecidable;
- singleton, finite, infinite, imported, aliased, nested, and complex-headed
  declarations preserve the proof evidence;
- ordinary non-`val` many-to-one declarations remain valid.

### Canonical strings and cleanup

- accepted values round-trip through their canonical declaration names by
  semantic equality;
- total and non-total values use the same insertion entry point;
- `_StrExpr` specification and subfederation recover source witnesses and
  terminate;
- values without a proven canonical insertion cannot enter `_StrExpr`;
- source search finds no `Evaluation.ToString.Injectivity`,
  `ToStringAtlasMapFederation`, alleged proof record, or dummy inverse, and no
  use of `$val` claims to be that proof.

## Completion criterion

The work is complete when `val` construction has exactly the three decision
outcomes above and only the proved outcome produces a canonical value. The
same retained inverse distinguishes values such as `from 2 to 5` and derives
their canonical names. The `$val` modifier identifies declarations requiring
this invariant; the retained insertion supplies the evidence.
