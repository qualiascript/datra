# Dependent Declaration Injectivity

## Status and scope

This document defines the injectivity law for dependent `val` declarations and
the federation machinery which proves, refutes, or declines to decide that law.
The same machinery owns canonical string images for every Datra value.

The design has three required outcomes:

1. A dependent `val` declaration is admitted only with a genuine proof that
   distinct capture members cannot evaluate to the same semantic value.
2. Canonical string conversion is an ordinary proven federation injection,
   including its executable inverse. It is not inferred from a table of
   `ValueSemantics` constructors.
3. The old string-specific proof representation, marker-based `val` handling,
   and unused diagnostics are removed rather than retained as compatibility
   paths.

`def` consistency is separate. It constrains replacement of an existing
binding; it does not prove that a declaration family is injective.

## Semantic law

For a prepared dependent declaration, let:

- `C` be the federation of valid capture tuples;
- `name : C -> Str` be the evaluated declaration-name template; and
- `value : C -> V` be the evaluated declaration implementation.

A `val` declaration requires both maps to be insertions over their admitted
federation members:

```text
name^-1(name(c)) = c
value^-1(value(c)) = c
```

Equality in this law is presentation-free semantic equality. It uses the same
identity as `interpretedSemanticResult`; an attached reference, import path, or
other presentation cannot make two equal results distinct.

The canonical presentation of a declared value is then the composition:

```text
canonicalName : image(value) -> image(name)
canonicalName = name . value^-1
```

Its inverse is:

```text
canonicalName^-1 = value . name^-1
```

Consequently, every canonical name identifies exactly one semantic value and
every value in the declaration image has exactly one canonical name.

For example:

```datra
val $!($pair; (_x : Int); $with; (_y : Int)) := it
```

is injective because the result retains the complete capture tuple. This is
not injective:

```datra
val $!($pair; (_x : Int)) := 1
```

Every capture maps to the same semantic integer. The declaration must be
refuted, even though each individual lookup can be evaluated.

Singleton capture federations are trivially injective. A non-singleton family
is never accepted merely because no collision was found in a sample.

## One federation-insertion abstraction

DatraTypes owns one evaluated insertion abstraction for all federation images.
Conceptually it contains:

```haskell
data EvaluatedFederationInsertion = EvaluatedFederationInsertion
  { federationInsertionSource :: InterpretedValue
  , federationInsertionTarget :: InterpretedValue
  , applyFederationInsertion
      :: InterpretedValue
      -> Either InterpretingError InterpretedValue
  , selectFederationPreimage
      :: InterpretedValue
      -> Decision InterpretedValue
  }
```

The constructor is not public. Callers receive an insertion only from a
federation decision:

```haskell
type FederationInsertionDecision =
  AtlasMapFederationDecision
    FederationInsertionRefutation
    FederationInsertionUncertainty
    EvaluatedFederationInsertion
```

`AtlasMapFederationProved` carries the usable forward map and partial inverse.
`AtlasMapFederationRefuted` carries a collision witness. An undecidable result
states that no implemented proof rule applies; it is not a weak proof and is
not reported as a demonstrated collision.

At the typed core, `DomanialInsertion` remains the law-carrying representation:

```text
preimage (applyInsertion source) = Just source
```

The evaluated wrapper erases the concrete witness types needed by the
interpreter, but it may only be constructed from typed insertions, structural
composition rules, or a complete finite decision. There is no public record
constructor that permits an arbitrary forward function to be paired with
`const Nothing`.

### Proof rules

The federation decision procedure is structural:

- identity is proved with the identity insertion;
- a singleton source is proved once its sole result is successfully evaluated;
- composition is proved by composing insertions and their preimages;
- a structural constructor is proved when its varying components retain a
  source discriminator and its component images cannot collide;
- `Either` is proved when both branches are injective and their target images
  are disjoint;
- sequential, expansion, coalization, map, argumentative-map, and
  concatenation cases reuse their ordinary federation construction rules;
- a function application preserves injectivity only when the selected function
  carries a proven federation insertion;
- a finite ordinal-indexed source may be decided completely by evaluating all
  members, comparing presentation-free results, and constructing the inverse
  from the resulting unique table;
- an infinite primitive family is handled only by a structural rule supplied
  by that primitive; it is never sampled;
- an unsupported operation is undecidable.

The existing concatenation collision logic becomes one rule of this general
image decision. It is no longer a string-only boolean exception layered over
the federation decision type.

## Injected federation images

An injective pointwise image is represented by a generic federation primitive,
not by a `ToString` primitive:

```haskell
InjectedAtlasMapFederation
  sourceFederation
  targetFederation
  insertion
```

The concrete representation may erase redundant fields, but it must retain:

- the source federation used to validate membership;
- the ordinary target federation used by access, specification, and
  subfederation;
- the insertion needed to recover the unique source witness.

Forward enumeration follows the source federation and applies the insertion.
Selection first selects a target member, then applies the insertion preimage,
then verifies that the recovered source belongs to the source federation.
This is the generic version of the provenance currently needed by string
federations.

String-language facts such as exact members, possible characters, and excluded
delimiters are properties of the target string federation. They are derived by
folding that federation's ordinary singleton, range, concatenation, and
primitive nodes. They are not fields on an alleged injectivity proof and are
not inferred by switching over unrelated source semantics.

## Validating a dependent `val` declaration

Validation happens after capture bounds and the declaration-name family have
been evaluated, but before the declaration is published into its scope.

For each prepared declaration branch:

1. Construct the capture federation `C` from the evaluated capture schemas.
   Preserve its ordinal/product structure and source witness at every member.
2. Evaluate the name template pointwise over `C`, producing the ordinary string
   federation `N`.
3. Ask the federation insertion procedure to decide `name : C -> N`.
   Exact template decoding supplies the inverse, but the inverse is accepted
   only when the federation decision establishes a unique semantic capture.
4. Evaluate the declaration implementation pointwise with each source witness
   as contextual `it`, producing the result federation `V` without erasing its
   source provenance.
5. Ask the same procedure to decide `value : C -> V`.
6. Compose the inverse of `value` with `name` and attach the resulting canonical
   string insertion to `V`.
7. Publish the descriptor and concrete lookup projection only after both
   decisions are proved.

A refuted value insertion produces `NonInjectiveDependentDeclaration` with two
distinct capture/name witnesses and their shared semantic result when the
decision procedure has concrete witnesses. An undecidable insertion produces a
separate `DependentDeclarationInjectivityUndecidable` diagnostic identifying
the unsupported operation. Unknown is never silently accepted and is never
misreported as a proven collision.

Non-`val` dependent declarations continue to use the same lookup and name
family machinery without requiring the implementation map to be injective.

### Function application

Ordinary function invocation and proof of injectivity are separate
capabilities. A declaration implementation may always invoke an ordinary
function when its type permits it, but the containing `val` is provable only if
that invocation also has a federation-insertion rule.

Native range constructors and other invertible hooks attach a real insertion.
An ordinary callable attaches no insertion. The declaration-family wrapper
must not manufacture an insertion merely to gain access to its forward call;
forward invocation goes through the ordinary function invocation path.

## Canonical string conversion

Canonical string conversion is defined as an injected federation image:

```text
canonicalString : T -> Str
```

Every conversion request goes through the federation insertion decision,
including total values. A total singleton is proved trivially, but it does not
bypass the common construction path.

The standard cases are:

- strings use the identity insertion;
- a proven `val` family uses its composed declaration-name insertion;
- structural values compose the canonical insertions of their components;
- built-in primitive families provide typed canonical insertions and inverses;
- syntax values use their parser-backed inverse and exact canonical
  round-trip check;
- functions or host values without a canonical insertion fail with
  `NoCanonicalStringConversion`;
- a conversion whose proof procedure is incomplete reports a distinct
  undecidable diagnostic.

`_StrExpr T` is the target string federation of this insertion. For non-total
`T`, the generic injected-image node retains `T` and its inverse. For total
`T`, the same operation yields a singleton string federation. Specification of
a string against `_StrExpr T` recovers a unique member of `T` through the
generic preimage operation.

Rendering and parsing are not themselves proofs. A renderer/parser pair is an
implementation candidate which becomes a canonical insertion only after the
federation rules establish its left-inverse law over the relevant source.
Returning several parse candidates is permitted during parsing, but successful
canonical selection must reduce them to exactly one semantic source member.

## Specification, subfederation, and termination

Injected images participate in the ordinary Datra type operations:

- specification selects the target member, reverses the insertion, and retains
  the source selection witness;
- `Image f S of Image f T` reduces to `S of T` only when both images carry the
  same insertion identity;
- images with different insertions compare through their ordinary target
  federations without assuming that equal target shapes imply equal sources;
- `_StrExpr S of _StrExpr T` follows from `S of T` when both use the canonical
  string insertion;
- optional names retain their named/unnamed source alternative through the
  inverse; they are not conflated with optional values;
- access and ordinal enumeration follow the target view while preserving the
  source witness in the selected member.

Each specification or subfederation rule unwraps at most one injected-image
layer before recurring. It must not reconstruct an image during the same
decision. This supplies the termination measure and prevents `_StrExpr`
comparison from cycling through canonical conversion.

## Ownership

Responsibilities are divided as follows:

- `DomanialInsertion` owns the typed forward/preimage law and its LiquidHaskell
  verification.
- `Evaluation.Federation.Insertion` owns evaluated insertion decisions,
  structural composition, finite completion, and collision witnesses.
- `Evaluation.Federation` delegates concatenation and other image-sensitive
  operations to that shared decision procedure.
- `Evaluation.DependentDeclaration` prepares capture/name/value federations and
  requires the `val` decisions.
- `Evaluation.ToString` is a thin client which asks for the canonical string
  insertion and constructs its injected target image.
- primitive evaluation modules own the canonical insertions for their values.
- the application parser owns syntax-value decoding; it does not own the
  injectivity decision.
- DatraLanguage owns declaration syntax and diagnostics, not runtime proof
  records or presentation algorithms.

No DatraTypes injectivity module imports AST operators, reserved spellings, or
concrete-syntax strings to approximate the language of rendered values.

## Required simplification

The implementation removes the superseded paths completely:

- delete `Evaluation.ToString.Injectivity`;
- delete `ProvenInjectiveToString` and `ToStringInverseDecision`;
- replace `ToStringAtlasMapFederation` with the generic injected federation
  image;
- remove `StringConversionProperties`, semantic-constructor alphabet tables,
  exact-string tables, and their delimiter heuristics from the source side;
- remove `CanonicalStringImplementation` and its family tags as purported
  proof evidence; a Datra type family routes operations, while an evaluated
  insertion proves a particular conversion;
- remove the `$val` trailing string marker, `canonicalValueMarker`, and all
  import/export branches which infer canonical behavior from that marker;
- carry canonical presentation as a typed insertion capability on the
  declaration image and through module exports;
- remove the declaration-family `RuntimeFunctionInsertion` whose preimage is
  `const Nothing`;
- remove `RuntimeFunctionInsertion`; ordinary calls use the existing invocation
  capability, while range constructors and other invertible functions migrate
  their forward/preimage pairs to evaluated federation insertions;
- replace `IdentifierStringProjectionForm`,
  `IdentifierStringProjectionSemantics`, and
  `IdentifierStringProjectionAtlasMapFederation` with the generic canonical
  string image;
- move `NonInjectiveDependentDeclaration` out of syntax-rewrite failures and
  produce it from declaration evaluation;
- add the distinct undecidable declaration diagnostic;
- delete the unused `NonInjectiveStringInterpolation`; interpolation collisions
  use the ordinary federation refutation/uncertainty diagnostics;
- remove special-case inverse selection for `ToStringAtlasMapFederation` from
  string specification, `Either`, projection, subfederation, and access
  modules;
- remove exports, localized messages, tests, and comments which refer to the
  deleted representations.

There is no compatibility constructor and no fallback to the semantic
hardcoding table.

## Required tests

### Federation insertion

- identity and composition satisfy the executable left-inverse law;
- finite images construct exact preimages;
- finite collisions return both distinct sources and the common target;
- infinite identity families are proved structurally;
- infinite constant families are refuted structurally;
- unsupported infinite transformations are undecidable;
- `Either`, concatenation, map, and argumentative-map composition preserve or
  reject insertions correctly.

### Dependent declarations

- `val pair (_x : Int) with (_y : Int) := it` is accepted;
- `val pair (_x : Int) := 1` is rejected as non-injective;
- two syntactically different captures with equal semantic results still
  collide;
- an implementation using a proven native insertion is accepted;
- an implementation using an ordinary unproved function is undecidable;
- singleton, finite, infinite, optional-name, optional-value, imported, and
  nested declaration families retain the required behavior;
- ordinary non-`val` declarations remain valid when many-to-one;
- specification and `of` involving declared canonical values preserve source
  witnesses and terminate.

### Canonical strings

- every built-in canonical insertion round-trips each representative source
  member by semantic equality;
- every accepted `val` value round-trips through its declaration name;
- total and non-total values use the same insertion entry point;
- strings use identity without adding source delimiters as data;
- ambiguous parser candidates are reduced to one semantic source or rejected;
- `_StrExpr` specification, subfederation, concatenation, and delimiter
  decisions operate on the generic target federation;
- a value without a proven canonical insertion cannot enter `_StrExpr`;
- no test relies on a global parse candidate list as proof of injectivity.

### Cleanup

Source searches must find no remaining references to the deleted module,
proof records, `ToString` federation primitive, `$val` marker, dummy preimage,
or stale diagnostics. Focused tests cover each new proof rule; the final suite
runs with LiquidHaskell disabled, and the `DomanialInsertion` laws are verified
separately with LiquidHaskell.

## Completion criteria

The design is complete when dependent declaration construction has exactly
three outcomes—proved, refuted with a collision, or undecidable—and only the
proved outcome can publish a `val`. The resulting proof must be the same
evidence used to invert that declaration's canonical string conversion. No
module may claim injectivity from a constructor tag, a marker string, a
renderer alone, a parser alone, finite sampling of an infinite family, or an
inverse which does not recover every admitted source member.
