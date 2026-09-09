# DatraCore Data Architecture — Agent Guide

This document is a working map for agents changing `datra-haskell`. It explains
how DatraCore organizes data, which invariants are encoded in each type, and how
the current Haskell implementation corresponds to the formal model in
[`../datra.lean`](../datra.lean).

This is a living document and must be updated continuously as DatraCore evolves.
Any change that adds, removes, or materially alters a core representation,
invariant, public abstraction boundary, verification guarantee, or correspondence
with `datra.lean` should update this guide in the same change. Agents should verify
the guide against the code before relying on it and leave it more accurate than
they found it.

## Architectural summary

DatraCore models data by separating **values**, **ways of locating values**, and
**ways of organizing locations**:

1. A **dominion** is a countable carrier. Every value has a stable natural-number
   rank and can be recovered from that rank.
2. A **finite dominion** turns a runtime finite set into a scoped carrier whose
   membership and bounded indices cannot be mixed with those of another set.
3. A **domanial insertion** is an injective map between carrier types, represented
   by a forward function plus an executable partial inverse.
4. An **ordinal** is a canonical position below `omega^omega`.
5. A **chain** is a carrier put in bijection with the initial segment below one of
   those ordinals. Chain order is therefore derived from position rather than
   stored separately.
6. A **consolidation** is a monotone, point-surjective map between chain
   carriers. A chosen preimage makes point-surjectivity executable.

These pieces are the executable foundation of the larger organization in
`datra.lean`: chains index pages, page cells carry dominions, and compatible
insertions relate those cells inside atlases. The Haskell package does **not** yet
implement that entire tower. It currently stops at consolidations between chains.

## Module and trust boundaries

Each core concept normally has a public facade and a hidden implementation:

```text
src/DatraCore/
├── DatraOrdinal/
│   ├── DatraOrdinal.hs       public opaque API
│   └── Internal.hs           representation and ordinal arithmetic
├── Dominion/
│   ├── Dominion.hs           public opaque API
│   └── Internal.hs           rank/unrank representation
├── FiniteDominion/
│   ├── FiniteDominion.hs     public scoped API
│   └── Internal.hs           maps, witnesses, and phantom scope
├── DomanialInsertion/
│   ├── DomanialInsertion.hs  public opaque API
│   ├── Internal.hs           composition and opposite category
│   └── LiquidInternal.hs     LiquidHaskell-checked representation
├── Consolidation/
│   ├── Consolidation.hs      public opaque API
│   ├── Internal.hs           sums, categories, and opposite category
│   └── LiquidInternal.hs     refined representation and core operations
└── Chains/
    ├── Chains.hs             public opaque API
    └── Internal.hs           positions, lookup, sums, and spine
```

The package exposes the short module names (`Dominion`, `Chains`, and so on), not
names prefixed with `DatraCore`. Constructors remain absent from the public export
lists. Treat the public modules as the abstraction boundary: construct values with
their smart constructors instead of importing an `Internal` module or assembling
proof fields manually.

LiquidHaskell refinements hold laws that ordinary Haskell types cannot express.
Their runtime witnesses have type `()`: the useful information is checked
statically and then erased. This means a proof callback is not ordinary runtime
validation. In particular, passing `const ()` is sound only where LiquidHaskell
can establish the refinement or where the module explicitly declares an assumed
implementation.

`DomanialInsertion` has an extra `LiquidInternal` layer because the supported
LiquidHaskell version cannot parse refinements for the symbolic `Category` method
`(.)`. The representation and smart constructor are checked there; identity,
composition, and the category instances are derived in `Internal.hs`.

`Consolidation` uses the same split. Its abstract refinements stand for the source
and target chain orders without adding them to the runtime representation.
The representation, smart constructor, composition, and identity's law witnesses
are checked. The identity packaging contract is kept beside the datatype and
explicitly assumed: LiquidHaskell 0.9.4 both mis-serializes that abstract-refined
contract across modules on a cold build and crashes when it solves the packaged
identity and composition contracts together. Its checked witnesses use identity
for both maps, making monotonicity and the right-inverse law immediate.

## Data representations and invariants

### Ordinals: canonical structural positions

`Ordinal` stores a finite list of natural coefficients in Cantor normal form,
highest power first. For example:

- `ordinal []` is zero.
- `finiteOrdinal 3` is `3`.
- `omega` has coefficients `[1, 0]`.
- A longer coefficient list denotes a higher leading power of omega.

The smart constructor removes leading zero coefficients, so zero has one canonical
representation and comparison can first compare list length, then coefficients
lexicographically. Every finite coefficient list denotes an ordinal below
`omega^omega`; the finite list is the computational counterpart of the bound proved
for Lean chains.

Ordinal addition is directional and generally noncommutative. `subtractOrdinal a b`
means “remove the left ordinal prefix `a` from `b` when possible”; it is designed
primarily to decode positions in a chain sum, not as integer subtraction.

### Dominions: countability with executable recovery

```haskell
Dominion a
  { rank   :: a -> Natural
  , unrank :: Natural -> Maybe a
  , dominionCoherence :: a -> ()
  }
```

The refinement on `dominionCoherence` establishes:

```text
unrank (rank x) == Just x
```

Consequently, `rank` is injective. `unrank` is partial because most naturals need
not name an element of the carrier. A `Dominion a` does not own or store all `a`
values; it stores the countable addressing scheme for carrier type `a`.

`CountableSet a` and `embed` deliberately expose only the enumerating direction,
`Natural -> Maybe a`. They are the Haskell-level operational view of forgetting a
dominion's proof structure.

### Finite dominions: membership tied to one carrier

A `FiniteDominion scope a` stores the same finite carrier in two synchronized maps:

```text
rank -> value
value -> rank
```

Ranks are assigned from `Set.toAscList`, so they are dense from zero and stable for
the set's `Ord` ordering. `finiteCardinality` is the size of both maps.

The `scope` parameter is a generative phantom identity introduced by
`finiteSetDominion` through a rank-2 continuation. It prevents evidence produced
for one runtime set from being reused with another set, even when both contain the
same Haskell element type.

- `FiniteElement scope a` is a value known to belong to that exact carrier.
- `FiniteIndex scope a` is a natural rank known to be in bounds for that carrier.
- `finiteRank` and `finiteUnrank` are total between those evidence-bearing types.
- `finiteMember` and `finiteIndex` are the checked gateways from untrusted values.
- `finiteAsDominion` forgets finiteness while retaining the scoped element type and
  the rank/unrank round trip.

This module is an implementation aid rather than a directly named structure in
`datra.lean`. It packages a common way to build examples of Lean's countable
dominions without allowing runtime membership facts to leak across carriers.

### Domanial insertions: injectivity represented constructively

```haskell
DomanialInsertion a b
  { applyInsertion       :: a -> b
  , preimage             :: b -> Maybe a
  , insertionLeftInverse :: a -> ()
  }
```

The checked law is:

```text
preimage (applyInsertion x) == Just x
```

This is stronger operational data than a bare assertion that the forward function
is injective: it also supplies a computable inverse on the image. Composition
composes both forward maps and partial preimages, preserving the law.

`CodomanialInsertion a b` is the categorical opposite. Its stored value is a
`DomanialInsertion b a`; `op` and `unop` reverse only the type-level direction, not
the underlying computation.

Unlike Lean's `DomIns`, the Haskell type represents a morphism directly over carrier
types. The `Dominion` dictionaries for `a` and `b` are not fields of the insertion.
Code that needs both countability and insertion must carry both values explicitly.

### Chains: ordered data through ordinal addressing

```haskell
Chain object
  { chainOrderType          :: Ordinal
  , chainPosition           :: object -> Ordinal
  , chainObjectAt           :: Ordinal -> Maybe object
  , chainPositionBelow      :: object -> ()
  , chainPositionInjective  :: object -> object -> ()
  , chainPositionSurjective :: Ordinal -> ()
  }
```

Together, the proof fields say that `chainPosition` is a bijection between the
object carrier and the ordinals strictly below `chainOrderType`. The linear order is
therefore normalized into one coordinate system:

- `compareInChain` compares ordinal positions.
- `hasArrow chain source target` is true exactly when `source <= target` in that
  order, reflecting that a chain is a thin ordered category.
- `chainObjectAt` is partial outside the chain's initial segment.

`sumChains left right` uses `Either left right` as the object carrier. Left objects
retain their positions; right objects are offset by the left order type. The result
uses ordinal addition, so order and summand direction matter.

`spine` is the canonical `Chain Natural` with order type `omega`. It gives Datra's
eventual page system its natural-number axis.

At present, LiquidHaskell is instructed to assume the contracts for `sumChains` and
`spine`; their implementations are executable and covered by tests, but their full
refinement proofs have not yet been discharged. Agents should preserve this
distinction when describing verification coverage.

### Consolidations: monotone point-surjections

```haskell
Consolidation source target
  { applyConsolidation              :: source -> target
  , consolidationPreimage          :: target -> source
  , consolidationMonotone          :: source -> source -> target
  , consolidationPointSurjective   :: target -> ()
  }
```

A consolidation is used with a source and target `Chain`. Its laws require the
object map to preserve their order and the chosen preimage to be a right inverse
of the object map. The latter is executable evidence of Lean's
`Function.Surjective` field. `composeConsolidations` composes object maps and
preimages, while `sumConsolidations` is the componentwise map on `Either` matching
Lean's `ConHom.sum`.

The monotonicity witness returns the mapped right object, refined both to follow
the mapped left object and to equal the result of the consolidation's object map.
The smart constructor's monotonicity callback receives the source-left object,
its mapped target value (a ghost argument needed by LiquidHaskell 0.9.4), and the
source-right object.

`Coconsolidation` is the categorical opposite (`CoCon` in Lean). As with domanial
insertions, the carrier types stand for the separately supplied chain values; the
chains are not stored inside each morphism.

LiquidHaskell checks the representation, smart constructor, identity, and
composition. These checks cover both the abstract monotonicity law and the
right-inverse law. `sumConsolidations` and the category instances remain
executable and runtime-tested, but their full refinement proofs have not yet been
discharged.

## Correspondence with `datra.lean`

The Lean file is the semantic source of truth. Haskell changes may choose a more
executable representation, but should preserve the corresponding mathematical
meaning.

| Lean concept | DatraCore counterpart | Representation choice |
| --- | --- | --- |
| `Dominion` / `Dom` | `Dominion a` | Lean stores a carrier and an embedding into `Nat`; Haskell places the carrier in `a` and represents the embedding by `rank` plus a partial inverse and round-trip law. |
| `Emb : Dom ⥤ Type` | `embed :: Dominion a -> CountableSet a` | Both forget proof-bearing dominion structure. Lean returns the underlying type; Haskell exposes an executable enumeration because the carrier is already the type parameter. |
| `DomIns` morphism (`Function.Embedding`) | `DomanialInsertion a b` | A forward function and verified left inverse constructively establish the same injectivity. Haskell does not wrap dominions as category objects. |
| `CoDomIns := Opposite DomIns` | `CodomanialInsertion a b` | Both reverse morphism direction while retaining the underlying insertion. |
| `Chain` | `Chain object` | Lean stores `Obj`, a linear well-order, and a proof about its order type. Haskell stores a concrete bijection between `object` and a bounded ordinal initial segment. |
| `Chain.sum` | `sumChains` | Lean uses the lexicographic order on `Sum`; Haskell uses `Either` and offsets right-hand ordinal positions. |
| `Spine` | `spine` | Both have natural-number objects and order type `omega`. |
| ordinals below `omega^omega` | `Ordinal` | Lean uses Mathlib ordinals and propositions; Haskell uses finite canonical Cantor-normal-form coefficients. |
| `ConHom` / `Con` | `Consolidation source target` | A monotone object map plus an executable chosen preimage and law witnesses represents Lean's point-surjective functor. |
| `ConHom.sum` | `sumConsolidations` | Both map independently over the left and right summands. |
| `CoCon` | `Coconsolidation` | Both reverse morphism direction while retaining the underlying consolidation. |
| `Tra.map` | `applyConsolidation` | Both expose the underlying set-theoretic surjection. |

The next unimplemented Lean layer defines `Folio`. DatraCore also does not yet
implement `Pag`, `Atl`, atlas
transposals/traversals, stable atlas families, coalitions, or data transformations.
Those later definitions should not be collapsed into the current `Chain` or
`Dominion` types.

The intended progression in Lean is:

```text
countable carrier (Dominion)
        +
injective carrier maps (DomIns)
        +
ordinal page shape (Chain / Con)
        |
        v
eventually stable page index (Folio)
        |
        v
page cells as a category of elements (Pag)
        |
        v
each cell carries a Dominion, related by insertions (Atl)
```

The current Haskell code implements the inputs through `Con` in that progression.

## Guidance for changes

- Preserve opacity. Add safe operations to a public module instead of exporting an
  internal constructor.
- Decide whether a new fact is runtime data or a refinement law. Do not turn erased
  `()` witnesses into ad hoc Boolean checks without reconsidering the API.
- Keep carrier identity in the type system. In particular, do not remove the
  generative `scope` from finite dominions or weaken its nominal role.
- Use ordinal operations for chain layout; do not infer chain semantics from a
  Haskell `Ord object` instance.
- Remember categorical direction. Insertions go forward; codomanial insertions wrap
  the reverse direction; arrows in a chain go from lesser to greater positions.
- When porting another Lean definition, document both its semantic counterpart and
  any stronger executable structure introduced by Haskell.
- Update verification claims precisely. GHC type checking, runtime tests, checked
  LiquidHaskell refinements, and explicitly assumed LiquidHaskell contracts are
  different guarantees.
