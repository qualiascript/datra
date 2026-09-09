# Planned Fixes

This document tracks the follow-up fixes identified during review of PR #7.

## 1. Make `Dominion.rank` total

### Problem

The Lean definition of `Dominion` uses a total injective ranking:

```lean
rank : Carrier ↪ Nat
```

Every value in the carrier therefore has a natural-number rank.

The Haskell version currently uses:

```haskell
rank :: a -> Maybe Natural
unrank :: Natural -> Maybe a
```

with a coherence condition equivalent to:

```text
rank x == Just n  <=>  unrank n == Just x
```

This does not require `rank x` to succeed for every `x`.

As a result, a degenerate implementation where both `rank` and `unrank` always return `Nothing` can satisfy the stated coherence property while failing to embed the carrier into `Natural`.

That means the current Haskell representation is closer to a partial bijection than to the total injection required by the Lean model.

### Planned fix

Prefer changing the representation to:

```haskell
rank :: a -> Natural
unrank :: Natural -> Maybe a
```

and require the round-trip law:

```text
unrank (rank x) == Just x
```

This directly expresses that `rank` is total and injective.

If keeping `rank :: a -> Maybe Natural` is important for another reason, add an explicit LiquidHaskell invariant proving totality:

```text
forall x. exists n. rank x == Just n
```

The total `a -> Natural` representation is preferred because it makes the intended semantics explicit in the Haskell type.

### Follow-up work

- Update `Dominion`.
- Update smart constructors such as `finiteSetDominion`.
- Update any functions that consume `rank`.
- Update LiquidHaskell refinements/proofs.
- Add tests demonstrating that every value in a finite dominion has a rank.
- Add a regression test preventing an all-`Nothing` dominion from satisfying the API contract.

### Acceptance criteria

- Every `a` represented by a `Dominion a` has a natural-number rank.
- `unrank (rank x) == Just x` is checked by LiquidHaskell.
- The Haskell semantics match the total-injection property of the Lean `Dominion`.
- Existing finite-dominion tests still pass.

---

## 2. Hide the raw `Ordinal` constructor

### Problem

`DatraOrdinal` currently exposes `Ordinal(..)`.

The implementation relies on ordinals being stored in a canonical coefficient representation, with leading zero coefficients removed. The smart constructor performs this normalization, but exporting the raw constructor allows callers to bypass it.

For example, external code can construct:

```haskell
Ordinal [0, 1]
```

instead of using:

```haskell
ordinal [0, 1]
```

The smart constructor can canonicalize the representation, while the raw constructor preserves the non-canonical list.

Because comparison and other ordinal operations depend on the internal coefficient representation, non-canonical values can violate assumptions used throughout the implementation.

### Planned fix

Make `Ordinal` abstract from public modules.

Change the public export from something like:

```haskell
Ordinal(..)
```

to:

```haskell
Ordinal
```

and require callers to construct ordinals through validated/smart constructors such as:

```haskell
ordinal
```

If internal modules such as `Chains` need access to the representation for LiquidHaskell proofs or pattern matching, move the constructor to an internal module, for example:

```text
DatraCore.DatraOrdinal.Internal
```

and expose only the abstract type and safe operations from the public module.

### Follow-up work

- Introduce an internal ordinal module if necessary.
- Stop exporting the raw constructor publicly.
- Audit current code for direct `Ordinal` construction.
- Route all construction through the smart constructor.
- Add tests covering canonicalization of leading-zero representations.
- Add property tests asserting equivalent coefficient lists normalize to equal ordinals.

### Acceptance criteria

- External users cannot construct a non-canonical `Ordinal`.
- All publicly constructible ordinals satisfy the representation invariant.
- Comparison and arithmetic only operate on canonical representations.
- Existing chain and ordinal behavior remains unchanged for valid inputs.

---

## 3. Strengthen ordinal and chain test coverage

### Problem

The current tests cover the basic happy path but do not exercise much of the semantic surface that the new core depends on.

Areas with limited coverage include:

- ordinal comparison;
- ordinal addition;
- ordinal subtraction;
- finite ordinal decoding;
- mixed finite/infinite ordinal cases;
- chain sums;
- insertion composition;
- opposite-category composition;
- round-tripping positions through chains;
- boundary positions around the left/right split in `sumChains`.

### Planned fix

Add property-based tests where practical.

Useful properties include:

```text
compare a b == EQ  =>  a == b
```

```text
objectAtPosition chain (chainPosition chain x) == Just x
```

```text
p < chainOrderType chain
=> fmap (chainPosition chain) (objectAtPosition chain p) == Just p
```

For sums:

```text
positions from the left chain are unchanged
```

```text
positions from the right chain are shifted by the left order type
```

```text
decoding around the sum boundary selects the correct side
```

For insertions:

```text
backward (forward x) == Just x
```

and verify that the property is preserved under composition.

### Acceptance criteria

- Core ordinal arithmetic has direct regression tests.
- Chain round-trip laws are tested.
- `sumChains` boundary behavior is tested.
- Domanial insertion composition is tested.
- Tests cover both finite and infinite-order-type examples.

---

## 4. Add CI for Haskell + LiquidHaskell verification

### Problem

PR #7 showed no GitHub checks.

Because LiquidHaskell proofs are intended to be part of the correctness story, contributors should not have to rely on local builds to know whether proof obligations still hold.

### Planned fix

Add a GitHub Actions workflow that runs the supported toolchain and verifies at least:

```bash
cabal build
cabal test
```

The workflow should use the GHC/LiquidHaskell versions supported by the project.

### Acceptance criteria

- Every PR touching the Haskell semantic core runs automated build and tests.
- LiquidHaskell failures fail CI.
- Runtime test failures fail CI.
- The supported GHC/LiquidHaskell versions are pinned or otherwise reproducible.

---

## Priority

Recommended order:

1. Fix `Dominion` totality.
2. Hide the `Ordinal` constructor.
3. Expand semantic/property tests.
4. Add CI enforcement.

The first two are correctness and abstraction-boundary issues. The latter two make those guarantees harder to regress.
