# datra-haskell

Haskell implementation of Datra.

## LiquidHaskell model

The library mirrors the proof-bearing structures in [`datra.lean`](../datra.lean):

- `Dominion` carries the coherence proof for its `rank`/`unrank` partial
  bijection (the executable form of Lean's injective `rank` embedding).
- `DomanialInsertion` carries an executable left-inverse law, which proves the
  injectivity required by Lean's `Function.Embedding` morphisms.
- `Chain` carries position bounds, injectivity, and an executable inverse for
  surjectivity onto its initial ordinal segment. Its `Ordinal` representation
  is restricted to ordinals below omega^omega.

The general smart constructors (`dominion`, `domanialInsertion`, and `chain`)
require proof functions whose refinements are checked during compilation.
Finite `Data.Set`/`Data.Map` construction and the two ordinal facts already
proved in Lean (`Ordinal.type_sum_lex` and `Ordinal.type_nat_lt`) are the small,
explicit `assume` boundary because those library implementations are opaque to
LiquidHaskell.

## Build

Install GHC 9.4.7, Cabal, and an SMT solver such as Z3. Then run these commands
from this directory:

```sh
cabal update
cabal build all
cabal test all
```

The library enables the `LiquidHaskell` GHC plugin directly, so `cabal build`
fails on an unsatisfied coherence proof as part of the normal build.

Run the executable with:

```sh
cabal run datra-haskell
```
