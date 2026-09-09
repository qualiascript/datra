# datra-haskell

Haskell implementation of Datra.

## LiquidHaskell model

The library mirrors the proof-bearing structures in [`datra.lean`](../datra.lean):

- `Dominion` carries a total `rank` and a proof that `unrank (rank x)` returns
  `x` (the executable form of Lean's injective `rank` embedding).
- `DomanialInsertion` carries an executable left-inverse law, which proves the
  injectivity required by Lean's `Function.Embedding` morphisms.
- `Chain` carries position bounds, injectivity, and an executable inverse for
  surjectivity onto its initial ordinal segment. Its `Ordinal` representation
  is restricted to ordinals below omega^omega.

The general smart constructors (`dominion`, `domanialInsertion`, and `chain`)
require proof functions whose refinements are checked during compilation.
The two ordinal facts already proved in Lean (`Ordinal.type_sum_lex` and
`Ordinal.type_nat_lt`) are an explicit `assume` boundary. Finite
`Data.Set`/`Data.Map` construction is a separate trusted boundary enforced by
GHC's scoped carrier types, because those containers are opaque to
LiquidHaskell 0.9.4.

The separate `FiniteDominion` module turns a runtime `Set` into a scoped finite
carrier. Values must first pass through `finiteMember`; its rank has a bounded
`FiniteIndex`, and `finiteUnrank` is total on that type. The scope is
generative, so elements and indices from distinct finite carriers cannot be
mixed or escape the constructor's continuation.

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
