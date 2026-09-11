# datra-haskell

The Haskell implementation of Datra's data-transformation model.

The library has one public entry point:

```haskell
import DataTransformations
```

LiquidHaskell verification is enabled by default:

```console
cabal test
```

For a faster ordinary GHC build without refinement checking:

```console
cabal test --flags=-liquid
```
