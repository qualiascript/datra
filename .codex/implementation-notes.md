# Internal implementation notes

These details were removed from the public READMEs. They are retained here for
local development context.

## Canonical function reconstruction

Function values render as executable Datra. Referenced definitions are rebuilt
recursively in nested blocks, including standard-library dependencies down to
their external registrations. Selected module members are reconstructed without
importing the whole module. Syntax adapters use the private `_AST` binding.

Canonical dependency declarations use quoted generated names so identifiers
with spaces, dots, or leading underscores remain representable. Reconstruction
tests cover text stability, canonical identity, and application without an
implicit standard-library scope.

Recursive closure source now emits `yield fun ...`; `fun` binds its own value to
`this` without providing the block-wide early-binding behavior of `let`.

## Local checks

The repository-local toolchain is selected by `cabal.project`:

```sh
make check
make coverage
```

Containers and CI can use:

```sh
make check CABAL_PROJECT=cabal.docker.project
```

## Documentation build details

The preprint LaTeX is embedded in `datra.lean`. `make blueprint` extracts it to
`datra-docs/preprint.tex`. The first PDF build installs the pinned Tectonic
engine and TeX packages under `.tools/tectonic`; later builds reuse that cache.
`make setup-tex` installs only the engine, and `make preprint_full` includes the
Lean formalization appendix.
