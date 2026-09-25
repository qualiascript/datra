# datra-haskell

The Haskell implementation of Datra. The supported distribution is the
`datra-haskell:prod` Docker image.

## Install the release image

You need Docker and curl, but not a Haskell toolchain:

```sh
mkdir -p dist
curl --fail --location \
  https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz \
  --output dist/datra-prod.tar.gz && \
  sudo docker image load --input dist/datra-prod.tar.gz
```

This installs the image as `datra-haskell:prod`. Omit `sudo` when your account
can access Docker directly.

## Build the images from source

From this directory:

```sh
make docker-images
```

This creates:

- `datra-haskell:prod`, the small runtime image
- `datra-haskell:development`, the image containing GHC, Cabal, Z3, and the
  source tree

Build just one with `make docker-prod` or `make docker-development`.

## Run Datra

Recursive declarations use `let`, which makes the name visible throughout its
block:

```sh
docker run --rm datra-haskell:prod build \
  --source 'let factorial := ({n? : Int} -> Int do
  yield if n = 0 then 1 else n * factorial (n - 1))
assert factorial 5 = 120' \
  --ast-output /dev/null \
  --output -
```

Expected output:

```text
()
```

The CLI defaults to development mode, where `assert` is evaluated. Use
`--mode prod` to omit ordinary assertions. `assert hard ...` is always
evaluated.

To work with files, mount a directory at `/data`:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data:Z" \
  datra-haskell:prod build \
  --input input.datra \
  --ast-output output.datra.ast \
  --output output.datra
```

Use the `ast` command to generate canonical AST notation and `interpret` to
evaluate an existing AST file. Pass `-` as an input or output path for standard
input or standard output.

## Canonical function source

Function values render as executable Datra. Referenced definitions are rebuilt
recursively in nested blocks, including standard-library dependencies down to
their `external` registrations. Selected module members are reconstructed without
an import of the whole module. Recursive functions use `let`.

Reconstruction reads primitive definitions from `lib/std.datra` and retains
module origins on imported bindings. Syntax adapters use the private `_AST`
binding; it is not exported by `Std` or implicitly imported into user programs.

For example, a dependency on `Int` is declared as:

```datra
"___Std.Int" : (external "datra.Int")
```

The reference `this."___Std.Int"[1]` denotes its bound value. This canonical
reference form also supports identifiers containing spaces or dots, bypassing
bare-symbol restrictions. No additional `_dependency0_0` alias is needed. Extra
leading underscores distinguish nested dependency levels. A reconstructed
user-origin name is encoded by prepending `_`, then adding the level's `L + 2`
scope underscores. At level zero, `abc` becomes `"___abc"`, `_abc` becomes
`"____abc"`, and `_____abc` becomes `"________abc"`. Original underscores are
never stripped. This applies to standard-library dependencies too.

Generated recursive bindings follow the same rule: `let "__fun" : ...`
is referenced as `this."__fun"[1]`, including in recursive calls and the
final `yield`. Internal names at level `L` have `L + 2` leading underscores:
`"__fun"`, `"___fun"`, `"____fun"`, and so on. Generated names
are checked against declarations and one another, since a user can also declare
an identical quoted name, or a name matching an internal name at a deeper level.
When a reconstruction block is read back, its user-name marker and scope prefix
are decoded together; serializing again does not accumulate underscores.
Observable parameter names and map fields retain their original labels.

Computed positional access selects a declaration before evaluating its value:

```datra
x : 2
y : 3
z : this[y-x][1]
yield z
```

This returns `3`; `this[y-x][0]` returns the identifier name, displayed as `$y`.
Standalone `this` still denotes
the block's declaration map.

The function reconstruction tests check text stability, canonical identity, and
application after reconstruction without an implicit standard-library scope.
These checks are not a proof of canonicity for every Datra type.

## Development checks

The repository-local toolchain is selected by `cabal.project`:

```sh
make check
make coverage
```

Containers and CI use the portable project file:

```sh
make check CABAL_PROJECT=cabal.docker.project
```

## License

Licensed under the [Apache License 2.0](LICENSE). Distributions and derivative
works must preserve the attribution in [NOTICE](NOTICE).
