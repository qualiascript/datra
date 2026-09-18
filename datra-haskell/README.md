# datra-haskell

The Datra parser and interpreter are built with:

- GHC 9.14.1
- cabal-install 3.18.1.0

The ordinary `cabal.project` selects the repository-scoped GHC installation.
The Docker image uses `cabal.docker.project` instead, which selects the pinned
compiler and Cabal executable from the container. This prevents a host Cabal
or the repository-relative `../.tools` paths from affecting container builds.

## Build the Docker image

From this directory, run:

```sh
docker build --tag datra-haskell .
```

The build verifies both tool versions, builds the executable with the Liquid
Haskell flag enabled, and performs a CLI smoke test. The image supports Docker's
`amd64` and `arm64` platforms.

Verify the installed tools if needed:

```sh
docker run --rm --entrypoint cabal datra-haskell --version
docker run --rm --entrypoint ghc datra-haskell --version
```

## Run with the default files

The container works in `/data`, so Datra's normal defaults are:

- `input.datra`
- `output.datra.ast`
- `output.datra`

The repository's example files are in `resources`. Mount that directory and
run the image without arguments:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell
```

The user mapping makes the generated files belong to your host account.

To use another directory, place `input.datra` in it and mount it at `/data`:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "/absolute/path/to/files:/data" \
  datra-haskell
```

## Generate only an AST

Generate an AST from inline Datra source:

```sh
docker run --rm datra-haskell \
  ast --source '[1; 2 + 3]' --output -
```

Expected output:

```text
(<:> 1 (+ 2 3))
```

Generate an AST from a mounted source file:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell ast \
  --input input.datra \
  --output output.datra.ast
```

## Interpret an AST directly

Interpret inline canonical AST syntax:

```sh
docker run --rm datra-haskell \
  interpret --ast '(<:> 1 (+ 2 3))' --output -
```

Interpret a mounted AST file:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell interpret \
  --input output.datra.ast \
  --output output.datra
```

Add `--locale română` or `--locale english` to commands that interpret an AST.

## Use the image as a Cabal development environment

Open a shell with the repository mounted separately from `/data`:

```sh
docker run --rm --interactive --tty \
  --entrypoint bash \
  --volume "$PWD:/workspace" \
  --workdir /workspace \
  datra-haskell
```

Inside the container, use the Docker project file so Cabal does not read the
host-only compiler paths:

```sh
cabal build --project-file=cabal.docker.project all -fliquid -j1
cabal test --project-file=cabal.docker.project all -fliquid -j1
```

## Run locally without Docker

The repository-local toolchain remains available through the ordinary project
file:

```sh
cabal build all -fliquid -j1
cabal test all -fliquid -j1
cabal run -- \
  --input resources/input.datra \
  --ast-output resources/output.datra.ast \
  --output resources/output.datra
```
