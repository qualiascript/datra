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
yield factorial 5' \
  --ast-output /dev/null \
  --output -
```

Expected output:

```text
120
```

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
