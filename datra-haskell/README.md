# datra-haskell

The Datra parser and interpreter are built with:

- GHC 9.14.1
- cabal-install 3.18.1.0
- Z3 (the SMT solver used by Liquid Haskell)

The ordinary `cabal.project` selects the repository-scoped GHC installation.
Both Docker targets use `cabal.docker.project` instead, which selects the pinned
compiler and Cabal executable from the container. This prevents a host Cabal
or the repository-relative `../.tools` paths from affecting container builds.

## Download and install the latest production image

To run Datra without compiling it, use the prebuilt release image. You need
Docker and curl; you do not need a repository checkout or a Haskell toolchain.

[Download the latest production image](https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz)
or run:

```sh
mkdir -p dist
curl --fail --location \
  https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz \
  --output dist/datra-prod.tar.gz && \
  sudo docker image load --input dist/datra-prod.tar.gz
```

This loads `datra-haskell:prod` into your local Docker image store. Continue
with [Run the whole pipeline](#run-the-whole-pipeline) below. If your account
can access Docker directly, omit `sudo`; otherwise use `sudo docker` in the
run commands too. Check the release notes for the supported platform.

The latest release must contain an asset named exactly `datra-prod.tar.gz`.
Publish each new production image under that same asset filename so this
link continues to work. The `&&` runs the Docker load only if the download
succeeds. Repeat these commands to install a newer release.

## Build development and production images

The images have separate targets and tags:

| Target | Image tag | Purpose |
| --- | --- | --- |
| `development` | `datra-haskell:development` | Full toolchain for building, testing, and interactive development |
| `prod` (default) | `datra-haskell:prod` | Slim runtime for running the Datra CLI |

From this directory, build both images:

```sh
make docker-images
```

Or build them individually with Docker:

```sh
docker build --target development --tag datra-haskell:development .
docker build --target prod --tag datra-haskell:prod .
```

The equivalent Make targets are `make docker-development` and
`make docker-prod`. Production is the default Docker stage and the default
Make target. Use the explicit tags above to keep the two images separate.

The multi-stage build verifies the toolchain and SMT solver, builds the
executable with the Liquid Haskell flag enabled, and strips the executable.
The default image uses Debian Bookworm slim and contains only Datra, its system
runtime libraries, and license notices. GHC, Cabal, Z3, sources, and build caches
stay in the build stage. CLI smoke tests run in the final runtime image. The
image supports Docker's `amd64` and `arm64` platforms.

This reduces the size of the image you distribute and download. A first build
from source still downloads the Haskell toolchain and compiles dependencies
with Liquid Haskell verification; subsequent builds reuse Docker's cached
dependency layer when the package metadata is unchanged. Build once and push
the resulting runtime image to your registry to let other machines pull it
without compiling it themselves.

Compare the local image sizes (in bytes):

```sh
docker image inspect datra-haskell:development datra-haskell:prod \
  --format '{{join .RepoTags ", "}}: {{.Size}} bytes'
```

## Run the whole pipeline

The `build` command parses and interprets Datra source. After downloading or building the
production image, run the whole pipeline and print only the final result:

```sh
docker run --rm datra-haskell:prod build \
  --source '[1; 2 + 3]' \
  --output -
```

The `--output -` option
prints the interpreted result to the terminal:

```text
[1; 5]
```

### Also display the AST

Use `--ast-output -` to print the AST before the final result:

```sh
docker run --rm datra-haskell:prod build \
  --source '[1; 2 + 3]' \
  --ast-output - \
  --output -
```

Expected output:

```text
(<:> 1 (+ 2 3))
[1; 5]
```

### Read and save files

The production container works in `/data`, so Datra's normal defaults are:

- `input.datra`
- `output.datra.ast`
- `output.datra`

From this directory, create an example input and run the whole pipeline,
saving both outputs to the host:

```sh
mkdir -p resources
printf '%s\n' '[1; 2 + 3]' > resources/input.datra

docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data:Z" \
  datra-haskell:prod build \
  --input input.datra \
  --ast-output output.datra.ast \
  --output output.datra

cat resources/output.datra.ast
cat resources/output.datra
```

This writes `(<:> 1 (+ 2 3))` to `resources/output.datra.ast` and `[1; 5]`
to `resources/output.datra`. The input creation step replaces
`resources/input.datra`; skip it to use your own source file.

The user mapping makes the generated files belong to your host account. The
`:Z` mount option labels the example directory for container access on
SELinux systems such as Fedora. If Docker requires administrator access,
use `sudo docker run` in place of `docker run`.

Running the image without a command or arguments performs the same pipeline
using the default filenames above.

To use another directory, place `input.datra` in it and mount it at `/data`:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "/absolute/path/to/files:/data" \
  datra-haskell:prod
```

## Generate only an AST

Generate an AST from inline Datra source:

```sh
docker run --rm datra-haskell:prod \
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
  datra-haskell:prod ast \
  --input input.datra \
  --output output.datra.ast
```

## Interpret an AST directly

Interpret inline canonical AST syntax:

```sh
docker run --rm datra-haskell:prod \
  interpret --ast '(<:> 1 (+ 2 3))' --output -
```

Interpret a mounted AST file:

```sh
docker run --rm \
  --user "$(id -u):$(id -g)" \
  --volume "$PWD/resources:/data" \
  datra-haskell:prod interpret \
  --input output.datra.ast \
  --output output.datra
```

Add `--locale romanian` or `--locale english` to commands that interpret an AST.

## Use the development image

Build the optional `development` target to include GHC, Cabal, Z3, and the build
caches. This image is larger than the default runtime image:

```sh
docker build --target development --tag datra-haskell:development .
docker run --rm --entrypoint cabal datra-haskell:development --version
docker run --rm --entrypoint ghc datra-haskell:development --version
docker run --rm --entrypoint z3 datra-haskell:development --version
```

Open a shell with the repository mounted separately from `/data`:

```sh
docker run --rm --interactive --tty \
  --entrypoint bash \
  --volume "$PWD:/workspace" \
  --workdir /workspace \
  datra-haskell:development
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
