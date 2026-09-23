# Datra

A language for data transformations. Read the [preprint](preprint.pdf), [primer](primer.pdf) and
[Lean code](datra.lean). GitHub repo [here](https://github.com/qualiascript/datra).

The LaTeX sources and PDF build instructions live in [datra-docs](datra-docs/README.md).

## Docker

Datra has separate development and production images:

| Docker target | Image tag | Contents |
| --- | --- | --- |
| `development` | `datra-haskell:development` | Datra, GHC, Cabal, Z3, sources, and build caches |
| `prod` (default) | `datra-haskell:prod` | Datra and its runtime libraries on Debian slim |

### Download and install the latest production image

[Download the latest production image](https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz)
or download and load it into Docker from your terminal:

```sh
mkdir -p dist
curl --fail --location \
  https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz \
  --output dist/datra-prod.tar.gz && \
  sudo docker image load --input dist/datra-prod.tar.gz
```

This requires Docker and curl, with no repository checkout or compilation.
It loads the `datra-haskell:prod` image. Omit `sudo` if your account can access
Docker directly; otherwise use `sudo docker` for the run examples too.
Check the release notes for the image's supported platform.

The latest release must include an asset named exactly `datra-prod.tar.gz`.
Keep that filename for each release so the download link continues to work.

### Build from source instead

Build both from the repository root:

```sh
make -C datra-haskell docker-images
```

To build only one, use `docker-development` or `docker-prod` in place of
`docker-images`. Each target uses its own image tag, so rebuilding one keeps
the other image available.

### Run the whole pipeline

After downloading or building the production image, print only the final result:

```sh
docker run --rm datra-haskell:prod build \
  --source '[1; 2 + 3]' \
  --ast-output /dev/null \
  --output -
```

Expected output:

```text
[1; 5]
```

The source is still parsed and interpreted; `--ast-output /dev/null` discards
the AST output. Use `--ast-output -` to print the AST before the result.

See the [Haskell README](datra-haskell/README.md) for direct Docker build
commands, a full pipeline example that saves files, and development shell instructions. Building from
source still runs Liquid Haskell verification; the production image keeps
the distributed runtime small.

## Lean development

This repository keeps its Lean environment in `.elan`. Use the repo-local Lake
executable rather than relying on a system installation; for example, verify the
main source file with:

```sh
./.elan/bin/lake env lean datra.lean
```

## License

Licensed under the [Apache License 2.0](LICENSE). Datra is authored by
[qualiascript](https://github.com/qualiascript); distributions and derivative
works must preserve the attribution in [NOTICE](NOTICE) as required by the
license.
