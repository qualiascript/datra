# Datra

Datra is a language for data transformations. The [preprint](preprint.pdf),
[primer](primer.pdf), and [Lean formalization](datra.lean) live in this
repository.

## Install with Docker

Download and load the latest production image:

```sh
mkdir -p dist
curl --fail --location \
  https://github.com/qualiascript/datra/releases/latest/download/datra-prod.tar.gz \
  --output dist/datra-prod.tar.gz && \
  sudo docker image load --input dist/datra-prod.tar.gz
```

This requires Docker and curl, but no repository checkout or Haskell toolchain.
It installs `datra-haskell:prod`. Omit `sudo` if your account can access Docker
directly.

To build the production and development images from a checkout instead:

```sh
make -C datra-haskell docker-images
```

## Run the factorial example

Recursive declarations use `let`:

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

See the [Haskell implementation README](datra-haskell/README.md) for file
mounts, development images, and test commands.

## License

Licensed under the [Apache License 2.0](LICENSE). Datra is authored by
[qualiascript](https://github.com/qualiascript); distributions and derivative
works must preserve the attribution in [NOTICE](NOTICE).
