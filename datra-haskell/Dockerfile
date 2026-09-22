FROM haskell:9.14.1-bookworm AS build

ARG CABAL_VERSION=3.18.1.0
ARG TARGETARCH

# Liquid Haskell delegates refinement checking to an external SMT solver.
# Keep Z3 in the image so both image builds and interactive development can
# use the liquid plugin.
RUN apt-get update && \
    apt-get install --yes --no-install-recommends z3 && \
    rm -rf /var/lib/apt/lists/* && \
    z3 --version

# The GHC 9.14.1 official image currently contains an older cabal-install.
# Install the exact Cabal version used by this project and verify the GHCup
# bindist before replacing /usr/local/bin/cabal.
RUN set -eux; \
    case "$TARGETARCH" in \
      amd64) \
        cabal_archive="cabal-install-${CABAL_VERSION}-x86_64-linux-glibc.tar.xz"; \
        cabal_sha256="bbc0ce17dea6600d44293be8f74e14ddca833a24a4bcbf56f8bd11962c09ff4c" \
        ;; \
      arm64) \
        cabal_archive="cabal-install-${CABAL_VERSION}-aarch64-linux-deb10.tar.xz"; \
        cabal_sha256="0f60a0f5941ce2eae4ebe759344d3b1f664893de7e42527fad8b5017e887c035" \
        ;; \
      *) \
        echo "unsupported Docker architecture: $TARGETARCH" >&2; \
        exit 1 \
        ;; \
    esac; \
    cabal_url="https://downloads.haskell.org/~ghcup/unofficial-bindists/cabal/${CABAL_VERSION}/${cabal_archive}"; \
    curl --fail --location --silent --show-error "$cabal_url" --output /tmp/cabal.tar.xz; \
    echo "${cabal_sha256}  /tmp/cabal.tar.xz" | sha256sum --check --strict; \
    tar --extract --xz --file /tmp/cabal.tar.xz --directory /usr/local/bin cabal; \
    rm /tmp/cabal.tar.xz; \
    test "$(cabal --numeric-version)" = "$CABAL_VERSION"; \
    test "$(ghc --numeric-version)" = "9.14.1"

WORKDIR /opt/datra

# Copy package metadata first so Docker can preserve the dependency cache when
# application sources change.
COPY cabal.docker.project datra-haskell.cabal LICENSE NOTICE CHANGELOG.md README.md ./
RUN cabal update && \
    cabal build \
      --project-file=cabal.docker.project \
      --only-dependencies \
      all \
      -fliquid \
      -j1

COPY app ./app
COPY src ./src
COPY test ./test

RUN cabal build \
      --project-file=cabal.docker.project \
      exe:datra-haskell \
      -fliquid \
      -j1 && \
    install --strip -m 0755 \
      "$(cabal list-bin --project-file=cabal.docker.project exe:datra-haskell -fliquid)" \
      /usr/local/bin/datra && \
    datra ast --source '[1; 2 + 3]' --output -

# Keep the full toolchain available explicitly for interactive development.
FROM build AS development
WORKDIR /data
VOLUME ["/data"]
ENTRYPOINT ["/usr/local/bin/datra"]

# Ship only the executable and its system libraries. Match the builder's
# Debian release so the executable uses the same glibc ABI at runtime.
FROM debian:bookworm-slim AS prod

RUN apt-get update && \
    apt-get install --yes --no-install-recommends libgmp10 libffi8 libnuma1 && \
    rm -rf /var/lib/apt/lists/*

ENV LANG=C.UTF-8

COPY --from=build /usr/local/bin/datra /usr/local/bin/datra
COPY LICENSE NOTICE /usr/local/share/doc/datra/

# Exercise the executable in the final image to catch missing shared libraries
# and preserve UTF-8 input/locale support without the development toolchain.
RUN test "$(datra ast --source '[1; 2 + 3]' --output -)" = '(<:> 1 (+ 2 3))' && \
    datra interpret --ast '(<:> 1 (+ 2 3))' --locale romanian --output -

# Datra's default input and output names are relative to this directory. Mount
# a host directory at /data to retain input.datra and generated output files.
WORKDIR /data
VOLUME ["/data"]

ENTRYPOINT ["/usr/local/bin/datra"]
