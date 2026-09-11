# IntelliJ Haskell `forall` diagnostic

## Symptom

IntelliJ may report a syntax error in
`src/DatraCore/Atlas/Morphism/Internal.hs` ending with:

```text
<q name>, <top declaration>, <var con>, HaskellTokenType... expected,
got 'forall'
```

The same file compiles successfully with both of the compiler configurations
used by this repository.

## What produces the error

The `HaskellTokenType...` vocabulary identifies this as an error from the
lightweight parser bundled with the IntelliJ **Haskell LSP** plugin. It is not
a GHC error, a Cabal error, a LiquidHaskell error, or an HLS diagnostic.

The installed IntelliJ plugin is `intellij-haskell-lsp` 1.5.1. Its parser
recognizes `forall` in several common positions, which is why the other
rank-n types in the codebase do not necessarily produce the same warning.
Some combinations of GADT syntax, parenthesized higher-rank fields, and
explicit `forall` are not handled consistently by its PSI grammar.

`Atlas.Morphism.Internal` originally contained a rank-n function directly in
a GADT constructor. That function has since been moved behind the ordinary
`AtlasMorphismAction` newtype, but IntelliJ can still report a parser error in
the module even though GHC accepts it. Restarting HLS alone cannot reset this
parser because it runs inside IntelliJ rather than in the language-server
process.

## Current compiler split

There are intentionally two configurations:

1. Normal builds use the repository-local GHC 9.14.1 selected by
   `cabal.project`. The Cabal `liquid` flag defaults to enabled, so these builds
   use LiquidHaskell 0.9.14.1.1.
2. IntelliJ uses the custom BIOS cradle selected by the root `hie.yaml`.
   `.hie/bios` uses system GHC 9.4.7 because the currently installed HLS 2.10
   executable was built with GHC 9.4.7. `cabal.hie.project` disables the
   `liquid` flag and defines `__GHCIDE__`, so the IDE can load the code without
   resolving or running the GHC-9.14-only LiquidHaskell plugin.

The generated cradle data is stored below `.hie/` and ignored by Git. Only
`.hie/bios` and `.hie/ghc` are tracked.

## Verified state

The complete library, including `Atlas.Morphism.Internal`, has been compiled
successfully in both modes:

```text
IDE build:    GHC 9.4.7, LiquidHaskell disabled, 27 modules compiled
Normal build: GHC 9.14.1, LiquidHaskell enabled
```

Therefore this particular editor warning should not be treated as evidence
that the Haskell source is invalid.

## Updating IntelliJ and HLS

The most likely actual fix is a newer version of the IntelliJ **Haskell LSP**
plugin with an updated PSI grammar:

1. Open **Settings → Plugins → Installed → Haskell LSP**.
2. Install an available update newer than 1.5.1.
3. Restart IntelliJ and use **File → Invalidate Caches…** if the old parser
   result remains attached to the file.

Changing only GHC may not fix this exact warning, because the PSI parser does
not delegate parsing to GHC. Nevertheless, HLS and GHC should be updated as a
matched pair if IntelliJ is moved to GHC 9.14.1.

First inspect the available HLS builds:

```bash
ghcup list -t hls
```

Install an HLS release that explicitly supports GHC 9.14.1:

```bash
ghcup install hls <HLS_VERSION>
ghcup set hls <HLS_VERSION>
```

Confirm that the selected HLS distribution contains a server compatible with
the project compiler:

```bash
haskell-language-server-wrapper --probe-tools
```

Then open **Settings → Tools → Haskell LSP** in IntelliJ and set the HLS path
to the GHCup wrapper, normally:

```text
/home/alex/.ghcup/bin/haskell-language-server-wrapper
```

If the wrapper needs an explicit project toolchain on `PATH`, create a small
launcher such as:

```sh
#!/bin/sh
PATH=/home/alex/Desktop/datra/.tools/.ghcup/ghc/9.14.1/bin:$PATH
export PATH
exec /home/alex/.ghcup/bin/haskell-language-server-wrapper "$@"
```

Make it executable and select that launcher under **Settings → Tools →
Haskell LSP**. After HLS is genuinely running against GHC 9.14.1, `.hie/bios`
and `.hie/ghc` can also be changed from `/usr/bin/ghc` and
`/usr/bin/ghc-pkg` to the corresponding executables under
`.tools/.ghcup/ghc/9.14.1/bin`.

Do not make that cradle change while HLS is still built for GHC 9.4.7: HLS
must use the exact GHC API version it was compiled to support.

## Refresh commands

After changing the compiler or HLS configuration, rebuild the disposable
cradle state from the repository root:

```bash
pkill -f haskell-language-server
rm -rf .hie/dist
```

IntelliJ should restart HLS automatically. If the `HaskellTokenType` warning
remains, restart or invalidate IntelliJ itself; killing HLS does not restart
the plugin's PSI parser.

The normal verified build remains:

```bash
cd datra-haskell
cabal build all --offline
```

