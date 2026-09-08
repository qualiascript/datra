# Datra documentation

This folder contains the LaTeX sources and tooling used to build Datra's PDF
documentation. Generated PDFs are written to the repository root.

## Primer

From this folder, build the primer PDF with:

```sh
make primer
```

This writes `../primer.pdf` using the pinned local Tectonic engine described
below; no system-wide TeX installation is required.

## Preprint

The LaTeX preprint is embedded directly in `../datra.lean` between `/-%%` and
`%%-/` markers. Generate its LaTeX source with:

```sh
make blueprint
```

This writes `preprint.tex` in this folder. Build the PDF with:

```sh
make preprint
```

This writes `../preprint.pdf`. No system-wide TeX installation is required.
The first build downloads the pinned Tectonic engine and the required TeX
packages into `../.tools/tectonic`; later builds reuse that local installation
and cache. To install the engine without compiling a document, run
`make setup-tex`.

To build the full edition, including the complete Lean formalization as a
syntax-highlighted and line-numbered appendix, run:

```sh
make preprint_full
```

This writes `../preprint_full.pdf`.
