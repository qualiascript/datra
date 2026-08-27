# Datra

A language for data transformations. Read the [preprint](datra.pdf) or the [Lean formalization](datra.lean).

## Preprint

The LaTeX preprint is embedded directly in `datra.lean` between `/-%%` and
`%%-/` markers. Generate it with:

```sh
make blueprint
```

This writes `preprint.tex`. Build the PDF with:

```sh
make preprint
```

No system-wide TeX installation is required. The first build downloads the
pinned Tectonic engine and the required TeX packages into `.tools/tectonic`;
later builds reuse that local installation and cache. To install the engine
without compiling the document, run `make setup-tex`.

To build the full edition, including the complete Lean formalization as a
syntax-highlighted and line-numbered appendix, run:

```sh
make preprint_full
```


