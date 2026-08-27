# Datra

A WIP language spec for a **da**ta **tra**nsformation language. Read the [primer](primer.md). Lean formalization
is in active progress.

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

## Code Example

### Hello World

```
"Hello, world!"
```

### Dependent Identifiers

```
double :: x of Int -> Int := 2 * x
myfunc :: {x of "x[double]" : Int, y of "y[double]" : Int} -> Int
    := 2 * x + y
    
mynum := myfunc(y4 := 2, x6 := 3) # := 8
# mynum := myfunc(x7 := 3, y6 := 4) # does not compile!
```
