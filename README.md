# Datra

A language for data transformations. Read the [preprint](preprint.pdf), [primer](primer.pdf) and
[Lean code](datra.lean). GitHub repo [here](https://github.com/qualiascript/datra).

The LaTeX sources and PDF build instructions live in [datra-docs](datra-docs/README.md).

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
