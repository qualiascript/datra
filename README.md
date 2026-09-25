# Datra

Datra is a language for data transformations. The [preprint](preprint.pdf),
[primer](primer.pdf), and [Lean formalization](datra.lean) live in this
repository.

## Factorial example

Inline recursion uses `fun`, where `this` is the value being defined:

`input.datra`:

```datra
factorial := fun {n? : Int} -> Int do
  yield if n = 0 then 1 else n * this (n - 1)
assert factorial 5 = 120
```

`output.datra`:

```text
()
```

See the [Haskell implementation README](datra-haskell/README.md) for Docker
installation and invocation.

## License

Licensed under the [Apache License 2.0](LICENSE). Datra is authored by
[qualiascript](https://github.com/qualiascript); distributions and derivative
works must preserve the attribution in [NOTICE](NOTICE).
