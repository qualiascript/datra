# Datra

Datra is a language for data transformations. The [preprint](preprint.pdf),
[primer](primer.pdf), and [Lean formalization](datra.lean) live in this
[repository](https://github.com/qualiascript/datra/). Details on the WIP
Haskell implementation can be found [here](/datra-haskell).

Excuse the AI slop, it is temporary until the surface language has a chance
to stablize, which will allow me to write its documentation in my own words.

## Factorial example

```datra
let factorial := {n? : Int} -> Int do
  yield if n = 0 then 1 else n * factorial (n - 1)
assert factorial 5 = 120
```

## First-class variadic arguments

Variadic arguments need no special handling in Datra. `Args` is a first-class
type defined entirely in the standard library:

```datra
Args := &T? do
  slots := (^_i :: Nat) do yield "arg%(_i)"? : T
yield ((^n? :: Nat) do yield slots[0..n])
```

For example, this is a Datra program that utilizes `Args` directly:

```datra
ArgsIntMap := {Args Int,}
ListInt := List Int
display := ArgsIntMap -> "%ListInt" do
  toList := ArgsIntMap -> {ListInt,} do yield it
  yield "%(toList it)"

assert display() = "()"
assert display(1) = "1"
assert display(1, 2, 3) = "(1; 2; 3)"
assert display(arg1 := 10, 4) = "(4; 10)"
assert ((arg2 := 10, 4) of ArgsIntMap) = false # missing argument: `arg1`
```

See the [Haskell implementation README](datra-haskell/README.md) for Docker
installation and invocation.

## License

Licensed under the [Apache License 2.0](LICENSE). Datra is authored by
[qualiascript](https://github.com/qualiascript); distributions and derivative
works must preserve the attribution in [NOTICE](NOTICE).
