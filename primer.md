# Datra: A Primer

Consider a topos `Datra`, with one of its objects as `N`, the set of natural numbers which can be seen as `FinSet`
taken skeletally. Then, in pseudolanguage, we can define a `sum` function as call it as such, with `#` starting an
inline comment:

```
sum :: a : N, b : N -> N
sum := a + b

mynum := sum(2, 3) # = 5
```

Notice, however, that when calling `sum`, we do not use the identifier names `a`, `b`. They are automatically matched
by the order they are given in. Then, the identifiers `a`, `b` exist for the convenience of the inner body of the
function `sum`, which takes an element `$ : N * N`, which has two projections `$ @ 0` and `$ @ 1`, and the names are
merely for clarity. Then, we could rewrite the function as follows:

```
sum :: N * N -> N
sum := $ @ 0 + $ @ 1
```

It could be useful in practical programming to make the identifier names be explicitly given, and in fact, we could
have some identifiers being given by order while others by name in the same function. In fact, we would like to make
some identifier names to be mandatory. While this seems like an unnecessary restriction, when building APIs, the JSON
format often takes key-value pairs, and we would like to do the same thing. Then, we would like to also keep the syntax
sugar for unordered, internal identifiers, but differentiates between the two. Let us write our function as:

```
sum :: a as N, b as N -> N
sum := a + b
```

An identifier is a subtype of `Str`, the type of strings. Giving an identifier name and a value is then equivalent to
giving a string and a value, which is a product type of the two. Let us say that we can obtain the `n`th object of a
term of a product, such as `x`, by `x @ (n - 1)`. Then, we can write:

```
sum :: "a" * N, "b" * N -> N
sum := $ @ 0 @ 1 + $ @ 1 @ 1

mysum := sum ("a" 2) ("b" 3)
```

We would like to sugar this significantly. Let us rewrite it as follows, while having the same underlying meaning:

```
sum :: a : N, b : N -> N
sum := a + b

mysum = sum(a := 2, b := 3)
```

However, as it is, this does not accept the opposite argument order, meaning giving `b` first and then `a`, despite
the fact that they are unambiguously disambiguated by the identifier names. We would like `sum` to accept any
permutation of arguments, and we would like to make this explicit. Let us say that, given `X` a product, `{X}` is the
type of permutations of `X`. Then, we can write the following:

```
sum :: {a : N, b : N} -> N
sum := a + b

mysum := sum(b := 3, a := 2)
```

## Dependent pairs of identifiers

Consider the successor function, taking an explicit argument:

```
succ :: x : N -> N
succ := x + 1
```

This would get desugared to:

```
succ :: "x" * N -> N
succ := $ @ 1 + 1
```

From another perspective, consider `x` to be an identifier that depends on a value. In this case, the value of the 
identifier is constant for any value, so it is reduced to a product, but it is useful to consider the general case
in order to construct further generalizations. This is a dependent sum, which could be written as follows:

```
succ :: Σ(placeholder : N) "x" -> N
succ := $ @ 0 + 1
```

As the value `"x"` is constant, let us say that this sugars back to exactly the original version. However, we would
also like to generally impose a restriction on the `b : a` syntax, that is, each value `b` should correspond to a single
`a`. This is stricter than dependent sum types in general, but is usually the correct semantics for function calling.
One can write `b : Σ a` in order to relax to dependent sums in general. Then we have:

```
succ :: x : N -> N
succ := x + 1

mynum := succ (x := 1) # 2
```

In this case, it becomes apparent that `x := 1` is, in fact, sugar for a function, and it inhabits the function type
`x : N`, which as we've seen, is sugar for a dependent sum. For consistency, we may also conceptualize unnamed
arguments passed to a function as a function. For instance, in this example:

```
sum :: a as N, b as N -> N
sum := a + b

mysum := sum(2, 3)
```

We may see `(2, 3)` as a function from `2` to `N`, assigning `0` to `2` and `1` to `3`. By extension, we will consider
functions to be the fundamental object in Datra. A value `x :: X` is given by a function `x : 1 -> X`, even if that
is sugared out. This also ought not to be surprising considering the semantics of lambda calculus.

## Regex types

If we have identifiers that depend on values, it is natural to consider non-constant identifiers, whose value actually
get modified, in some manner, by the value they depend on. Regex provides the correct semantics for this: we can say
that a regex is a string that depends on its captured values. However, Regex is also heavy, so it is unclear whether
only a well-behaved subset of it ought to be implemented. As a demo example, let us consider merely an identifier where
a section of it depends on an integer, without using formal Regex syntax. We could, for instance, write it as follows:

```
twice :: x as N -> N
twice := x * 2

func :: arg as \arg(twice)\ : N 
func := arg + 1

myval := func(arg4 := 2) # = 5
```

In this instance, `func` only accepts values where the identifier name consists of `arg` followed by a value that is
twice the value of the argument. This example is not practically useful, but it serves to illustrate the principle at
play. More generally, this can validate that an argument name is provided with a coherent value of sorts. Identifiers
are strings, but it is useful to not confound the two. Let us say that `\x\` is the canonical representation of an
identifier, such as when it is not inferrable that it refers to an identifier in context. For instance:

```
kvargs :: Π X as Type -> Type
kvargs := x as PosInt -> \arg(x)\ : X

myfunc :: args as {kvargs(N)}
myfunc := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # = 9
```

Where `PosInt` is the type of positive integers. This type checks as `(arg0 := 1, arg1 := 4)` is, by itself, a
function `x as 2 -> \arg(x) : N`, and it can be inferred at compile time to be the case. Furthermore, `kvargs` can be
inferred to be of type `Type2`, that is, in a type universe larger than `Type` itself. This illustrates the promise of
Datra: function calling and argument names ought to be first class, and have the full expressivity of dependent types.
If successful, this could be a natural way to design API constrains so that wrong API calls are unrepresentable.
