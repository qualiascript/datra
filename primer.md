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
succ :: some(placeholder : N) "x" -> N
succ := $ @ 0 + 1
```

As the value `"x"` is constant, let us say that this sugars back to exactly the original version. However, we would
also like to generally impose a restriction on the `b : a` syntax, that is, each value `b` should correspond to a single
`a`. This is stricter than dependent sum types in general, but is usually the correct semantics for function calling.
One can write `b : some a` in order to relax to dependent sums in general. Then we have:

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

func :: arg as \arg(twice($))\ : N 
func := arg + 1

myval := func(arg4 := 2) # = 5
```

In this instance, `func` only accepts values where the identifier name consists of `arg` followed by a value that is
twice the value of the argument. This example is not practically useful, but it serves to illustrate the principle at
play. More generally, this can validate that an argument name is provided with a coherent value of sorts. Identifiers
are strings, but it is useful to not confound the two. Let us say that `\x\` is the canonical representation of an
identifier, such as when it is not inferrable that it refers to an identifier in context. For instance:

```
kvargs :: any X as Type -> Type
kvargs := x as PosInt -> \arg(x)\ : X

myfunc :: args as {kvargs(N)}
myfunc := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # = 9
```

Where `PosInt` is the type of positive integers. This type checks as `(arg0 := 9, arg1 := 4)` is, by itself, a
function `x as 2 -> \arg(x)\ : N`, and it can be inferred at compile time to be the case. Furthermore, `kvargs` can be
inferred to be of type `Type2`, that is, in a type universe larger than `Type` itself. This illustrates the promise of
Datra: function calling and argument names ought to be first class, and have the full expressivity of dependent types.
If successful, this could be a natural way to design API constrains so that wrong API calls are unrepresentable.

## Typing ambiguities

There are some ambiguities inherent to the design that ought to be handled. Firstly, we ought to disallow this:

```
func :: x as N, x as N
```

With `x` as an internal identifier, it is unclear which of the values it is referring to. We also ought to not allow
internal identifiers to be non-constant, as that defeats the purpose of using them by name internally. As such, despite
being introduced in that manner, internal identifiers are more than sugar, and must respect its own laws. This can be
also seen when dealing with more complex function domain bodies, such as this:

```
func :: x : N, N, {a as N, b as N}
```

Firstly, `x : N` also treats `x` as an internal identifier, so it can be seen as `x as x : N`. The second argument is
here only given the type `N`, so in order to call it, one would need to call `$ @ 1` internally. Then, it could be seen
as `1 as N`, taking into account that numeric identifiers have a different call convention. In fact, all arguments in
`func` have a numeric calling convention, given by `$ @ 0`, `$ @ 1`, `$ @ 2 @ 0`, `$ @ 2 @ 1`, and this is unambiguous.
Some also have internal identifiers, this is an injective function from `String` to the parameter space.

We also wish to disallow this:

```
func :: {\a(func1)\ : N, \a(func2)\ : N}
```

We seek for there to be a unique mapping from the argument list to the quotient space of `{f}`, and in general,
non-constant identifiers induce ambiguity. Let us define, then, that `{}` only operates on constant identifiers, that
is, identifiers that, as dependent types, have all values they depend on in the same fiber. Quotient maps, while they
accept any permutation, still have a canonical order given by the order of typing, so that internal identifiers can be
injected into it. Then, the domain function, as the product of hereditarily finite body maps, has a canonical injection.

We would like to allow a calling style convention of mixing positional and identifier-based argument naming. By this
perspective, this can be made unambiguous as follows. Consider function calls:

```
val1 := func(2, x := 3)
val2 := func(x := 3, 2)
```

In both cases, the function bodies are identical, and given by the map `(0 := 2, x := 3)`. This can be constructed by
first removing the identifier-based positions from the map, and for the remaining ones, assigning position values in
order. The function body can be seen as an abstract syntax tree, dependent on internal identifiers, either as integers
or strings. This is a bijective function, mapping each identifier to codomain `Tree(Args)`. If the argument body matches
the external identifiers, it can be made to match the internal identifiers as well, in order for it to inhabit `f`.

In fact, we can drop the hereditarily finite requirement as long as only one node in `Tree(Args)` is given by a
function `f : N -> Args`, and it is, by canonical order, the last one to use positional arguments. This also requires
all its child nodes to be hereditarily finite. In general, it is likely too ambiguous to allow infinite maps containing
external identifier based arguments; this would require a proof of non-ambiguity, which an interpreter cannot generally
construct. Infinite positional arguments, by comparison, are practically useful for lazy evaluation.

## Default Values

So far, we have considered two possibilities: argument maps as types, and the values that inhabit it. In practice, we
would like for argument maps to have default values, so that the argument maps can skip some values and have them be
inferred, or override the default values. In general, positional default values followed by positional arguments without
default values cannot be overridden; however, positional arguments can be given explicitly, as key-value pairs starting
in an integer, so we do not seek to totally disallow this. It is a good candidate for an interpreter warning.

In general, given an argument map, by giving an argument a default value, one creates a new map so that said value is
optional. If all values have defaults, then all arguments are optional, and the unit value `()` inhabits it. We can
consider this to be a subtyping operation on the canonical function `f` of an argument map. If the map has no default
values, then we can construct `g = f + ()` as a canonical representation of the map. Otherwise, given a map `f` and a
subtype, or injective function `f'` into it, this is given by `g' = f' + Defaults`, the latter inhabited by `()`.

Then, `Defaults` must provide, for each argument, either a value or `()`, meaning to use the default value. The
arguments are indexed by their internal identifiers, but they may contain external identifier information in the form
of dependent pairs. By another perspective, `Defaults` is the type of injective functions into a default arguments map.
This is similar to the definition of `f'` itself, so that `g'` is inhabited by an inhabitant of `f'` along with a
subtype of the arguments of `f` that are unchosen by `f'`, which we denote `f / f'`. 

We would like subtyping to be given by a subobject classifier. Given an object `f`, a subobject `f'` is given by what is
mapped to `()` by the canonical unique morphism. This consists of the values `f'` does not give a default value to.
However, this implies that `f'` is the type of all possible ways of assigning default values of a selection of
arguments. This tracks, as from a categorical perspective, all such default value mappings are isomorphic, in the sense
of having the exact same subtypes. However, it implies we are not working in sets, but some other category.

In fact, the internal identifiers can also be made invariant. That is, if `f'` subtypes `f` but they do not agree on
internal identifiers, all that is necessary is to be provided an internal identifier map from `f'` to `f'`. Let us also
simplify by saying all arguments have external identifiers, but they might be provided by natural numbers as opposed
to the regex type. Then, some object `f` is given by an arguments tree, where some arguments are marked as optional and
some nodes are marked as accepting any order, however, they do not handle dependent identifiers.

Let us define it as such: `Reg` is a regex dependent type. `CReg` is the subtype of `Reg` where all values it depends
on are in the same fiber. In addition, let `NDep` be an integer that depends on a value, and `CNDep` be the case where
the dependence is constant. Then, `CArg = CReg + CNDep`, `Arg = Reg + NDep`, `QArgL = CArg + N * CArgL`,
`ArgL = Arg + N * ArgL`. Then, `ArgMap : ArgL -> 2`, as it maps the argument list to whether they have default values.
Up to isomorphism, `ArgMap` is a Datra type, but in reality, Datra types depend on the provision of default values.

As a category, `ArgMap` can be partially ordered by inclusion. That is, for `x, y :: ArgMap`, `x < y` exactly when all
arguments of `x` are contained in `y` and if an argument of `y` is marked as having a default value, and it also appears
in `x`, then it also has a default value in `x`. This requirement is reminiscent of the base change stability
requirement of a Grothendieck topology, where the covering sieve is the selection of default values. This suggests the
direction to take is in trying to formalize this as a category of sheaves of some sort.

## Datra Topos

[TO BE CONTINUED]