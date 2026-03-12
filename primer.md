# Datra: A Primer

Firstly, an important clarification: a lot of Datra operations seem ambiguous, or like they could break in non-obvious
ways. This is not the case. Formally, Datra is modeled by nominal sets, so all operations done below are either correct,
or only incorrect due to human syntactical errors.

Consider the following function:

```
sum :: a : Int, b : Int -> Int
    := a + b
```

Note that the indentation is not semantically relevant, this is simply `name : type := value`. `::` has the same
meaning as `:`, except it binds to the latest `->` in the type definition, as to be the function type's left side
argument. In Datra, `sum` must be called with explicit identifiers, as such, with `#` denoting an inline comment:

```
y := sum(a := 2, b := 3) # y := 5
```

This might seem like an unnecessary restriction, but it maps to how APIs are utilized in practice. Additionally, Datra
supports positional arguments as well, using the `as` keyword, and positional arguments are also callable explicitly
by identifier:

```
func :: a as Int, b as Int -> Int
    := 2 * a + b
    
y := func(2, 3) # y := 7
z := func(b := 4, 3) # z := 10
```

We may seek to restrict this further, by making arguments positional only. We refer to identifiers that only serve
an internal purpose, and cannot be used externally, as **intra-identifiers**. Identifiers using `:` are denoted
**extra-identifiers**, and identifiers using `as` which can be used in both ways as **ambi-identifiers**. We declare
intra-identifiers using the `of` keyword:

```
func :: a of Int, b of Int -> Int
    := 2 * a + b
    
y := func(2, 3) # y := 7
# z := func(b := 4, 3) # does not compile
```

In fact, both `as` and `of` are syntactic sugar. We use the `val` keyword to denote the values provided to the function,
and the `@` operator to denote the value in a tuple at a specific index. We also use the `do` and `yield` keywords,
with `do` replacing `:=` to mean that there is a full function body that yields a value.

```
func :: Int, Int -> Int do
    a := val @ 0
    b := val @ 1
    yield 2 * a + b
```

In fact, the `do` / `yield` syntax is itself syntactic sugar [^1]. It can be rewritten as follows. We can obtain the
values in the map using the `@` operator, followed by the string corresponding to the identifier name. As such, we get:

```
func' :: Int, Int -> (a : Int, b : Int)
    := (a := val @ 0, b := val @ 1)
    
func :: Int, Int -> Int
    := 2 * (func' val) @ "a" + (func' val) @ "b"
```

You may have noticed a self-similarity at play here: the entire code snippet looks like an argument map. This is not
coincidental: all Datra programs are so-called **total maps**, maps that have all values filled. In that sense, a
newline character is another way of writing `,` as a separator. As such, we can rewrite our snippet in one line, as
follows. Note the parentheses use for clarity. To clarify: this is **not** how Datra is normally used! This is closer
to an internal representation.

```
(func' :: Int, Int -> (a : Int, b : Int) := (a := val @ 0, b := val @ 1), func :: Int, Int -> Int := 2 * (func' val) @ "a" + (func' val) @ "b")
```

But if Datra programs are maps, then keys in a map do not have to be identifiers. In fact, we have been using the
following convention implicitly: for a map argument `a : b := c`, if `a` is given under identifier form, it is
implicitly coerced to be a string. As such, the sum function could have been written as follows:

```
"sum" :: a : Int, b : Int -> Int := a + b
```

We refer to an identifier on the left side of `:`, or of `:=` directly if the type is inferred, as a **free
identifier**. By similar logic, there is no reason for the left side to not be some other value:

```
0 :: a : Int, b : Int -> Int := a + b
```

In fact, just like with a positional argument, no key must be provided at all. This leads to another implicit Datra
convention: in any map, values that are provided without keys have their keys inferred by the natural numbers, starting
from `0` and assigning in order. As such, the code snippet is equivalent to the following:

```
(a : Int, b : Int) -> Int := a + b
```

In order to call such a function, we need the map to refer to itself. This is done using the `this` keyword, as follows:

```
(a : Int, b : Int) -> Int := a + b
y := (this @ 0)(a := 2, b := 3) 
```

A Datra program takes some structured input and yields structured output. In this context, given a map representing a
source code, the function executed is the one with the highest integer key, which, if using positional arguments, is
the last one defined in the program. For instance, this is the Hello World program:

```
"Hello, world!"
```

Going back, this makes it clear in what sense `as` is syntactic sugar. The following code snippet:

```
func :: a as Int, b : Int -> Int
    := 2 * a + b
```

Could be written using sum types, given by the operator `|`, and using implicit positional arguments, as follows:

```
func :: (a : Int, b : Int) | (a of Int, b : Int) -> Int
    := 2 * a + b
```

Of course, within one map, some keys might have arguments provided and some might not. This corresponds to a function
that has default arguments. Without going into detail, this does not, in fact, induce ambiguities with positional
arguments. We introduce `::=` as syntactic sugar for `:=`, with the same meaning except it clarifies that this is an
inner argument assignment. For instance:

```
func :: a : Int ::= 4, b as Int -> Int
    := 2 * a + b
    
y := func(5) # := 13
```

Of course, one can explicitly override the provided default value:

```
func :: a : Int ::= 4, b as Int -> Int
    := 2 * a + b
    
y := func(a := 1, 5) # := 7
```

Datra also supports string interpolation, in a modified sense. Within the `"` delimiters, one can write values within
square brackets, and they will be interpolated. This is also how Datra handles string concatenation. Non-string values
are automatically converted to string values in this context. For instance:

```
hello := "Hello, "
world := "world"
mynum := 7
"[hello][world]! My number is [mynum]"
```

In fact, Datra extends this concept by allowing the interpolated values to be functions, so that given an input, one
obtains a string with the desired output. For instance:

```
# This function is in the standard library
Id :: x of Any -> Any := x

mynum := 2
double :: x of Int -> Int := 2 * x
dependent_string := "The double of [id] is [double]" : Int
dependent_string @ my_num 
```

The usage of `:` in `dependent_string`'s definition might seem ambiguous at first, but it is not. An argument such as
`a : Int` is equivalent to `"a" : Int`, so that the identifier is a trivial string interpolation. When called with an
argument such as `a := 5`, the argument subtypes `"a" : Int` by providing the value of `"a"` at `5`. As it is trivial,
this seems pointless, but `a : b`, which is the syntax of **dependent types**, can encode identifiers that depend on
values, or simply **dependent identifiers**. For instance, with operator `$` obtaining the extra-identifier:

```
double :: x of Int -> Int := 2 * x
myfunc :: arg of "arg[double]" : Int -> Str
    := "Received value [arg] with identifier [$arg]"
    
myval := myfunc(arg4 := 2) # := "Received value 2 with identifier arg4"
# myval := myfunc(arg5 := 2) # does not compile!
```

One feature not yet mentioned is variable order arguments, however, Datra makes this trivial: given any map `a`, `{a}`
is the map with variable order arguments. This can yield to ambiguous situations when calling, however, Datra is able
to unambiguously map arguments in many cases, and if it is not able to resolve it, it provides a compiler error. As
such, all Datra function calls are unambiguous and valid. For instance:

```
double :: x of Int -> Int := 2 * x
myfunc :: {x of "x[double]" : Int, y of "y[double]" : Int} -> Int
    := x + y
    
mynum := myfunc(y4 := 2, x6 := 3) # := 5
# mynum := myfunc(x7 := 3, y6 := 4) # does not compile!
```

In this case, there is no ambiguity. Obviously, positional arguments in any order are ambiguous, and so are repeated
identifiers in any order. However, if order is not variable, nothing in Datra forbids repeated identifiers:

```
func :: arg1 of x : Int, arg2 of x : Int -> Int
    := arg1 + arg2
 
mynum := func(x := 2, x := 3) # := 5
```

Datra is, in fact, a **dependently typed programming language**, but while advanced features are available, they are
not necessary in order to write a Datra program. `a : b` is the syntax for dependent sums, and one can write, for
instance, `myfunc(x, y, z) : (x as Int, y as Int, z as Int)`. Dependent products are written by appending the `any`
keyword to arguments in the function type signature. This is the context in which one obtains the code snippet on the
front page, where `kwargs` is a first-class `Datra` function:

```
kwargs :: any X of Type -> Type
    := x of PosInt -> "arg[x]" : X

myfunc :: **args of {kwargs Int}
    := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # := 9
```

In this example, `PosInt` is a positive integer, and `**` tells Datra that the map provided during function call ought
to be made to fit into `args`, not `val`.

[^1]: Except for the fact that they ensure the name of the induced helper function does not collide with anything.
