# datra

a language for **da**ta **tra**nsformation.

note: this is extremely wip and subject to change

## basic data types

- `Integer` (bigint)
- `Float` (double), when numeric literal includes a period
- `Infinity`
- `String` within double quotes
- `Empty` type (initial object, no inhabitants)
- `()` type (terminal object, singleton inhabitant)
- `Anything`
- `Identifier`
- `Type` types (values that depend on `Type` are not themselves in `Type`)

## basic operations
- `+`, `-`, `*`, `/`, `^` (exponentiation) with their usual math sense for integers and rationals
- `>`, `<`, `>=`, `<=`, `=`, `=/=` comparisons
- `+` string concatenation
- `and`, `or`, `not`
- `(`, `)` order of operations

## paradigms 
- fully functional
- strong, static, inferred typing
- lazy evaluation

## functions
- functions lazily map values in the domain to a value in the codomain
- everything in **datra** is a function, including basic literals
  - if `x` is a literal, it is equivalent to `() := x`, which is a function that maps `()` to `x`
  - more generally, `x := y` is a function that maps the value x to the value y
- full syntax for one kv (key-value) pair (which is by itself a valid function) is `a : b := c`, where either `: b` or `:= c` can be skipped
  -  `: b` is a type annotation, which checks compile-time if b subtypes c. it is inferred if skipped
  - note that `a` isn't required to be a simple value, and mapping evaluation is done by pattern matching
  - however, if `a` is a simple identifier, it will be taken as a value of `Identifier` type
- if a mapping has undefined values (i.e. keys with no `:=`), it is considered partial and it cannot be called
  - however, it can still be used as a type annotation
- if a key is not given as a value, but as an identifier, e.g. `a`, that identifier will bind to the value
  - if the kv pair is part of the key map of another kv pair, `a` can be used directly within the outer kv pair
  - e.g. `(a : Integer) := a * 2`. note the parentheses, as the structure is `(map) := result`
  - `*identifier` is sugar for `identifier :  ()`

## algebraic data types
- the `,` operator creates a product function of two existing functions
  - `a := b, c := d` will create a new function which maps `a` to `b` and `c` to `d`
  - if either the left or right side maps `()` to a value (i.e. is a standalone value), the behavior is different:
    - the key is shifted to be the smallest non-negative integer not already mapped
    - this allows `1, 2, 3` to be semantically equivalent to `0 : 1, 1 : 2, 2 : 3`, i.e. allows lists
- the `|` operator creates a coproduct (sum) partial function
  - `a := b | c := d` is partial because it could map `a` to `b` or `c` to `d`, but it is not known which
  - the same `()` key rule applies as for the `,` operator
- `a & b` merges two maps, that is, it creates the smallest map that supertypes both, and errs if it's not possible

## function application and evaluation
- `f m` applies a map to a function
  - this is *not* evaluating the function, it is more akin to currying
  - for each kv pair `kv` in `m`, it replaces the definition of all kv pairs that supertype it in the function domain with `kv`
  - it does not compile if such a key does not exist
  - e.g. for `f := (x : Integer, y : Integer) := x + y`, `f (x := 5)` is `(x : Integer := 5, y : Integer) := x + y`
- `f!` evaluates a function
  - this only compiles if the function's domain is reducible to a single kv pair, whose key is a total function (a complete map)
  - if the function's domain consists of a summed union of kv pairs, it will evaluate the first pair whose key is a total function
  - as the function has all information necessary, it can be transformed into a value (or technically, a `() := value` function)
- `f[x]` evaluates a function for a specific value, matched to the first kv pair whose key it subtypes
  - seeing functions as maps, this becomes the usual sense of `map[key]`
  - if the function consists of a summed union of kv pairs, evaluation removes all kv pairs but the first matching one
- `^ f` transforms a map into a positional map, which can be pattern-matched by positional arguments
  - e.g. `^(x : Int, y : Int)` will match to `(1, 2)` as `^(x : Int := 1, y : Int := 2)`
  - arguments can also be matched explicitly key in positional maps
  - `nonposmap & posmap` will also generate a map that is mixed positional - non-positional

## additional notes
- any **datra** program is implicitly a function/map, with newlines outside of expressions being taken as `,`
- `a :: b -> c` is sugar for `a := b := c`, for clarity
- `a @ b` is sugar for `(^a) b!`. if `a` is already positional, applying `^` doesn't change anything
- `$a` retrieves the `Identifier` value equal to `a`, instead of the value of `a`
  - `a.b` is syntactic sugar for `a[$b]`
- to have `a := b` represent the value at `a`, it needs to be a full expression, such as `Id@a`

## code example

```
Id := ^(x : Anything) := x)
Boolean := *True | *False
Maybe :: type : Type -> Just : type | *Nothing
myValue := (Maybe@Integer).Just@7
Tree :: type : Type -> left : Tree@type, right : Tree@type | *Nothing
List :: type : Type -> () | ^(value : type) & List@type
Kwargs :: type : Type -> ^(ids : List@(Identifier : type))
Dummy :: x : Integer & Kwargs@String -> ids
```
