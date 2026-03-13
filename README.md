# Datra

A WIP language spec for a **da**ta **tra**nsformation language. Read the [primer](primer.md).

## Code Example

### Hello World

```
"Hello, world!"
```

### First class arbitrary arguments

```
Args :: X of Map -> Map
    := any x of PosInt -> "arg[x]" : X

myfunc :: args of {Args Int}
    := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # := 9
```

### Dependent Identifiers

```
double :: x of Int -> Int := 2 * x
myfunc :: {x of "x[double]" : Int, y of "y[double]" : Int} -> Int
    := 2 * x + y
    
mynum := myfunc(y4 := 2, x6 := 3) # := 8
# mynum := myfunc(x7 := 3, y6 := 4) # does not compile!
```