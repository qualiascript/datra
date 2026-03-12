# Datra

A WIP language spec for a **da**ta **tra**nsformation language. Read the [primer](primer.md).

## Code Example

### Hello World

```
"Hello, world!"
```

### First class Kwargs

```
kwargs :: any X of Type -> Type
    := x of PosInt -> "arg[x]" : X

myfunc :: **args of {kwargs Int}
    := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # := 9
```

### Dependent Identifiers

```
double :: x of Int -> Int := 2 * x
myfunc :: arg of "arg[double]" : Int -> Str
    := "Received value [arg] with identifier [$arg]"
    
myval := myfunc(arg4 := 2) # := "Received value 2 with identifier arg4"
# myval := myfunc(arg5 := 2) # does not compile!
```