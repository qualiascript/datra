# Datra

A WIP language spec for a **da**ta **tra**nsformation language. Read the [primer](primer.md).

## Code Example

```
kwargs : any X of Type -> Type
    := x as PosInt -> \arg(x)\ : X

myfunc : args of {kwargs(N)}
    := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # := 9
```
