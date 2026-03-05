# Datra

A WIP language spec for a **da**ta **tra**nsformation language. Read the [primer](primer.md).

## Code Example

```
kvargs :: any X as Type -> Type
kvargs := x as PosInt -> \arg(x)\ : X

myfunc :: args as {kvargs(N)}
myfunc := args @ 0

myval := myfunc(arg1 := 4, arg0 := 9) # = 9
```
