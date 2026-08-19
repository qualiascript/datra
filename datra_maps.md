# Datra Maps

## 1. Base Definitions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1` (i.e.
the first uncountable ordinal), that is, its objects are sets that have a surjection to `omega_1`, and as its morphisms
set-theoretic injections (i.e. monomorphisms in `Set`).

1.2. The **Category of Domanial Sets**, denoted `DomSet`, is the category of presheaves on `Dom`, that is
`DomSet = [op Dom, Set]`. Note that this category is similar to the category of nominal sets, but distinct as nominal
sets are presheaves on `FinSet_mono`, which does not include sets whose cardinality is `omega_1`.

1.3. The **Category of Codomanial Sets**, denoted `CoDomSet`, is the category of copresheaves on `Dom`, that is,
`CoDomSet = [Dom, Set]`. It is a concept with an attitude for the category of functors whose origin is `Dom` and target
is `Set`. Trivially, it is also the opposite category of `DomSet`.

1.4. The **Category of Antidominions**, denoted `AntDom`, has the same objects as `Dom`, and a morphism `f : X -> Y`
for `X, Y : AntDom` is a set-theoretic surjection (i.e. epimorphism) `f : Y -> X`. Note that this category has no
initial object, as the only morphism with origin `0` is `id_0`, and there is no other morphism with target `0`.
However, `1` is initial in the origin of the inclusion that contains all `AntDom` objects besides `0`.

1.5. The **Category of Antidomanial Traversals**, denoted `AntDomTra`, is the coslice, or undercategory, from the
singleton set `1` to `AntDom`. That is, `AntDomTra = 1 / AntDom`. 

1.6. The **Category of Data Traversal Maps**, denoted `DaTrav`, is the category of presheaves of the category of
Antidomanial Traversals `AntDomTra` to the category of Domanial Sets `DomSet`, that is,
`DaTrav = [op AntDomTra, DomSet]`. Alternatively, it is the functor category from `AntDomTra` to `CoDomSet`, that is,
`DaTrav = [AntDomTra, CoDomSet]`. Trivially, these definitions coincide.

1.7. The **Category of Data Transformation Maps**, denoted `DaTra`, is the monoidal category defined on the base of
`DaTrav`, along with the **Sequential Operator** denoted `;`, which is a functor `X ; X -> X` for `X : DaTrav`, defined
on morphisms as follows: for `f : X -> Y`, `g : X' -> Y'`, let `h` be an object in `DaTrav` obtained as the presheaf on
`1 -> 2` in `AntDomTra`, so that, by pulling back on `op (1 -> 2)` at `0`, one obtains `X`, and by pulling back at `1`,
one obtains `X'`. This object is universal insofar as `h 1 = X + X'`. Then, `f ; g` is the presheaf on `1 -> 2 -> K`,
where `|K| = |Y| + |Y'|`, so that the morphism on `1 -> 2` is `h`, whose pullback on the first leg of `h` is `f`, and
on the second leg is `g`. The unit object of `DaTra` is the empty presheaf on `1`, which we will denote `[]` and refer
to as the **Empty Map**. There is also a **DaTra Associator** `asc : (X ; X) ; X -> X ; (X ; X)` that can be obtained
by inverting the legs on the outermost sequential operator application, as well as the natural left and right unitors
on `X ; []` and `[] ; X` respectively.