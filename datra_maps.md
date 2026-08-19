# Datra Maps

## 1. Base Definitions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1` (i.e.
the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its morphisms
set-theoretic injections (i.e. monomorphisms in `Set`).

1.2. The **Category of Domanial Sets**, denoted `DomSet`, is the category of presheaves on `Dom`, that is
`DomSet = [op Dom, Set]`. The **Category of Codomanial Sets**, denoted `CoDomSet` is the opposite of the category of
domanial sets, that is, `CoDomSet = op DomSet`. [CONNECTION TO NOMINAL SETS?]

1.3. The **Category of Antidominions**, denoted `AntDom`, has the same objects as `Dom`, and a morphism `f : X -> Y`
for `X, Y : AntDom` is a set-theoretic surjection (i.e. epimorphism) `f : Y -> X`. Note that this category has no
initial object, as the only morphism with origin `0` is `id_0`, and there is no other morphism with target `0`.

1.4. The **Category of Stable Antidominions**, denoted `StAntDom`, is the coslice, or undercategory, from the
singleton set `1` to `AntDom`. That is, `StAntDom = 1 / AntDom`. As such, `1` is initial in `StAntDom`, and the
canonical inclusion `inc : StAntDom -> AntDom` reaches all objects of `AntDom` besides `0`.

1.5. The **Category of Data Traversal Maps**, denoted `DaTrav`, is the category of presheaves of the category of
Antidomanial Traversals `StAntDom` to the category of Domanial Sets `DomSet`, that is,
`DaTrav = [op StAntDom, DomSet]`. Alternatively, it is the opposite of functor category from `StAntDom` to `CoDomSet`,
that is,`DaTrav = op [StAntDom, CoDomSet]`. Trivially, these definitions coincide.

1.6. The **Category of Data Transformation Maps**, denoted `DaTra`, is the monoidal category defined on the base of
`DaTrav`, along with the **Sequential Operator** denoted `;`, which is a functor `X ; X -> X` for `X : DaTrav`, defined
on morphisms as follows: for `f : X -> Y`, `g : X' -> Y'`, let `h` be an object in `DaTrav` obtained as the presheaf on
`1 -> 2` in `StAntDom`, so that, for `p : 2 -> 1` the unique surjective function, `h p 0 = X` and `h p 1 = X'`. This
object is universal insofar as `h 1 = X + X'`. Then, `f ; g` is the presheaf on `p' . p`, where `p' : |Y| + |Y'| -> 2`
so that `(f ; g) p'` pulled back at `0` equals `f`, and pulled back at `1` equals `g`. The unit object of `DaTra` is
the empty constant presheaf on `1`, which we will denote `[]` and refer to as the **Empty Map**, as such, there are
left and right unitors `L : [] ; X -> X`, `R : X ; [] -> X`.

1.7. There is a **DaTra Associator** `asc : (A ; B) ; C -> A ; (B ; C)`, that can be obtained as follows: for
`A : X -> Y`, `B : X' -> Y'`, `C : X'' -> Y''`, create the universal presheaf `h` on `p : |X + X' + X''| -> 3` so that,
by pulling back at `0`, `1`, and `2` respectively, one obtains `A`, `B` and `C`. Then, one obtains `A ; (B ; C)` by
precompositions with surjection `k, k' : 3 -> 2`, so that `k 0 = 0`, `k 1 = 1`, `k 2 = 1`. [ADD MORE DETAIL LATER]

1.8. There is a **DaTra Braiding**, `br : (A ; B) -> (B ; A)` obtained similarly as above by precomposition with
`k : 2 -> 2`, `k 0 = 1`, `k 1 = 0`. Naturally, `br br = id`. One can also check that the pentagon, triangle and hexagon
identities are fulfilled by similar logic [TO BE COMPLETED LATER]. As such, `DaTra` is a symmetric monoidal category.