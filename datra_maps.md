# Datra Proof Sketchbook

## 1. Base Definitions

1.1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1`
(i.e. the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its
morphisms set-theoretic functions (i.e. morphisms in `Set`).

1.1.2. The **Domanial Embedding Functor**, denoted `Emb : Dom -> Set`, sends each dominion to its corresponding set.

1.2.1. The **Category of Domanial Insertions**, denoted `DomIns`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. 

1.2.2. The **Category of Codomanial Insertions**, denoted `CoDomIns`, is the opposite category of `DomIns`, that is,
`CoDomIns = op DomIns`.

1.3.1. The **Category of Domanial Consolidations**, denoted `DomCon`, is the category whose objects are dominions and
morphisms are order-preserving epimorphisms in `Dom`. More specifically, a morphism `F : A -> B` in `DomCon` has the
property that for any `x, y : A`, if `|x| < |y|`, then `|F x| <= |F y|`.

1.3.2. The **Category of Codomanial Consolidations**, denoted `CoDomCon`, is the opposite category of `DomCon`, that
is, `CoDomCon = op DomCon`.

1.4.1. The **Traversal Functor**, denoted `Tra`, is of type `Tra : DomCon -> Set`, and sends each morphism in `DomCon`
to its underlying set-theoretic surjection.

1.5.1. A **Chain** is a totally ordered thin category, taken skeletally.

1.5.2. A **Short Chain** is a chain that is finite, taken skeletally.

1.6.1. A **Folio** is a functor `F : C -> (1 / CoDomCon)`, where `1 / CoDomCon` is the coslice category, that preserves
the initial object.

1.6.2. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(H, E)`, where 
`H = Tra ∘ (op F)`, `F : C -> CoDomCon` is a folio, and `E` is the category of elements of functor `H`. For any
`W : Pag`, we denote `W_H` as the first inclusion and `W_E` as the second inclusion. Morphisms in `Pag`, for
`F : X -> Y`, `X, Y : Pag`, are given by functors `T : X_E -> Y_E`, so that the following diagram commutes:

```
x = (m, i) -----f----> (n, (X_H f) i)
|                      |
|                      |
T                      T
|                      |
|                      |
⌄                      ⌄                             
(m', i') ----T f-----> (n', (Y_H (T f)) i')
```

1.7.1. The **Category of Data Transformations**, denoted `DaTra`, which we will also refer to as the **Category of Data
Transformation Sets**, or simply **DaTra Sets**, is the category whose objects are pairs `(P, G)`, where `P : Pag`
and `G` is a functor `G : P_E -> DomIns`, or alternatively a presheaf `G : op P_E -> CoDomIns`. For `X : DaTra`,
we denote `X_P` the first inclusion, `X_G` the second inclusion, along with `X_H = X_P_H`, `X_E = X_P_E`. A
morphisms in `DaTra`, for `T : X -> Y`, are pairs `(T_P, T_A)`, where `T_P : X_P -> Y_P` is a morphism in `Pag`
and `T_A : X_G => Y_G ∘ T_E` is a natural transformation, that is, the following diagram commutes for all morphisms
`f : x -> y` in `X_P`:

```
X_G x ------------X_G f------------> X_G y
|                                    |
|                                    |
(T_A)_x                              (T_A)_y
|                                    |
v                                    v
Y_G (T_E x) -----Y_G (T_E f)-------> Y_G (T_E y)
```

1.7.2. The **Cardinality of a DaTra Set** `D : DaTra` is the cardinality of the origin of `D_H : C -> Set`, that
is, the number of objects of the small chain `C`. It is denoted as `|D|`.

1.7.3. The **Extent of a DaTra Set** `D : DaTra` is the value at `D_G (0, 0)`, that exists as folios preserve initial
objects. It is denoted as `Ex D`. Since the objects of `DomIns` are dominions, `Ex D : Dom` for any `D : DaTra`.

1.7.4. The **Territory of a DaTra Set** `D : DaTra` is the indexed collection of dominions `Ter D : M -> Dom`, 
where `M = D_G (|D| - 1)`, so that `Ter D k = D_G (|D| - 1, k)`.

1.7.5. The **nth Region of a DaTra Set** `D : DaTra` is the dominion `Ter D n` for `n : M`, noting that the indexing
starts at `0`.

1.8.1. The **Category of Structured Data Transformations**, denoted `StDaTra`, is the wide subcategory of `DaTra`
whose morphisms for `F : X -> Y` have the property that `F_E` is a faithful functor.

1.8.2. The **Category of Data Traversals**, denoted `DaTrav`, is the wide subcategory of `StDaTra` whose morphisms
for `F : X -> Y` have the following properties: for any `x = (k, i)`, `y = (k, j)` with `i < j`, let
`x' = F_E x = (m, i')`, `y' = F_E y = (n, j')` and let `k' = min(m, n)`, then `Y_G (m -> k') i' < Y_G (n -> k') j'`.

1.9.1. The **Category of Data Transformation Maps**, denoted `DaTraMap`, is the full subcategory of `DaTra` that
includes all DaTra sets with the property that their extent is isomorphic to the coproduct of its regions. That is, for
`D : DaTra`, let `F = Emb ∘ Ter D : M -> Set`, and let `Sum D` be the coproduct on diagram `F`, then `D : DaTraMap`
iff `Sum D ~= Ex D`.

1.9.2. The **DaTra Map Inclusion Functor**, `DaTraMapInc : DaTraMap -> DaTra` sends each DaTra map to its equivalent
DaTra set.

1.9.3. The **Category of Data Traversal Maps**, or simply **DaTrav Maps**, denoted `DaTravMap`, is the wide
subcategory of `DaTraMap` so that a morphism `f : x -> y` of `DaTraMap` is a morphism of `DaTravMap` iff
`DaTraMapInc f` is a morphism of `DaTrav`.

1.9.4. The **DaTrav Map Inclusion Functor**, `DaTravMapInc : DaTravMap -> DaTrav` is the canonical restriction of
`DaTraMapInc` on the morphisms of `DaTravMap`.

1.9.5. The **Charting Functor**, if it exists, is defined as the right adjoint to `DaTravMapInc`, and it is denoted
`Chr : DaTrav -> DaTravMap`.

1.9.6. The **Cartography Lemma** states that `Chr` exists. Proof sketch: `Chr`'s action on objects `X : DaTrav` is
sending it to the universal arrow from `DaTravMapInc` to `X`, so that we denote `X' = DaTravMapInc Chr X`, along with
`H : X' -> X`, with `X'` terminal among objects with this property. The solution is given by the DaTra map so that
`Ter X' ~= Ter X`, which is unique as `DaTrav` preserves orders, and terminal as `H_E` is faithful.

1.10.1. The **Coalizing Functor**, denoted `Coa : DaTrav -> Dom`, is defined as `Coa = Ex ∘ Chr`.

1.10.2. The **Domanial Inclusion Functor**, denoted `DomInc : Dom -> DaTrav`, is the functor that is left adjoint to
`Coa`. That is, for every `X : Dom`, `Y : DaTrav`, `hom_DaTrav (DomInc X, Y) ~= hom_Dom(X, Coa Y)`, naturally in
`X` and `Y`, so that `Coa (DomInc X) = X`.

1.10.3. The **Coalition of a DaTra Object**, given an object `X` of `DaTra`, is `Coa X'`, where `X' : DaTrav` is the
same object viewed as an object of `DaTrav`.

1.10.4. The **Empty Map** is the DaTra set that `DomInc` sends the initial object of `Dom`, `0 : Dom`, to. It is
denoted as `I = DomInc 0`, and it is initial in `DaTra`.

1.11.1. The **Horizontal Sum Bifunctor**, if it exists, is denoted as `HorSum : DaTrav * DaTrav -> DaTrav`, or using
infix notation using the `+_<` symbol as `DaTrav +_< DaTrav -> DaTrav`, and is defined as follows: given two morphisms
in `DaTrav`, `F : X -> Y`, `F' : X -> Y`, let `H : G * G' -> F + F'` be the universal arrow from `DaTrav * DaTrav` to
`F + F'` so that for projections `H_1 : G -> F + F'`, `H2 : G' -> F + F'`, for `(m, i) = H_1_E (0, 0)`,
`(m', i') = H_2_E (0, 0)`, we have `m < 2`, `m' < 2`, `i = 0`, and furthermore, if `m = 1`, then `i' = 1`. Then,
`F +_< F' = H`. It remains to be shown `H` exists and is unique for all morphisms `F, F'` of `DaTrav`.

1.11.2. The **Horizontal Lemma** states that `HorSum` exists. Proof sketch: for `F +_< F'`, if `F' = I`, then
`H : I -> F`, and `I` is initial so `H` is unique, so that `H ~= H_1 ~= H_2` and `(m, i) = H_E (0, 0) = (0, 0)`, so
so that `i = 0` and as `m = 1`, the other condition need not be checked. The case for `F = I` is dual. If both `F` and
`F'` are distinct from `I`, for `(m, i) = H_1_E (0, 0)`, if `m = 0`, then `i = 0` and `Ex F = Ex F + Ex F'`, but as
`F'` is not `I`, this cannot hold, so that `m = 1`, which implies `i' = 1`, so that the solution is given by
`(m, i) = (1, 0)`, `(m', i') = (1, 1)`.

1.12.1. The **Data Traversal Monoidal Category**, denoted `DaTravMon`, if it exists, is the symmetric monoidal category
with `DaTrav` as the underlying category, `+_<` as the tensor product and `I` as the identity, so that we denote
`DaTravMon = (DaTrav, +_<, I)`. As for `X : DaTrav`, `X = X + I = I + X` is strict, the left and right unitors are
given by identity. It remains to be shown that there is a braiding functor whose double application yields identity,
and an associator functor so that the pentagon, triangle and hexagon identities commute.

1.12.2. The **Data Traversal Braiding Functor**, denoted `Brd_X_Y : X +_< Y -> Y +_< X` for `X, Y : DaTrav`, is defined
as follows: if `X = I` or `Y = I`, `Brd_X_Y = Id`. Otherwise, let `G : H -> X +_< Y` be the universal arrow from
`StDaTra` to `X +_< Y` so that `G_E (1, 0) = (1, 1)` and `G_E (1, 1) = (1, 0)`. Trivially, `H = Y +_< X`, so that
we let `Brd_X_Y X +_< Y = H`, and trivially, `Brd_Y_X Brd_X_Y = Id`.

1.12.3. The **Data Traversal Associator**, denoted `Asoc_X_Y_Z : (X +_< Y) +_< Z -> X +_< (Y +_< Z)`, is defined
as follows: if `X = I`, `Y = I` or `Z = I`, then `Asoc_X_Y_Z = Id`. Otherwise, denote `R = (X +_< Y) +_< Z` and let
`G : H -> R` be the universal arrow from `StDaTra` to `R` so that `G_E (2, 0) = (1, 0)` and there exists a morphism
`G' : (Y +_< Z) -> H` in `DaTrav` with `G'_E (0, 0) = (1, 1)`. As `G_E` is faithful and `G_A = Id`, `G` is invertible
in `StDaTra`, and by extension in `DaTra`. As both `Asoc` and `Brd` send objects to isomorphic objects in `DaTra`,
it is clear that the pentagon, triangle and hexagon identities commute, thus `DaTravMon` is a symmetric monoidal
category.
