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

1.7.1. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(H, E)`, where 
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

1.8.1. The **Category of Data Transformations**, denoted `DaTra`, which we will also refer to as the **Category of Data
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

1.8.2. The **Cardinality of a DaTra Set** `D : DaTra` is the cardinality of the origin of `D_H : C -> Set`, that
is, the number of objects of the small chain `C`. It is denoted as `|D|`.

1.8.3. The **Extent of a DaTra Set** `D : DaTra` is the value at `D_G (0, 0)`, that exists as folios preserve initial
objects. It is denoted as `Ex D`. Since the objects of `DomIns` are dominions, `Ex D : Dom` for any `D : DaTra`.

1.8.4. The **Territory of a DaTra Set** `D : DaTra` is the indexed collection of dominions `Ter D : M -> Dom`, 
where `M = D_G (|D| - 1)`, so that `Ter D k = D_G (|D| - 1, k)`.

1.8.5. The **nth Region of a DaTra Set** `D : DaTra` is the dominion `Ter D n` for `n : M`, noting that the indexing
starts at `0`.

1.9.1. The **Category of Data Traversals**, denoted `DaTrav`, is the wide subcategory of `DaTra` whose morphisms
for `F : X -> Y` have the following properties: the underlying functor `F_E : X_E -> Y_E` is faithful, and for any
`x = (k, i)`, `y = (k, j)` with `i < j`, let `x' = F_E x = (m, i')`, `y' = F_E y = (n, j')` and let `k' = min(m, n)`,
then `Y_G (m -> k') i' < Y_G (n -> k') j'`.

1.10.1. The **Category of Data Transformation Maps**, denoted `DaTraMap`, is the full subcategory of `DaTra` that
includes all DaTra sets with the property that their extent is isomorphic to the coproduct of its regions. That is, for
`D : DaTra`, let `F = Emb ∘ Ter D : M -> Set`, and let `Sum D` be the coproduct on diagram `F`, then `D : DaTraMap`
iff `Sum D ~= Ex D`.

1.10.2. The **DaTra Map Inclusion Functor**, `DaTraMapInc : DaTraMap -> DaTra` sends each DaTra map to its equivalent
DaTra set.

1.10.3. The **Category of Data Traversal Maps**, or simply **DaTrav Maps**, denoted `DaTravMap`, is the wide
subcategory of `DaTraMap` so that a morphism `f : x -> y` of `DaTraMap` is a morphism of `DaTravMap` iff
`DaTraMapInc f` is a morphism of `DaTrav`.

1.10.4. The **DaTrav Map Inclusion Functor**, `DaTravMapInc : DaTravMap -> DaTrav` is the canonical restriction of
`DaTraMapInc` on the morphisms of `DaTravMap`.

1.10.5. The **Charting Functor**, if it exists, is defined as the right adjoint to `DaTravMapInc`, and it is denoted
`Chr : DaTrav -> DaTravMap`.

1.10.6. The **Serenity Lemma** states that `Chr` exists. Proof sketch: `Chr`'s action on objects `X : DaTrav` is
sending it to the universal arrow from `DaTravMapInc` to `X`, so that we denote `X' = DaTravMapInc Chr X`, along with
`H : X' -> X`, with `X'` terminal among objects with this property. The solution is given by the DaTra map so that
`Ter X' ~= Ter X`, which is unique as `DaTrav` preserves orders, and terminal as `H_E` is faithful.

1.11.1. The **Coalizing Functor**, denoted `Coa : DaTrav -> Dom`, is defined as `Coa = Ex ∘ Chr`.

1.11.2. The **Domanial Inclusion Functor**, denoted `DomInc : Dom -> DaTrav`, is the functor that is left adjoint to
`Coa`. That is, for every `X : Dom`, `Y : DaTrav`, `hom_DaTrav (DomInc X, Y) ~= hom_Dom(X, Coa Y)`, naturally in
`X` and `Y`, so that `Coa (DomInc X) = X`.
























[TODO; needs rework from below due to definition changes above]

1.11. The **Coalizing Functor** `Coa : DaTra -> DaTra` sends morphisms `F : X -> Y` to `F' : X' -> Ser F`, where
`F'` is a universal arrow in `DaTrav`. Then, `X'` is referred to as the **Coalition** of `F`, and, in particular, if
`F = id X`, `X'` is the coalition of `X`. Clearly [TODO: Proof outline], `X' m k` is inhabited iff `m = k = 0`, so
that `X'` is isomorphic to an object of `DomIns`, and in fact, as the only morphism is identity in `X'`'s pagination,
to an object of `Dom`. As such, to each arrow of `Coa`, one obtains an arrow `f : DaTra -> Dom`, mapping `DaTra`
objects to `Dom` objects, and as such, a forgetful functor `Forg : DaTra -> Dom`. Then let `Free : Dom -> DaTra`
be the free functor sending each dominion to its coalition. Clearly, `Free Forg Free x = Free x` and
`Forg Free Forg y = Forg y`, so that `Free` is left adjoint of `Forg`.

1.12. The **Sequential Bifunctor**, `(;) : DaTra * DaTra -> DaTra`, also denoted infix as `DaTra ; DaTra -> DaTra`,
is defined for `F : X -> Y`, `F' : X' -> Y'` as follows: let `U` be the universal arrow `U : F + F' -> H` in `DaTrav`,
so that for inclusions `U_F : F -> H`, `U_F' : F' -> H`, if there exists integers `k`, `m`, `n`, so that `U_F` sends
`F 0 0` to `H k m` and `U_F'` sends `F' 0 0` to `H k n`, then `m < n`. Clearly, the solution has the properties that
`k = 1`, `m = 0`, `n = 1`, and `U 0 0 = Forg (F + F')`.

[TODO: `DaTra`, along with `(;)`, form a symmetric monoidal category]

