# Datra Proof Sketch [Lean verification WIP]

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_0`
(i.e. the smallest infinite ordinal), that is, its objects are sets that have an injection to `omega_0`, and as its
morphisms set-theoretic functions (i.e. morphisms in `Set`).

1.2. The **Domanial Embedding Functor**, denoted `Emb : Dom -> Set`, sends each dominion to its corresponding set.

2.1. The **Category of Domanial Insertions**, denoted `DomIns`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. 

2.2. The **Category of Codomanial Insertions**, denoted `CoDomIns`, is the opposite category of `DomIns`, that is,
`CoDomIns = op DomIns`.

3.1. The **Category of Domanial Consolidations**, denoted `DomCon`, is the category whose objects are dominions and
morphisms are order-preserving epimorphisms in `Dom`. More specifically, a morphism `F : A -> B` in `DomCon` has the
property that for any `x, y : A`, if `|x| < |y|`, then `|F x| <= |F y|`.

3.2. The **Category of Codomanial Consolidations**, denoted `CoDomCon`, is the opposite category of `DomCon`, that
is, `CoDomCon = op DomCon`.

4.1. A **Chain** is a totally ordered thin category, taken skeletally.

4.2. A **Short Chain** is a chain that is finite, taken skeletally.

5.1. The **Transportation Functor**, denoted `Tra`, is of type `Tra : DomCon -> Set`, and sends each morphism
in `DomCon` to its underlying set-theoretic surjection.

5.2. A **Folio** is a functor `F : C -> (1 / CoDomCon)`, where `1 / CoDomCon` is the coslice category, that preserves
the initial object.

6.1. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(H, E)`, where 
`H = Tra ∘ (op F)`, `F : C -> CoDomCon` is a folio, and `E` is the category of elements of functor `H`. For any
`W : Pag`, we denote `W_H` as the first inclusion and `W_E` as the second inclusion. Morphisms in `Pag`, for
`F : X -> Y`, `X, Y : Pag`, are given by functors `T : X_E -> Y_E`, which implies the following diagram commutes:

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
6.2. The **Category of Atlases**, denoted `Atl`, is the category whose objects are pairs `(P, G)`, where `P : Pag`
and `G` is a functor `G : P_E -> DomIns`, or alternatively a presheaf `G : op P_E -> CoDomIns`. For `X : Atl`,
we denote `X_P` the first inclusion, `X_G` the second inclusion, along with `X_H = X_P_H`, `X_E = X_P_E`. A
morphisms in `Atl`, for `T : X -> Y`, are pairs `(T_P, T_A)`, where `T_P : X_P -> Y_P` is a morphism in `Pag`
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

6.3 The **Cardinality of an Atlas** `A : Atl` is the cardinality of the origin of `A_H : C -> Set`, that is, the
number of objects of the small chain `C`. It is denoted as `|A|`.

6.4. The **Extent of an Atlas** `A : Atl` is the value at `A_G (0, 0)`, that exists as folios preserve initial
objects. It is denoted as `Ex A`. Since the objects of `DomIns` are dominions, `Ex A : Dom` for any `D : Atl`.

6.5. The **Territory of an Atlas** `A : Atl` is the indexed collection of dominions `Ter A : M -> Dom`,
where `M = A_G (|A| - 1)`, so that `Ter A k = A_G (|A| - 1, k)`.

6.6. The **nth Region of an Atlas** `A : Atl` is the dominion `Ter A n` for `n : M`, noting that the indexing
starts at `0`.

7.1. The **Category of Atlas Transposals**, denoted `AtlTrap`, is the wide subcategory of `Atl` whose morphisms
`F : X -> Y` have the property that `F_E` is a faithful functor.

7.2. The **Category of Atlas Traversals**, denoted `AtlTrav`, is the wide subcategory of `AtlTrap` whose morphisms
for `F : X -> Y` have the following properties: for any `x = (k, i)`, `y = (k', j)` with `i < j`, let
`x' = F_E x = (m, i')`, `y' = F_E y = (n, j')` and let `p = min(m, n)`, then `Y_H (m -> p) i' < Y_H (n -> p) j'`.

[TODO: missing lemma: `AltTrap` and `AltTrav` stable under pullback along atlas monos]

8.1. The **Category of Atlas Maps**, denoted `AtlMap`, is the full subcategory of `Atl` with the property that, for any
`A : AtlMap`, `A`'s extent is isomorphic to the coproduct of its regions. That is, let `F = Emb ∘ Ter A : M -> Set`,
and let `Sum A` be the coproduct on diagram `F`, then `A : DaTraMap` iff `Sum A ~= Ex A`.

8.2. The **Atlas Map Inclusion Functor**, denoted `AtlMapInc : AtlMap -> Atl`, sends each Atlas Map to its equivalent
object in `Atl`.

8.3. The **Category of Atlas Traversal Maps**, denoted `AtlTravMap`, is the full subcategory of `AtlTrav` whose objects
are Atlas Maps.

8.4. The **Atlas Traversal Map Inclusion Functor**, denoted `AtlTravMapInc : AtlTravMap -> AtlTrav`, is the canonical
restriction of `AtlMapInc` on the morphisms of `AtlTravMap`.

8.5. The **Cartography Lemma** states that `AtlTravMapInc` has a right adjoint, denoted the **Charting Functor**
`Chr : AtlTrav -> AtlTravMap`. Proof sketch: `Chr`'s action on objects `X : AtlTrav` is sending it to the universal
arrow from `AtlTravMapInc` to `X`, so that we denote `X' = AtlTravMapInc Chr X`, along with `H : X' -> X`, with `X'`
terminal among objects with this property. The solution is given by the DaTra map so that `Ter X' ~= Ter X`, which is
unique as `AtlTrav` preserves orders, and terminal as `H_E` is faithful.

9.1. The **Coalizing Functor**, denoted `Coa : AtlTrav -> Dom`, is defined as `Coa = Ex ∘ Chr`.

9.2. The **Coalition of an Atlas**, given an object `X` of `Atl`, is `Coa X'`, where `X' : AtlTrav` is the
same object viewed as an object of `AtlTrav`.

9.3. The **Domanial Inclusion Functor**, denoted `DomInc : Dom -> AtlTrav`, is the functor that is left adjoint to
`Coa`. That is, for every `X : Dom`, `Y : AtlTrav`, `hom_AtlTrav (DomInc X, Y) ~= hom_Dom(X, Coa Y)`, naturally in
`X` and `Y`, so that `Coa (DomInc X) = X`. It sends each dominion to the atlas of cardinality `1` whose coalition
is the dominion in question.

10.1. The **Category of Data Transformations**, also referred to as the **Category of Data Transformation Sets**, or
simply **DaTra Sets**, denoted `DaTra`, is the category of presheaves on `Atl`, that is,`DaTra = [op Atl, Set]`.
Trivially, `DaTra` is a topos.

10.2. A **Subatlas of a Data Transformation**, given `D : DaTra`, is a monomorphism `S : Yo A -> D` so that `A : Atl`,
where `Yo` represents the Yoneda embedding `Yo : Atl -> DaTra`.

10.3. A **DaTra Restriction**, given `A` a wide subcategory of `Atl`, is the wide subcategory of `DaTra` whose
morphisms for `F : X -> Y` have the property that, for any subatlas `S : Yo A -> D`, let `P` be the pullback of `F`
and `S`, then projection `P' : P -> X` is either empty or representable as `P' = Yo f`, where `f` is a morphism of `A`.

10.4. The **Category of Data Transposals**, denoted `DaTrap`, is the DaTra restriction on `AtlTrap`.

10.5. The **Category of Data Traversals**, denoted `DaTrav`, is the DaTra restriction on `AtlTrav`.

10.6. The **Category of Data Transformation Maps**, denoted `DaTraMap`, is the full subcategory of `DaTra` composed of
objects `D : DaTra` so that for any subatlas `S : Yo A -> D`, we have `A : AtlMap`.

10.7. The **Empty Map**, denoted `I`, is the Yoneda Embedding of `DomInc 0` in `DaTrav`.

11.1. The **Atlas Horizontal Sum Bifunctor**, denoted as `AtlHorSum : Atl * Atl -> Atl`, is defined as follows: given
two morphisms in `Atl`, `F : X -> Y`, `F' : X' -> Y'`, if `F = I`, then `AtlHorSum F F' = F'` and if `F' = I`, then
`AtlHorSum F F' = F`. Otherwise, `AtlHorSum F F'` is the universal arrow from `Atl` to `R = Y + Y'`, `G : K -> R`,
with the property that there exists morphisms `M : X -> K`, `M' : X' -> K` in `AltTrav` with `M_E (0, 0) = (1, 0)`,
`M'_E (0, 0) = (1, 1)` so that `G ∘ M ~= F` and `G ∘ M' ~= F'`.

11.2. The **Horizontal Lemma** states that `AtlHorSum` exists. Proof sketch: cases where `F = I`, `F = I'` are trivial.
Otherwise, for `F : X -> Y`, `F' : X' -> Y'`, let `G : Atl`, `G : A -> B` so that `|G| > 1`, `|A_P 1| = 2`, and for
each `L : |G|`, let `L_max` be the maximal value so that `A_E (L -> 1) L_max = 0`, or `L_max = -1` if such a value does
not exist. Then, define the monomorphisms `T_X : X_E -> A_E`, `T_X' : X'_E -> A_E` as follows: for all `(m, n) : A_E`,
`m > 0`, if `n < m_max`, then `T_X (m, n) = ((m - 1), n)`, otherwise, `T_X' (m, n) = ((m-1), n - m_max + 1)`. It can be
checked `T_X`, `T_X'` are indeed monic, and for any `(m, n) : A_E` there exists `(m', n')` so that either
`T_X (m', n') = (m, n)` or `T_X' (m', n') = (m, n)`. Then define iso `V : A_E -> X_E + X'_E`, along with
`P = (F_P + F'_P) : (X_E + X'_E) -> (Y_E + Y'_E)`, `A = (F_A + F'_A) : (X_G + X'_G) -> ((Y_G ∘ F_E)) + ((Y'_G ∘ F'_E))`.
Finally, let `A_P (0, 0) = B_P (0, 0) = Coa X + Coa X'` `G_A_(0, 0) = Id`, and for all `(m, k) : A_E`, `m > 0`, let
`G_P = P ∘ V`, `G_A_(m, k) = A_(V (m, k))`. This fully defines `G`, which can be checked to be universal.







[TODO: redo from below]



11.1. The **Horizontal Sum Bifunctor**, if it exists, is denoted as `HorSum : DaTrav * DaTrav -> DaTrav`, or using
infix notation using the `+_<` symbol as `DaTrav +_< DaTrav -> DaTrav`, and is defined as follows: given two morphisms
in `DaTrav`, `F : X -> Y`, `F' : X -> Y`, let `H : G * G' -> F + F'` be the universal arrow from `DaTrav * DaTrav` to
`F + F'` so that for projections `H_1 : G -> F + F'`, `H_2 : G' -> F + F'`, for any subatlases `T : Yo R -> H_1`,
`T' : Yo R' -> H_2` so that `T, T' : AltTrav`, for `(m, i) = T_E (0, 0)`, `(m', i') = T'_E (0, 0)`, we have `m < 2`,
`m' < 2`, `i = 0`, and furthermore, if `m = 1`, then `i' = 1`. Then, `F +_< F' = H`. It remains to be shown `H` exists
and is unique for all morphisms `F, F'` of `DaTrav`.

11.2. The **Horizontal Lemma** states that `HorSum` exists. Proof sketch: for `F +_< F'`, if `F' = I`, then
`H : I -> F`, and `I` is initial so `H` is unique, so that `H ~= H_1 ~= H_2` and `(m, i) = H_E (0, 0) = (0, 0)`, so
that `i = 0` and as `m = 0`, the condition on `i'` need not be checked. The case for `F = I` is dual. If both `F` and
`F'` are distinct from `I`, for `(m, i) = R_E (0, 0)`, if `m = 0`, then `i = 0` and `Ex R = Ex R + Ex R'`, but as
`F'` is not `I`, this cannot hold, so that `m = 1`, which implies `i' = 1`, so that the solution is given by
`(m, i) = (1, 0)`, `(m', i') = (1, 1)`.

12.1. The **Data Traversal Monoidal Category**, denoted `DaTravMon`, if it exists, is the symmetric monoidal category
with `DaTrav` as the underlying category, `+_<` as the tensor product and `I` as the identity, so that we denote
`DaTravMon = (DaTrav, +_<, I)`. As for `X : DaTrav`, `X = X + I = I + X` is strict, the left and right unitors are
given by identity. It remains to be shown that there is a braider functor whose double application yields identity,
and an associator functor so that the pentagon, triangle and hexagon identities commute.

12.2. The **Data Traversal Braider**, denoted `Brd_X_Y : X +_< Y -> Y +_< X` for `X, Y : DaTrav`, is defined
as follows: if `X = I` or `Y = I`, `Brd_X_Y = Id`. Otherwise, let `G : H -> X +_< Y` be the universal arrow from
`DaTrap` to `X +_< Y` so that for any `R : AtlTrap` subobject of `G`, `R_E (1, 0) = (1, 1)` and
`R_E (1, 1) = (1, 0)`. Trivially, `H = Y +_< X`, so that we let `Brd_X_Y X +_< Y = H`, and trivially,
`Brd_Y_X Brd_X_Y = Id`.

12.3. The **Data Traversal Associator**, denoted `Asoc_X_Y_Z : (X +_< Y) +_< Z -> X +_< (Y +_< Z)`, is defined
as follows: if `X = I`, `Y = I` or `Z = I`, then `Asoc_X_Y_Z = Id`. Otherwise, denote `K = (X +_< Y) +_< Z` and let
`G : H -> K` be the universal arrow from `DaTrap` to `K` so that for any `R : AtlTrap` subobject of `G`,
`R_E (2, 0) = (1, 0)` and there exists a morphism `G' : (Y +_< Z) -> H` in `DaTrav` with so that for any
`R' : AtlTrav` subobject of `G'`, `R'_E (0, 0) = (1, 1)`. As `R_E` is faithful and `R_A = Id`, `G` is invertible
in `DaTrap`, and by extension in `DaTra`.

12.4. The **Serenity Lemma** states that `DaTravMon` exists. Proof sketch: As both `Asoc` and `Brd` send objects to
isomorphic objects in `DaTra`, it is clear that the pentagon, triangle and hexagon identities commute, thus `DaTravMon`
is a symmetric monoidal category.
