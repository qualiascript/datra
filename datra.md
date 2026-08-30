# DaTra: Data Transformation Semantics as a Symmetric Monoidal Category on Atlas Presheaves

## Authors: `@qualiascript`, ChatGPT

## 1. Dominions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_0`
(i.e. the smallest infinite ordinal), that is, its objects are sets that have an injection to `omega_0`, and as its
morphisms set-theoretic functions (i.e. morphisms in `Set`).

1.2. The **Domanial Embedding Functor**, denoted `Emb : Dom -> Set`, sends each dominion to its corresponding set.

## 2. Domanial Insertions

2.1. The **Category of Domanial Insertions**, denoted `DomIns`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. 

2.2. The **Category of Codomanial Insertions**, denoted `CoDomIns`, is the opposite category of `DomIns`, that is,
`CoDomIns = DomIns^op`.

## 3. Chains

3.1. A **Chain** is a totally ordered thin category with strictly less than `omega_0 ^ omega_0` distinct objects,
taken skeletally.

3.2. The **Spine** is the chain with `omega_0` objects.

## 4. Consolidations

4.1. The **Category of Consolidations**, denoted `Con`, is the category whose objects `D : Con` are chains
and whose morphisms `K : X -> Y` are point-surjective functors on chains `F : X -> Y`.

4.2. The **Category of Coconsolidations**, denoted `CoCon`, is the opposite category of `Con`, that
is, `CoCon = Con^op`.

## 5. Transportation and Folios

5.1. The **Transportation Functor**, denoted `Tra`, is of type `Tra : Con -> Set`, and sends each morphism
in `Con` to its underlying set-theoretic surjection.

5.2. A **Folio** is a functor `F : S -> CoCon`, where `S` is a spine, so that `F 0 = 1`.

## 6. Paginations

6.1. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(H, E)`, where 
`H = Tra ∘ (F^op)`, `F : C -> CoCon` is a folio, and `E` is the category of elements of functor `H`. For any
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

## 7. Atlases

7.1. The **Category of Atlases**, denoted `Atl`, is the category whose objects are pairs `(P, G)`, where `P : Pag`
and `G` is a functor `G : P_E -> DomIns`, or alternatively a presheaf `G : P_E^op -> CoDomIns`, with the property that
for `P_H : C -> Set`, for `m : |C|`, for any `a = (m, k) : P_E`, `b = (m, k') : P_E`, if `k =/= k'`, the pullback in
`G` of `(m -> 0) k` and `(m -> 0) k'` is empty. Furthermore, there exists an integer `w` with the property that
for any other integer `w'` so that `w < w'`, `P_H (w' -> w) = id` and for any `k : |P_H w|` `G (w' -> w) k = id`.
The least integer `w` with this property is then named the **Cardinality of the Atlas**, and denoted `|A|` for
`A : Atl`. For `X : Atl`, we denote `X_P` the first inclusion, `X_G` the second inclusion, along with `X_H = X_P_H`,
`X_E = X_P_E`. A morphism in `Atl`, for `T : X -> Y`, are pairs `(T_P, T_A)`, where `T_P : X_P -> Y_P` is a morphism in
`Pag` and `T_A : X_G => Y_G ∘ T_E` is a natural transformation, that is, the following diagram commutes for all
morphisms `f : x -> y` in `X_E`. Furthermore, for `x = |X|`, for any `x' > x`, for any `r : X_H (|X| - 1)`,
`T_P (x', r) = T_P (x, r)` and `T_A_(x', r) = T_A_(x, r)`.

```
X_G x ------------X_G f------------> X_G y
|                                    |
|                                    |
(T_A)_x                              (T_A)_y
|                                    |
⌄                                    ⌄
Y_G (T_E x) -----Y_G (T_E f)-------> Y_G (T_E y)
```

7.2. The **Cardinality of an Atlas** `A : Atl`, denoted `|A|`, is the least positive integer after which the spine
repeats its final genuine page `|A| - 1`.

7.3. The **Extent of an Atlas** `A : Atl` is the value at `A_G (0, 0)`.
It is denoted as `Ex A`. Since the objects of `DomIns` are dominions, `Ex A : Dom` for any `A : Atl`.

7.4. The **Territory of an Atlas** `A : Atl` is the indexed collection of dominions `Ter A : M -> Dom`,
where `M = A_H (|A| - 1)`, so that `Ter A k = A_G (|A| - 1, k)`.

7.5. The **nth Region of an Atlas** `A : Atl` is the dominion `Ter A n` for `n : M`, noting that the indexing
starts at `0`.

## 8. Transposals and Traversals

8.1. The **Category of Atlas Transposals**, denoted `AtlTrap`, is the wide subcategory of `Atl` whose morphisms
`F : X -> Y` have the property that `F_E` is point-injective.

8.2. The **Category of Atlas Traversals**, denoted `AtlTrav`, is the wide subcategory of `AtlTrap` whose morphisms
for `F : X -> Y` have the following properties: for any `x = (m, i)`, `y = (m', j)`, let `p = min(m, m')`,
`x' = F_E x = (n, i')`, `y' = F_E y = (n', j')` and let `p' = min(n, n')`, then if `X_H (m -> p) i < X_H (m' -> p) j`,
then `Y_H (n -> p') i' < Y_H (n' -> p') j'`. Furthermore, for any `q : |X|`, `t : X_G q`, if there exists `k : |Ter X|`
and `l : Ter X k` so that `t : X_G ((|X| - 1) -> q) k l`, this property gets preserved by `F`. 

8.3. The **Category of Stable Atlas Traversals**, denoted `AtlTras`, is the wide subcategory of `AtlTrav` so that
for `F : X -> Y`, `F_E (0, 0) = (0, 0)`.

## 9. Maps and Cartography

9.1. The **Category of Atlas Maps**, denoted `AtlMap`, is the full subcategory of `Atl` with the property that, for any
`A : AtlMap`, for `m = |A| - 1`, for any `v : Ex A`, there exists `k : |Ter A|` so that let `f = A_G (m -> 0) k`,
there exists `p : A_G m k` so that `v ~= f p`.

9.2. The **Atlas Map Inclusion Functor**, denoted `AtlMapInc : AtlMap -> Atl`, sends each Atlas Map to its equivalent
object in `Atl`.

9.3. The **Category of Atlas Traversal Maps**, denoted `AtlTravMap`, is the full subcategory of `AtlTrav` whose objects
are Atlas Maps.

9.4. The **Atlas Traversal Map Inclusion Functor**, denoted `AtlTravMapInc : AtlTravMap -> AtlTrav`, is the canonical
restriction of `AtlMapInc` on the morphisms of `AtlTravMap`.

9.5. The **Cartography Lemma** states that `AtlTravMapInc` has a right adjoint, denoted the **Charting Functor**
`Chr : AtlTrav -> AtlTravMap`. Proof sketch: `Chr`'s action on objects `X : AtlTrav` is sending it to the universal
arrow from `AtlTravMapInc` to `X`, so that we denote `X' = AtlTravMapInc Chr X`, along with `H : X' -> X`, with `X'`
terminal among objects with this property. The solution is given by the DaTra map so that `Ter X' ~= Ter X`, which is
unique as `AtlTrav` preserves orders, and terminal as `H_E` is faithful.

## 10. Coalitions

10.1. The **Coalizing Functor**, denoted `Coa : AtlTras -> DomIns`, is defined as `Coa = Ex ∘ Chr`.

10.2. The **Coalition of an Atlas**, given an object `X` of `Atl`, is `Coa X'`, where `X' : AtlTras` is the
same object viewed as an object of `Atl`.

10.3. The **Domanial Inclusion Functor**, denoted `DomInc : DomIns -> AtlTras`, is the functor that is left adjoint to
`Coa`. That is, for every `X : DomIns`, `Y : AtlTras`, `hom_AtlTras (DomInc X, Y) ~= hom_DomIns(X, Coa Y)`, naturally
in `X` and `Y`, so that `Coa (DomInc X) = X`. It sends each dominion to the atlas of cardinality `1` whose coalition
is the dominion in question.

## 11. Data Transformations

11.1. The **Category of Data Transformations**, also referred to as the **Category of Data Transformation Sets**, or
simply **DaTra Sets**, denoted `DaTra`, is the category of presheaves on `Atl`, that is,`DaTra = [Atl^op, Set]`.
Trivially, `DaTra` is a topos.

11.2. A **Navigation of a Data Transformation**, given `D : DaTra`, is a monomorphism `Nav : Yo A -> D` so that
`A : Atl`, where `Yo` represents the Yoneda embedding `Yo : Atl -> DaTra`.

11.3. An **Expedition of a Data Transformation**, given `D : DaTra`, is a navigation `Exd : Yo A -> D` so that
`A : AtlMap`.

11.4. A **DaTra Restriction**, given `W` a wide subcategory of `Atl`, is the wide subcategory of `DaTra` whose
morphisms for `F : X -> Y` have the property that, for any navigation `Nav : Yo A -> Y`, let `P` be the pullback of `F`
and `Nav`, then projection `P' : P -> X` is either empty or there exists a navigation `Nav : Yo B -> X`, along with
a morphism `f : B -> A` in `W`, so that the following square is a pullback:

```
Yo B --------Nav'-------> X
|                        |
| Yo f                   | F
|                        |
⌄                        ⌄
Yo A --------Nav---------> Y
```

11.5. The **Category of Data Transposals**, denoted `DaTrap`, is the DaTra restriction on `AtlTrap`.

11.6. The **Category of Data Traversals**, denoted `DaTrav`, is the DaTra restriction on `AtlTrav`.

11.7. The **Category of Stable Data Traversals**, denoted `DaTras`, is the DaTra restriction on `AtlTras`.

11.8. The **Category of Data Transformation Maps**, denoted `DaTraMap`, is the full subcategory of `DaTra` composed of
the DaTra sets with the property that all of their navigations are expeditions.

## 12. Horizontal Atlases

12.1. The **Empty Atlas**, denoted `AtlI`, is defined as `AtlI = DomInc 0`.

12.2. The **Atlas Horizontal Sum Bifunctor**, denoted as `AtlHorSum : Atl * Atl -> Atl`, is defined as follows: given
two morphisms in `Atl`, `F : X -> Y`, `F' : X' -> Y'`, if `F = AtlI`, then `AtlHorSum F F' = F'` and if `F' = AtlI`,
then `AtlHorSum F F' = F`. Otherwise, `AtlHorSum F F'` is the universal arrow from `Atl` to `R = Y + Y'`, `G : K -> R`,
with the property that there exists morphisms `M : X -> K`, `M' : X' -> K` in `AtlTrav` with `M_E (0, 0) = (1, 0)`,
`M'_E (0, 0) = (1, 1)` so that, for injections `Y_i : Y -> R`, `Y'_i : Y' -> R`, we have `G ∘ M ~= Y_i ∘ F` 
and `G ∘ M' ~= Y'_i ∘ F'`.

12.3. The **Horizontal Lemma** states that `AtlHorSum` exists. Proof sketch: cases where `F = AtlI`, `F' = AtlI` are
trivial. Otherwise, for `F : X -> Y`, `F' : X' -> Y'`, let `T : Atl`, `R = Y + Y'`, `G : T -> R` so that
`|T| = max(|X|, |X'|) + 1`. Then, let `T_G (0, 0) = Ex X + Ex X'`, `R_G (0, 0) = Ex Y + Ex Y'`, and `G_A_(0, 0)` be the
induced mono. Then, for `m` positive integer, let `T_H m = X_H (m − 1) + X'_H (m − 1)`, and for any `n : |A_P m|`, iff
`n < M m`,`T_G (m, n) = X_G (m - 1, n)` and `G_A_(m, n) = F_A_(m - 1, n)`, otherwise,
`T_G (m, n) = X'_G (m - 1, (n - |X_H (m - 1)|))`, `G_A(m, n) = F'_A_(m - 1, (n - |X_H (m - 1)|))`. This fully defines
`G`, which can be checked to be initial among solutions.

12.4. The **Atlas Braider** `AtlBrd_F_F' : (AtlHorSum F F') -> (AtlHorSum F' F)` is defined as follows: if `F = AtlI`
or `F' = AtlI`, `AtlBrd_F_F' = Id`. Otherwise, let `R = (AtlHorSum F F')` and let `G : H -> R` be the universal arrow
from `AtlTrap` to `R` so that `G_E (1, 0) = (1, 1)` and `G_E (1, 1) = (1, 0)`. Then, `AtlBrd_F_F' = inv G`, and
trivially, `AtlBrd_F_F' AtlBrd_F'_F = Id`.

[TODO: figure out associativity flattening]

12.5. The **Atlas Associator**, denoted
`AtlAsoc_F_F'_F'' : (AtlHorSum (AtlHorSum F F') F'') -> (AtlHorSum F (AtlHorSum F' F''))`, is defined as follows:
if `F = AtlI`, `F' = AtlI` or `F'' = AtlI`, then `AtlAsoc_F_F'_F'' = Id`. Otherwise, denote
`R = (AtlHorSum (AtlHorSum F F') F'')` and let `G : H -> R` be the universal arrow from `AtlTrap` to `R` so that
`G_E (2, 0) = (1, 0)` and there exists a morphism `G' : (AtlHorSum F' F'') -> H` in `AtlTrav` so that
`G'_E (0, 0) = (1, 1)`. Then, `AtlAsoc_F_F'_F'' = inv G`.

12.6. The **Atlas Left Unitor** `Lu : (AtlHorSum F AtlI) -> F` and the **Atlas Right Unitor**
`Ru : (AtlHorSum AtlI F) -> F` are given by `Lu = Id`, `Ru = Id`.

## 13. Horizontal Data Traversals

13.1. The **Empty Map**, denoted `I` is the Yoneda Embedding of the Empty Atlas, `I = Yo AtlI`.

13.2. The **Horizontal Sum Bifunctor**, denoted as `HorSum : DaTrav * DaTrav -> DaTrav`, or in infix notation using
the `+_<` symbol, as `DaTrav +_< DaTrav -> DaTrav`, is the Day convolution extension of `AtlHorSum`.

13.3. The **Data Traversal Braider**, denoted `Brd_F_F' : (F +_< F') -> (F' +_< F)`, is the Day convolution extension
of `AtlBrd`.

13.4. The **Data Traversal Associator**, denoted `Asoc_F_F'_F'' : ((F +_< F') +_< F'') -> (F +_< ( F' +_< F''))`, is
the Day convolution extension of `AtlAsoc`

13.5. The **Data Traversal Left Unitor** `Lu : F +_< I -> F`, along with the **Data Traversal Right Unitor**
`Ru : I +_< F -> F`, are given by the Day convolution extensions of `AtlLu` and `AtlRu`.

13.6. The **Data Traversal Monoidal Category**, denoted `DaTravMon`, is given by `DaTravMon = (DaTrav, +_<, I)`. The
coherence conditions can be trivially checked by noting that `Brd`, `Asoc`, `Lu` and `Ru` sent to isomorphisms in
`DaTra`.
