# Datra Maps

## 1. Base Definitions

1.1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1`
(i.e. the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its
morphisms set-theoretic functions (i.e. morphisms in `Set`).

1.2.1. The **Category of Domanial Inclusions**, denoted `DomInc`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. 

1.2.2. The **Category of Codomanial Inclusions**, denoted `CoDomInc`, is the opposite category of `DomInc`, that is,
`CoDomInc = op DomInc`.

1.3.1. The **Category of Domanial Consolidations**, denoted `DomCon`, is the category whose objects are dominions and
morphisms are order-preserving epimorphisms in `Dom`. More specifically, a morphism `F : A -> B` in `DomCon` has the
property that for any `x, y : A`, if `|x| < |y|`, then `|F x| <= |F y|`.

1.3.2. The **Category of Codomanial Consolidations**, denoted `CoDomCon`, is the opposite category of `DomCon`, that
is, `CoDomCon = op DomCon`.

1.4.1. The **Traversal Functor**, denoted `Tra`, is of type `Tra : DomCon -> Set`, and sends each morphism in `DomCon`
to its underlying set-theoretic surjection.

1.5.1. A **Chain** is a strongly connected thin category, taken skeletally.

1.5.2. A **Short Chain** is a chain that is finite.

1.6.1. A **Folio** is a functor from a short chain `C` to `CoDomCon`, `F : C -> CoDomCon`, with the property that 
`F 0 = 1`, where `1` is the singleton set in `CoDomCon`.

1.6.2. Alternatively, a Folio is a functor `F : C -> (1 / CoDomCon)`, where `1 / CoDomCon` is the coslice category,
that preserves colimits.

1.6.3. In fact, to show `F : C -> (1 / CoDomCon)` is a Folio, it is sufficient to show it preserves the initial object.

1.7.1. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(P, E)`, where 
`P = Tra ∘ (op F)`, `F : C -> CoDomCon` is a folio, and `E` is the category of elements of functor `P`. For any
`W : Pag`, we denote `W_P` as the first inclusion and `W_E` as the second inclusion. Morphisms in `Pag`, for
`F : X -> Y`, `X, Y : Pag`, are given by functors `T : X_E -> Y_E`. As such, given two morphisms `f : x -> y`,
`g : y -> z`, where `x, y, z : X_E`, we have that `T f : T x -> T y`, `T g : T y -> T z`, and `T (g ∘ f) = T g ∘ T f`.
By the definition of the category of elements, let `x = (m, i)`, `y = (n, j)`, `z = (p, k)`, then we find that
`X_P f i = j` and `X_P g j = k`, and for let `x' = T x = (m', i')`, `y' = T y = (n', j')`, `z' = T z = (p', k')`, we
find that `Y_P (T f) i' = j'`, `Y_P (T g) j' = k'`. As such, the following diagram commutes for any `f : x -> y`,
`g : y -> z` morphisms in `X_E`:


```
x = (m, i) -----f----- y = (n, (X_P f) i) ------g------  z = (p, (X_P g) ∘ (X_P f) i)
|                      |                                 |
|                      |                                 |
T (m, i)               T (n, (X_P f) i)                  T(p, (X_P g) ∘ (X_P f) i)
|                      |                                 |
|                      |                                 |
x' = (m', i') --T f--- y' = (n', (Y_P (T f)) i') --T g-- z' = (p', (Y_P (T g)) ∘ (Y_P (T f)) i') 

```




























































[TODO: Alternative name: DaTra sets]

1.8. The **Category of Data Transformations**, denoted `DaTra`, is the category of functors from `Pag` to `DomInc`, so
that `DaTra = [Pag, DomInc]`. Alternatively, it is the category of presheaves `DaTra = [op Pag, CoDomInc]`. Given an
identity morphism `X_id` in `DaTra`, its cardinality `|X_id|` is the cardinality of its underlying pagination.

[TODO: terminology notes: `D : DaTra`'s extent = `D 0 0`, `D`'s territory = `D (|D| - 1)`, `D`'s regions = objects
`D (|D| - 1) k`]

[TODO: DaTrav should preserve order when pulled back to the same k-level]

1.9. The **Category of Data Traversals**, denoted `DaTrav`, is the full subcategory of `DaTra` whose morphisms are the
morphisms `F : X -> Y` of `DaTra` so that `alpha_F : X -> Y` is a faithful functor and for all `x : X m k`,
there exists a monomorphism `g : alpha_F x -> x`.

[TODO: category in image of `Ser` referred to as DaTra Maps, or Serene Data Transformations. double terminology
reflects practical usage vs. mathematical definition]

[TODO NOTE: Should be "Charts?" vocabulary? Or just "Mapping Functor?"]

1.10. The **Serenification Functor** `Ser : DaTra -> DaTra` sends morphisms `F : X -> Y` to `F' : X' -> Y`, where 
`F' = F ∘ H` and `H : X' -> X` is the universal arrow in `DaTrav` to target `X` with the property that `H`'s underlying
functor is full, and for set `K` with the property that `k : K` iff `X (|X| - 1) k` is inhabited, for any `m : K`, for
integers `n`, `p` so that `X' n p` is sent to `X (|X| - 1) m`, we have `X' n p ~= X (|X| - 1) m`.

[TODO: A DaTra set is a map (i.e. is serene) iff its extent is isomorphic to the coproduct of its regions]

1.11. The **Coalizing Functor** `Coa : DaTra -> DaTra` sends morphisms `F : X -> Y` to `F' : X' -> Ser F`, where
`F'` is a universal arrow in `DaTrav`. Then, `X'` is referred to as the **Coalition** of `F`, and, in particular, if
`F = id X`, `X'` is the coalition of `X`. Clearly [TODO: Proof outline], `X' m k` is inhabited iff `m = k = 0`, so
that `X'` is isomorphic to an object of `DomInc`, and in fact, as the only morphism is identity in `X'`'s pagination,
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

