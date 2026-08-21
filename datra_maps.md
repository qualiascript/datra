# Datra Maps

## 1. Base Definitions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1` (i.e.
the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its morphisms
set-theoretic injections (i.e. monomorphisms in `Set`).

[TODO: sheaf condition?]
1.2. The **Category of Domanial Inclusions**, denoted `DomInc`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. The **Category of Codomanial Inclusions**, denoted
`CoDomInc`, is the opposite category of `DomInc`, that is, `CoDomInc = op DomInc`.

1.3. The **Category of Domanial Consolidations**, denoted `DomCon`, is the category whose objects are dominions and
morphisms are order-preserving epimorphisms in `Dom`. The **Category of Codomanial Consolidations**, denoted
`CoDomCon`, is the opposite category of `DomCon`, that is, `CoDomCon = op DomCon`. Note that `CoDomCon` has no initial
object, as the only morphism with origin `0` is `id_0`, and there is no other morphism with target `0`.

1.4. The **Traversal Functor**, denoted `Tra`, is of type `Tra : DomCon -> Set`, and sends each morphism in `DomCon` to
its underlying set-theoretic surjection.

1.5. A **Chain** is a strongly connected thin category, taken skeletally. A **Short Chain** is a chain that is finite.
For instance, `0 -> 1 -> 2` is the chain of cardinality `3`.

1.6. A **Folio** is a functor from a short chain `C` to `CoDomCon`, `F : C -> CoDomCon`, with the property that 
`F 0 = 1`, where `1` is the singleton set in `CoDomCon`. Alternatively, it is a functor `F : C -> (1 / CoDomCon)`,
where `1 / CoDomCon` is the coslice category, that preserves colimits. In fact, it is sufficient to show it preserves
the initial object.

1.7. The **Category of Paginations**, denoted `Pag`, is the category whose objects are the categories of elements of
functors `P`, where `P = Tra ∘ (op F)` and `F : C -> CoDomCon` is a folio. Morphisms in `Pag` for `H : X -> Y` are
given by functors `alpha_H : X_El -> Y_El`. [TODO: check connections with natural transformations]. The **Cardinality
of a Pagination** is defined on Pagination objects `P` as the highest positive integer so that `P k` is inhabited, and
is denoted `|P|`.

1.8. The **Category of Data Transformations**, denoted `DaTra`, is the category of functors from `Pag` to `DomInc`, so
that `DaTra = [Pag, DomInc]`. Alternatively, it is the category of presheaves `DaTra = [op Pag, CoDomInc]`. Given an
identity morphism `X_id` in `DaTra`, its cardinality `|X_id|` is the cardinality of its underlying pagination.

1.9. The **Category of Data Traversals**, denoted `DaTrav`, is the full subcategory of `DaTra` whose morphisms are the
morphisms `F : X -> Y` of `DaTra` so that `alpha_F : El_X -> El_Y` is a faithful functor and for all `x : El_X m k`,
there exists a monomorphism `g : alpha_F x -> x`.

1.10. The **Stabilizing Functor** `Sta : DaTra -> DaTra` sends morphisms `F : X -> Y` to `F' : X' -> Y`, where 
`F' = F ∘ H` and `H : X' -> X` is the universal arrow in `DaTrav` to target `X` so that there exists `k` a positive
integer so that `k = |X| = |X'|` and `H X' k ~= X k`.

1.11. The *Coalizing Functor* `Coa : DaTra -> DaTra` sends morphisms `F : X -> Y` to `F' : X' -> Sta F`, where
`F'` is a universal arrow in `DaTrav`. Then, `X'` is referred to as the **Coalition** of `F`, and, in particular, if
`F = id X`, `X'` is the coalition of `X`. Clearly [TODO: Proof outline], `X' m k` is inhabited iff `m = k = 0`, so
that `X'` is isomorphic to an object of `DomInc`, and in fact, as the only morphism is identity in `X'`'s pagination,
to an object of `Dom`. As such, to each arrow of `Coa`, one obtains an arrow `f : DaTra -> Dom`, mapping `DaTra`
objects to `Dom` objects, and as such, a forgetful functor `Forg : DaTra -> Dom`. Then let `Free : Dom -> DaTra`
be the free functor sending each dominion to its coalition. Clearly, `Free Forg Free x = Free x` and
`Forg Free Forg y = Forg y`, so that `Free` is left adjoint of `Forg`.

1.12. The **Sequential Bifunctor**, `(;) : DaTra * DaTra -> DaTra`, also denoted infix as `DaTra ; DaTra -> DaTra`,
is defined for `F : X -> Y`, `F' : X' -> Y'`as follows: let `G = Coa F`, `G' = Coa F'`, then `F ; F'` is the `DaTrav`
object `H` on pagination `1 -> 2 -> |F| + |F'|` so that `H (1 -> 2) 0 = F` and `H (1 -> 2) 1 = X'`.