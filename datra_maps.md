# Datra Maps

## 1. Base Definitions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1` (i.e.
the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its morphisms
set-theoretic injections (i.e. monomorphisms in `Set`).

1.2. The **Category of Domanial Sets**, denoted `DomSet`, is the category of presheaves on `Dom`, that is
`DomSet = [op Dom, Set]`. The **Category of Codomanial Sets**, denoted `CoDomSet` is the opposite of the category of
domanial sets, that is, `CoDomSet = op DomSet`.

1.3. The **Category of Domanial Inclusions**, denoted `DomInc`, is the reflective subcategory of `DomSet` whose
morphisms are precisely the monomorphisms in `DomSet`. The **Category of Codomanial Inclusions**, denoted `CoDomInc`,
is the opposite category of `DomInc`, `CoDomInc = op DomInc`.

1.4. The **Category of Antidominions**, denoted `AntDom`, has the same objects as `Dom`, and a morphism `f : X -> Y`
for `X, Y : AntDom` is a set-theoretic surjection (i.e. epimorphism) `f : Y -> X`. Note that this category has no
initial object, as the only morphism with origin `0` is `id_0`, and there is no other morphism with target `0`.

1.5. The **Traversal Functor**, denoted `Tra`, is of type `Tra : op AntDom -> Set`, and sends the opposite of each
morphism `f : X -> Y` in `AntDom` to `f' : |Y| -> |X|` in `Set`, so that `f'` is the underlying surjection of `f` in
`AntDom`.

1.6. A **Chain** is a strongly connected thin category, taken skeletally. A **Short Chain** is a chain that is finite.
For instance, `0 -> 1 -> 2` is the chain of cardinality `3`.

1.7. A **Pagination** is a functor from a short chain `C` to `AntDom`, `P : C -> AntDom`, with the property that 
`P 0 = 1`, where `1` is the singleton set in `AntDom`. Alternatively, it is a functor `P : C -> (1 / AntDom)`, where
`1 / AntDom` is the coslice category, that preserves colimits. In fact, it is sufficient to show it preserves the
initial object.

[TODO: check naturality condition]
1.8. The **Category of Paginations**, `Pag`, is the category whose objects are pairs `(D, El)`, where
`D = Tra . (op P)`, `P : C -> AntDom` is a pagination, and `El` is the category of elements of `D`. Morphisms in `Pag`
for `F : X -> Y` are given by natural transformations `alpha : X_D -> Y_D`, so that the corresponding functor
`H : X_El -> Y_El` is faithful.

[TODO: Data Traversals Category (?) and DaTra maps]