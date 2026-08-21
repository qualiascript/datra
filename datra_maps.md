# Datra Maps

## 1. Base Definitions

1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_1` (i.e.
the first uncountable ordinal), that is, its objects are sets that have an injection to `omega_1`, and as its morphisms
set-theoretic injections (i.e. monomorphisms in `Set`).

1.2. The **Category of Domanials**, denoted `Doma`, is the category whose objects are dominions, that is, objects of
`Dom`, and whose morphisms are monomorphisms in `Dom`. The **Category of Codomanials**, denoted `CoDoma`, is the
opposite category of `Doma`, that is, `CoDoma = op Doma`.

1.3. The **Category of Antidomanials**, denoted `ADoma`, is the category whose objects are dominions and morphisms are
epimorphisms in `Dom`. The **Category of Coantidomanials**, denoted `CoADoma`, is the opposite category of `ADoma`,
that is, `CoADoma = op ADoma`. Note that `CoADoma` has no initial object, as the only morphism with origin `0` is
`id_0`, and there is no other morphism with target `0`.

1.4. The **Traversal Functor**, denoted `Tra`, is of type `Tra : ADoma -> Set`, and sends each morphism in `ADoma` to
its underlying set-theoretic surjection.

1.5. A **Chain** is a strongly connected thin category, taken skeletally. A **Short Chain** is a chain that is finite.
For instance, `0 -> 1 -> 2` is the chain of cardinality `3`.

1.6. A **Folio** is a functor from a short chain `C` to `CoADoma`, `F : C -> CoADoma`, with the property that 
`F 0 = 1`, where `1` is the singleton set in `CoADoma`. Alternatively, it is a functor `F : C -> (1 / CoADoma)`, where
`1 / CoADoma` is the coslice category, that preserves colimits. In fact, it is sufficient to show it preserves the
initial object.

1.7. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(P, El)`, where
`P = Tra . (op F)`, `F : C -> CoADoma` is a folio, and `El` is the category of elements of `P`. Morphisms in `Pag` for
`H : X -> Y` are given by natural transformations `alpha : X_El -> Y_El`.
