# DaTra: A Representable Topos Theory for Data Transformation on Partial Maps With Partially Variable Argument Order [WIP]

> In this document, we provide the categorical construction of the `DaTra` topos, whose objects, denoted **DaTra
> Maps**, are partially named partial maps with partially variable argument order. DaTra maps can have a finite number
> of arguments, denoted a **DaTra Literal**, or a countably infinite number of arguments, denoted a **DaTra Sequence**.
> The morphisms in **DaTra**, denoted **repaginations**, restructure DaTra maps while preserving order with or without
> information loss. We show that all DaTra maps are representable by **Atlases**, which have a clearly defined,
> computationally-friendly structure. In this regard, we define **Domanial Sets** as the underlying data of DaTra maps,
> and prove that there is a geometric morphism between the DaTra maps topos and the domanial sets topos. We provide a
> definition for **DaTra functions**, which utilize DaTra maps to the fullest extent to provide the semantics for
> overriding default values in the function's domain, as well as order-preserving restructuring to pattern-match the
> partially variable argument order. Finally, we introduce the concept of **Folio Sums**, which are able to follow a
> strategy to combine a potentially countably infinite number of DaTra maps, while ensuring no data loss in the process.

## Section I: Foundations

I.1.1. An **Order** is an isomorphism `F : X -> X` where `X` is a conatural number, `X : N+`. An **Order's
Cardinality**, given `F : X -> X`, is `X`. It is denoted as `|F|`.

I.1.2. The **Category of Orders** is denoted `Ord` and has orders as its objects. An **Order Embedding** is a morphism
in `Ord`, `Emb : A -> B`. It is a monomorphism `F : |A| -> |B|` with the property that for any `x , y : |A|`,
`A x < A y` iff `F (A x) < F (A y)`.

I.1.3. An **Order Embedding's Image** given `Emb : A -> B` is the domain of the monomorphism `M : B' -> B` so that for
each `b : B` there exists a `m : B'` so that `M m = b` iff there exists a `a : A` so that `Emb a = b`. It is denoted
`Img Emb`.

I.1.4. A **Trivial Order** of cardinality `X : N+` is the order `id X`. A **Trivial Order Embedding**, given
`X, Y : N+`, is an order embedding on trivial orders `Emb : id X -> id Y`.

I.1.5. **Ordering Lemma**: given two orders `A, B : Ord` and a subset of `B` denoted `B'`, there exists a unique order
embedding with origin `A` and image `B'`. Proof: let `X, Y : A -> B` be order embeddings with image `B'`. Let
`X', Y' : A -> B'` be isomorphisms so that `X' a = X a` and `Y' a = Y a` for all `a : A`. Then, for the monic
`M : B' -> B`, we have that `X = M . X'` and `Y = M . Y'`. Let `Z : B' -> |B'|` be an isomorphism so that for all
`x, y : B'` so that `x < y`, `Z x < Z y`. We seek to show `Z` is unique by the following argument: assume
`Z' : B' -> |B'|` is another isomorphism sharing the same property. If they are distinct, there is `z : B'` so that
`Z z =/= Z' z`. Let `z' : B'` be the value so that `Z' z' = Z z`. Naturally, `z =/= z'`, so that either `z < z'` or
`z' < z`. In the former case, `Z z < Z z'` but `Z' z < Z' z' = Z z`, thus `z` does not exist. Analogous for the other
case. As such, `Z` is unique, so that for `X', Y' : A -> B'`, there are unique isomorphisms `X'', Y'' : A -> |B'|`,
that is, `X'', Y'' : A -> A` so that `X'' = Z . X'` and `Y'' = Z . Y'`. As such, `X''` and `Y''` have the property that
for all `a, b : A`, if `X a < X b`, `X'' a < X'' b`, and analogous for `Y` and `Y''`.  We may then consider
`X'', Y'' : |B'| -> |id |B'||` by isomorphism, and by analogy to `Z`, `X'' = Y''`, so that `X = Y`.

I.1.6. An **Order Embedding's Complement**, given an order embedding `Emb : A -> B` with image `B'`, is the trivial
order embedding with image `X`, where `x : X` iff it is not the case that `x : B'`. It is denoted
`Comp Emb`.

I.2.1. A **Regime** is a morphism `R : X -> A` where `X : N+`, denoted its **Cardinality** as `X = |R|`.

I.2.2. A **Regime's Region Set**, given a regime `R : X -> A`, is denoted `Rgo R`, and it is defined as the subobject
of `X * A`, which we denote as `Rgo R <: X * A`, with the property that `(x, a) : Rgo R` iff `R x = a`

I.2.3. A **Regime Inclusion** of two regimes `R1 : X -> A`, `R2 : Y -> A` is a monomorphism `RegInc : Rgo R1 -> Rgo R2`
whose projection `F : X -> Y` is a trivial order embedding on `X` and `Y`. The order embedding of a regime inclusion is
denoted `OrdEmb RegInc`.

I.2.4. A **Regime Reduction** of two regimes `R1 : X -> A`, `R2 : Y -> A` is an epimorphism `RegRed : Rgo R1 -> Rgo R2`
so that, given any section `Sec : Rgo R2 -> Rgo R2` so that `RegRed . Sec = id`, it is a regime inclusion.

I.2.5. An **Expansion** is a regime inclusion `Exp : N -> M` with the property that for `(n, k) : Rgo N`,
`(n', k') : Exp (n, k)` we have `k <: k'`.

I.2.6. The **Category of Regimes** `Reg` has as its objects regimes, and morphisms for `X, Y : Dom`, `F : X -> Y`
denoted **Annexations**, which are defined as expansions `Anx : X -> Y` with the property that for `(n, k) : Rgo X`,
`(n', k') : Anx (n, k)` we have `k = k'`.

I.2.7. The **Subexpansion Family** of an expansion `Exp : N -> M` is the collection obtained by precomposing `Exp` with
all annexations in the Yoneda embedding of `N`, that is, `Exp . Anx_i` for all `Anx_i : Yo N`.

I.2.8. The **Category of Dominions** `Dom` has as its objects regimes, and morphisms for `M, N : Dom`, `F : M -> N`,
denoted **Consolidations**, are regime inclusions `Cons : Z -> M` so that for `(m, z) : Rgo Z`,
`(m', z') : Cons (m, z)`, we have `z : z'`. Additionally, consolidations must fulfill the condition that the unique
`Exp : N -> M` so that `OrdEmb Exp = Comp OrdEmb Cons`, is an expansion.

I.2.9. The **Serene Dominion Site** `SerDom` is the site induced on `Dom` by the **Serenity Axiom**: a dominion's
covering family consists of the consolidations whose expansions are part of a given subexpansion family. Lemma:
`SerDom` is a site. Proof: given a dominion `M`, its maximal sieve is the subexpansion family of expansion `id Reg M`.
Stability under base change is induced by precomposing the given expansion with the consolidation's expansion, thus
obtaining another subexpansion family. The local character condition is induced by the fact that, if by pulling back a
sieve on the consolidations whose expansions are annexations, one obtains subexpansion families, that is in itself a
subexpansion family.

I.3.1. The **Category of Domanial Sets** is the category of sheaves on `SerDom`. It is denoted `DomSet`, and as it is
a category of sheaves, it is a topos.

I.3.2. A **Domanial Atom** is a domanial set that is the Yoneda Embedding of a regime with cardinality `1`.

I.3.3. **Domanial Atomicity Lemma**: all domanial sets are coproducts of atoms. Proof: given a representable domanial
set `X`, by the serenity axiom, there is an expansion family `Exp : 1 -> X` on each region. By the property that each
matching family has a unique amalgamation, this is isomorphic to the coproduct of `|X|` domanial atoms. As coproducts
are associative, the coproduct of representable domanial sets, which are coproducts of atoms, is itself a coproduct of
atoms. Given a pushout of coproducts of domanial atoms, between `F : A -> B` and `G: A -> C` the result can be
calculated atom-wise, by creating equivalence classes on isomorphic atoms in `F` and `G` and calculating the coproduct
of the resulting atom set. By the Density Theorem, all domanial sets are the result of colimits, which can be composed
of coproducts and pushouts, thus this is sufficient.

I.3.4. A **Federation** is a collection of domanial sets whose coproduct in the presheaf category `[op Dom, Set]` is
isomorphic to its sheafification to `DomSet`. A **federalization** is a sheafification from `[op Dom, Set]` to
`DomSet`. Lemma: federations are sets of domanial sets whose elements are pairwise disjoint. Proof: Given a presheaf
coproduct, if two of its elements have common inhabitants, this does not respect the serenity axiom, and as such its
federalization cannot be an isomorphism.

I.3.5. A **Domanial Map** is a regime `DMap : X -> DomSet`. A **Domanial Map's Territory** is the coproduct in
`DomSet` on diagram `DMap`.

I.3.6. A **Region of a Domanial Map** is an element of its region set, so that for `DMap : X -> DomSet`, we have
`(x, k) : Rgo DMap <: X * DomSet`. A **Region's Indexing** is the projection on the first component, and a **Region's
Territory**, or **Arrow**, is the projection on the second component.

I.4.1. A **Pagination** is an epimorphism `Pag : B -> A` where `A, B : N`.

I.4.2. A **Pagination's Fiber Map**, given a pagination `Pag : B -> A`, is a monomorphism `FibM : A -> 2 ^ B` so that
for any `a : A`, `x : FibM a` iff `Pag x = a`. It is denoted `Fib Pag`.

I.4.3. A **Folio** is a pagination `Fol : |B| -> |A|` along with two orders `A, B : Ord` so that given any section
of `Fol`, that is, a morphism `Sec : |A| -> |B|` so that `Fol . Sec = id |A|`, `Sec` is an order embedding with origin
`A` and target `B`.

I.4.4. A **Chart** of cardinality `K` is a monomorphism `Chrt : X -> Ord`, so that for any `x : X`, `|Chrt x| = K`,
and there exists `y : X` so that `Chrt y = id K`. The **Trivial Chart** is the chart `Chrt : 1 -> Ord`.

I.4.5. A **Complete Chart**, or **Reverse Chart**, of cardinality `K` is a chart `Chrt : X -> Ord` of cardinality `K`
so that for any `k : K` there exists `x : X` so that for all `a, b : N`, `a < b <= k`, `Chrt x a > Chrt x b`.

I.4.6. A **Navigable Pagination**, given a chart `Chrt : X -> Ord` with cardinality `B`, is a pagination `Pag : B -> A`
so that, for any `x : X`, `Pag` is a folio on `id A` and `Chrt x`.

I.4.7. A **Collapsed Pagination** is an epimorphism `Pag : B -> 1`, so that `Pag ~= B`. Lemma: if a pagination is
navigable by the complete chart, it is a collapsed pagination. Proof: given pagination `Pag : B -> A`, for any
`a : A`, `Pag` has all sections `Emb : A -> B` so that if `x, y : A`, `x < y`, `Emb x < Emb y`. Furthermore, `Pag`
has all sections `Emb' : A -> B` so that if `x, y : A`, `x < y`, `Emb' x > Emb' y`. This is only vacuously true if
there are no `x, y : A` so that `x < y`, which is the case if `A = 1`.

I.4.8. A **Chart's Minimal Pagination** is a pagination `Pag : B -> A` that is navigable by `Chrt : X -> Ord` so that,
given a distinct pagination `Pag' : B -> C` navigable by `Chrt`, for `FibM = Fib Pag`, `FibM' = Fib Pag'`, if
`x : N` is the smallest value so that for any `y : N`, `y < n`, `FibM y = FibM' x`, then `|FibM x| < |FibM' x|`.
Lemma: given a chart, its minimal pagination is unique up to isomorphism. Proof: `Pag` navigates all sections so that
if `x, y : A`, `x < y`, `Emb x < Emb y`, hence it is uniquely determined by `F : A -> N` so that for `a : A`,
`F a = |FibM a|`.

I.5.1. The **Category of Atlases** `Atl` has as its objects domanial maps `DMap : A -> DomSet`, and its morphisms
`F : X -> Y`, `X, Y : Atl` are denoted **Incorporations**, and are defined as follows: An incorporation between
`X` and `Y` is a regime reduction `RegRed : Rgo X -> Rgo Y`. Given the morphism `Fibr : Y -> 2 ^ X` so that for
`y : Y`, `x : Fibr y` iff `RegRed x = y`, let `RegCop : Y -> DomSet` so that `RegCop y` is the coproduct in `DomSet`
on diagram `Fibr y`. Then, incorporations fulfill the condition that for all `y = (n, y') : Rgo Y`, `y' <: RegCop y`.

I.5.2. A **Regional Pagination**, given an incorporation `Inc : Rgx X -> Rgo Y` is the pagination obtained on the order
value projection of `Rgo X` and `Rgo Y`. Lemma: all incorporations have a regional pagination that is navigable by the
trivial chart. Proof: It is an epimorphism whose sections have a trivial order embedding.

I.5.3. The **Cartographic Atlases Site** `CartAtl` is induced on `Atl` by the **Cartography Axiom**: given any atlas,
its covering families are the incorporations whose regional paginations are navigated by a given chart. Lemma:
`CartAtl` is a site. Proof: the maximal sieve is determined by the trivial chart. Stability under base change is
conferred by the incorporation precomposition's regional pagination. The local character condition is conferred by the
incorporation whose regional pagination is minimal under the chart, which yields another minimal regional pagination
so that the original chart can be reconstructed by incorporation composition.

I.6.1. The **Category of Data Transformation Sets**, or simply **DaTra Sets**, is the category of sheaves on the
Cartographic Atlas Site. It is denoted the `DaTra` topos.

I.6.2. The **Repagination** of a representable DaTra set morphism `A, B : DaTra`, `F : A -> B` is a morphism on the
atlas's region sets `Rep : Rgo A -> (Rgo B) ^ 2` with the property that, by projecting to its indexing, one obtains
the fiber map of the incorporation `Inc : Rgo B -> Rgo A`.

I.6.3. The **Repagination Lemma** states that all DaTra morphisms are repagination. In other words, all DaTra sets
are representable. Proof: by the universal property, morphisms whose origin is the coproduct of representable DaTra
sets are equivalent to a collection of morphisms from each representable DaTra set. Each representable DaTra set is
equivalent to its region set, which forms a federation by virtue of being pairwise disjoint at the projection of their
indexing. As such, each coproduct of representable DaTra sets has a canonical representation as a domanial set. Given a
wide pushout of representable DaTra sets, by the universal property and cartography axiom, it is the result of the
incorporation of the coproduct of the pushout targets defined as follows: it is the incorporation with the minimal
pagination on the chart containing the collection of orders that navigate by the minimal pagination of each component
in the pushout's targets. By the Density Theorem, as coproducts and pushouts preserve representability, all DaTra sets
are representable.

I.6.4. The **DaTra Free Functor** `DaTraFree : DomSet -> DaTra` sets domanial sets to the DaTra sets whose region set
has cardinality `1`, and whose unique arrow is the given domanial set. The **DaTra Forgetful Functor**
`DaTraForget : DaTra -> DomSet` sets DaTra sets to the federation equivalent to its region set. Lemma: `DaTraFree` is
left adjoint to `DaTraForget`. Proof: given `X : DomSet`, `Y : DaTra`, `hom(DaTraFree X, Y)` consists of
repaginations `Rep : 1 -> (Rgo Y) ^ 2`, that is `Rep <: Rgo Y`. Furthermore, `hom(X, DaTraForget Y)` consists of the
subobjects of `Y`'s region set federation. Thus, `hom(DaTraFree X, Y) ~= hom(X, DaTraForget Y)`.

I.6.5. The **Coalizing Geometric Morphism** is the geometric morphism consisting of the pair of `DaTraFree` and
`DaTraForget` Lemma: `DaTraFree` and `DaTraForget` form a geometric morphism. Proof: it is sufficient to show that
`DaTraFree` preserves all limits. This can be trivially seen by reversing all arrows.

I.6.6. The **Coalizing Comonad** is the comonad defined as `Coa = DaTraFree . DaTraForget`. A **DaTra set's
Coalition**, Given any `x : DaTra`, is the result of `Coa x`. Lemma: `Coa` is an idempotent comonad. Proof: as it is a
comonad induced by a geometric morphism.

I.6.7. The **Category of Self-Enriched DaTra Sets** is the category of `DaTra` enriched on `DaTra`. By slight abuse of
notation, we will refer to this category as simply `DaTra`, and to self-enriched DaTra sets as simply DaTra sets. The
base case, of DaTra sets whose arrows are domanial sets, is provided by the DaTra sets that are coalitions.

1.6.8. **DaTra Flattening** is a property of DaTra sets representable by atlases whose arrow set has infinite
cardinality and whose arrows have finite cardinality, or whose arrow set has finite cardinality and all but the last
arrow has finite cardinality. By the product-exponent adjunction and repagination, such a DaTra set is representable
by an atlas so that each arrow is written under the form of a collection of arrows. As such, DaTra sets do not, in
general, have a canonical arrow set. One can define a DaTra sets by providing the value at each arrow, however, the
result is representable im multple ways. As we will soon see, one can talk of the arrow sets of DaTra maps instead.

I.6.9. A **DaTra Remapping** is a DaTra set that is a repagination with the property that all region are sent to a
DaTra set repeatable by an atlas so that the coproduct of its arrows equals the given region's arrow.

## Section II: DaTra Maps

> Note: In order to differentiate between DaTra notation and mathematical notation, square brackets will be used for
> DaTra notation, so that `[X]` means that the content inside ought to be considered as DaTra notation. We will clarify
> the exact meaning of this notation shortly.

II.1.1. The **DaTra Natural Numbers Set** is the coalition of the total DaTra set representable by an atlas of
cardinality `N` so that given any region, its arrow is `1`. As such, it is denoted `[N]`. Its elements can be written
by their base 10 decimal expansion, such as `[123]`.

II.1.2. The **ASCII Map** is the coalition of the total DaTra set induced by the atlas with cardinality `128`, so that
given any region, its arrow is `[1130914162]`, which as we will later see, is the natural number encoding for the DaTra
string `[\Char\]`.

II.1.3. A **DaTra String** is a DaTra literal enumeration so that given any arrow, its target is the ASCII Map. A
**DaTra Canonical String** is a string so that given any arrow, let the region of the ASCII Map in its target be
`(n, k) : 128 * {[\Char\]}`, then `48 <= n < 57` or `65 <= n <= 90` or `97 <= n <= 122` or `n = 95` or `n = 39`. As
such, we denote a canonical string by writing the ASCII characters corresponding to each value in sequential order,
enclosed by `\` characters, for instance, `[\String\]`.

II.1.4. A **String's Natural Encoding** is defined on region sets as follows: given a DaTra string `Str`, its regions
are `(n, x, Char) : Rgo Str`. Then, its natural encoding is the coproduct of `128 ^ n * x` for all `n`. By usual base
128 reasoning, given two distinct DaTra strings, their natural encoding is distinct. The natural encoding of `[\Char\]`
is `[1130914162]`.

II.1.5. The **Imbue Operator** given two DaTra sets `A, B : DaTra` is a coalition whose arrow has origin `A * B`
and target `Coa B`, and it is a projection of the first component. It is denoted using the `<~` symbol, for instance,
`[\x\ <- N]`.

II.1.6. The **Type Definition Operator** is similar to the imbue operator, but its first argument is a canonical string
not enclosed in `\`. It uses the `:` symbol, and is defined as `[A : B] = [\A\ <~ B]`. A **DaTra Labeled Type** is the
result of the application of the type definition operator, and `B` is denoted a **DaTra Type**. For instance, the
**ASCII Character Type** is defined as `[Char : 128]`. In practical settings, a more inclusive encoding such as UTF-8
is preferable.

II.1.7. The **Assignment Operator** is defined on a DaTra type, along with a DaTra coalition with origin `1` and target
as the same target as the DaTra type. In that case, it is the pullback of the two DaTra coalitions. It is denoted using
the `:=` symbol. For instance, `[x : N := 3]` yields a coalition with origin `[\x\]` and target as the fourth arrow of
`N`. As such, this provides the semantics for assigning labels to values. In this context, `x` is denoted a **Simple
Identifier**, as it maps one canonical string to its value.

II.1.8. A **Natural String Encoding** is a monomorphism mapping each natural number to a string. We select a
**Canonical Natural String Encoding** to be used in future operations. Notation-wise, we write the natural string
encoding of `3`, for instance, as `\3\`, and in general, each natural number is denoted by itself as a string in base
ten.

II.1.9. The **Sequential Operator**, or the **Horizontal Sum Operator** is defined on an ordered finite or countably
infinite collection of DaTra sets, denoted `X`, and each element denoted `X_k` for `k : |X|` where `|X|` is the
collection's cardinality. The result is a DaTra set defined on the atlas whose `k`th arrow is `[k : X_k]`. It can be
denoted using the **DaTra Literal Notation**, by writing each element sequentially in order, delineated by `;` and
enclosed by `[` at the beginning and `]` at the end. For instance, given two DaTra sets `A, B :: DaTra`, it yields the
DaTra set `[0 : A, 1 : B]`. 

II.2.1. A **DaTra Map** is the result of the application of the sequential operator. A **DaTra Map's Arrow Set** is
defined so that the `k`th arrow is the map `X_k` at the arrow `[k : X_k]`. As such, if `X` is a DaTra map, we define
`X k = X_k`, and we denote it the **DaTra Map's `k`th arrow**. A **DaTra Map's Territory** is the DaTra set represented
by the DaTra map's arrow set as an atlas. It is denoted `Ter X`, where `X` is a DaTra map. A **DaTra Map's
Cardinality** is the cardinality of its arrow set, and it is denoted as `|X|`.

II.2.2. A **DaTra Enumeration**, or **DaTra Total Map** is a DaTra map whose arrows are domanial sets with origin `1`.
A **DaTra Partial Map** is a DaTra map that is not a DaTra enumeration.

II.2.3. A **DaTra Sequence** is a DaTra map with cardinality `N`. A **DaTra Literal** is a DaTra map that is not a
DaTra sequence.

II.2.4. The **Concatenation Operator** is defined on a DaTra literal and a DaTra map, and yields a Datra map. It is the
DaTra map defined arrow-wise as follows: Let `X` be the cardinality of the literal's arrow set, then for all `x : X`,
the resulting map has as its `x`th arrow the `x`th arrow of the literal, and as its `X + y`th arrow the `y`th arrow of
the DaTra map. It is denoted using the `,` symbol, for instance, `[[x : N, y : N]] , [z : N]] = [x : N, y : N, z : N]`.
In particular, it yields the concatenation of two strings, so that `[\Hello_\, \world\] = [\Hello_world\]`. By the
flattening property, we have that, given `A`, `B`, `C` are literals, `[[A, B], C] = [A, B, C]`.

II.2.5. A **DaTra Collection** is a DaTra map whose arrows are DaTra maps of cardinality `1` so that the arrow's origin
is isomorphic to its target. A **DaTra Collection's Element** is one of its arrows. In this sense, the sequential
operator can be seen as operating on a DaTra collection.

II.2.6. A **Datra Confederation** is a DaTra map whose arrow set, viewed as a constant presheaf in `[op Dom, Set]`,
that is, viewed as a set-theoretic set, has trivial federalization.

II.2.7. A **Reordering** of a DaTra map `X`, whose territory has as target a confederation, `Ter X : A -> B`, and an
order embedding `OrdEm : |B| -> C` is the DaTra map `Y` with territory `Ter Y : A' -> B'` with the following property:
for any `x : |B|`, `x' = Img OrdEm x`, `Y x = X x'`. Trivially, `Coa B = Coa C`. It is denoted as `Reord X OrdEm = Y`.
The **Reindexing** of two DaTra Maps `X`, `Y` with territories denoted `Ter X : A -> B`, `Ter B : C -> D`, if it
exists, is the unique order embedding `OrdEm : |B| -> |D|` so that `Y = Reord X OrdEm`. Such a reindexing exists iff
for any `x : |B|` there exists `x' : |D|` so that `B x = D x'`, and for any `x''` so that `B x = D x''`, `x' = x''`.

II.2.8. A **Maximal Confederation** of a confederation `X` is a confederation `Y` so that there exists a remapping
`F : Ter X -> Ter Y`, and for any other confederation `Z` and remapping `G : Ter X -> Ter Z`, `|Z| <= |Y|`.

II.2.9. A **Restructuring** of a DaTra map `X` is a DaTra map `Y`, so that there exists a DaTra set `Z` so that there
exist two remappings, `X' : Ter X -> Z`, `Y' : Ter Y -> Z`. Lemma: if `X, Y : DaTra` are confederations, `Y` is a
restructuring of `X` iff there exists `Z : DaTra` so that `Z` is a maximal confederation for both `X` and `Y`. Proof:
`Z` has the property that the arrows in its arrow set are pairwise disjoint, but there is no DaTra coproduct of arity
higher than `1` equal to any arrow, which can be used in a repagination. Specifically, for the arrow with the highest
cardinality, if it exists, it has no coproduct decomposition whose cardinality lies in `N+`. For the other arrows, they
have no decomposition whose cardinality lie in `N`. Thus, `Z`'s only remapping is `id Z`. Thus, given any other `Z'`
that is a confederation whose confederation is the target of a remapping of `X` and `Y`, there exists a maximal
confederation `Z_i` for confederation `Z'`.

II.3.1. The **Federation Operator** coalizes a DaTra confederation's arrow set, but is not defined on DaTra maps that
are not DaTra confederations. Its result is denoted a **DaTra Federation**. It is denoted by enclosing a DaTra map in
`{` at the beginning and `}` and the end, and if the DaTra map is written in literal notation, it accepts literals
stripped of their `[]` enclosing. For instance, we have that `{a : N; b : N}` is a valid application of the federation
operator, but `{N; N}` is not, as it has non-trivial federalization. One can still coalize `[N; N]`, however, by using
the **Coalition Operator** `><`, which coalizes any DaTra map's arrow set.

II.3.2. The **Union Operator** is equivalent to a pullback in the `DaTra` category, and as such is defined on
DaTra maps of equal cardinality with isomorphic targets arrow-wise. If it is defined, its action is to compute the
pushout of the origins of each pair of arrows and use it as the new arrow origin. It is denoted using the `&` symbol.
For instance, `[[x : N := 1; y : N; z : N := 2] & [x : N; y : N := 2; z : N := 3]]` is equal to
`[x : N := 1; y : N := 2, >< [z : N := 2; z : N := 3]]`. Note the usage of the coalition operator. The **Safe Union
Operator**, denoted using the `<>` symbol, has the same action as the union operator but is only defined if there is
no overlap of distinct origins with the same target, that is, no necessity to coalize.

II.3.3. The **Override Operator** given two DaTra maps, `X, Y : DaTra` is equivalent to the composition of the
projection `Pr_Y : X & Y -> Y` with `Y`, `Y . Pr_Y`. As such, it is similar to the union operation, but prefers the
origins provided by the second map in case of conflict, instead of coalizing. It is denoted using the `<<` operator.
For instance, `[[x : N := 1; y : N; z : N := 2] << [x : N; y : N := 2; z : N := 3]]` is equal to
`[x : N := 1; y : N := 2; z : N := 3]`. Hence, the override operator provides the semantics for overriding
default values in `DaTra`, with the origins of the arrows of the first map playing the role of the default values.

II.3.4. The **Binary Sum Operator** is the coproduct of the territories of two DaTra maps, which is a coalition
regardless of whether the given DaTra maps are coalitions. It is denoted using the `+` operator, for instance,
`[5] = [2 + 3]`.

II.3.5. The **Binary Product Operator** is the product of the territories of two DaTra maps. More specifically, it is
the coalition of all arrows with origin as an inhabitant of the first map, and target as an inhabitant of the second
map. It is denoted using the `*` operator, for instance, `[15] = [3 * 5]`.

II.4.1. The **Map Application Operator**, or **Map Filling Operator**, of two DaTra maps `X, Y : DaTra`,
denoting `X'` as `X`'s territory and `Y'` as `Y`'s territory. It is defined if there exists a unique `Z` whose
territory `Z'` is a restructuring of `Y'`, so that there exists a trivial order embedding `OrdEm : id |Z| -> id |X|` 
sending each arrow to an arrow with the same target. Furthermore, there is the additional constraint that `OrdEm` is
unique, which is trivially the case if `X`, `Y` are confederations and `Z` exists. It is defined as follows: it is
the territory of the canonical DaTra map `C` with cardinality `|X|`, so that for all `(n', d') : Rgo C`, if
`n' : Img OrdEm`, for `(n, d) : Rgo Z` so that `n' = OrdEm n`,`d' = d`, and otherwise, `d' = X n`. Then, the map
application, denoted using the `<&` symbol as `[X <& Y]`, is defined as `[X <& Y] = C`. By definition, `C = [C << Y]`,
so that if `X'`, `Y'` have the same target, `[X <& Y] = [X << Y]`. Hence, map application is an extension of the
override operator to allow the restructuring of `X` when unique.

II.3.2. The **Function Type Operator** is defined on two DaTra maps, `A, B : DaTra`. It is denoted using the `->`
symbol, and defined as follows: let `A : V -> A'`, let `F = hom_DomSet[DaTraForget B, DaTraForget A]`, applied
contravariantly as to account for the arrow reversal in the adjunction, then `[A -> B] = [(A ; B) <~ F]`.
Alternatively, `F` can be constructed as a `DaTra`-internal collection of sections of `[B <~ A]`. A **DaTra Function**
is the result of applying the assignment operator to a function type, so that for `[A -> B := C]`, the resulting
function is a map of form `[[A, B] -> [F := C]]`. The **Origin Map** of a DaTra function `[A -> B := C]` is `A`, and
the **Target Map** is `B`.

II.3.3. The **Function Application Operator**, or **Access Operator**, is defined on a DaTra function, along with a
DaTra map with the property that the map application of the given map on the origin map yields a total map. Then, for
`[A -> B := C]`, `A = [X -> A']`, denoting the map as `M : X' -> A'`, let `V = [A <& M]`, then `V : 1 -> A'`. Let `B'`
be the coalizing morphism `B' : Coa B -> B`. As such, the function application operator is defined as `R = B' . C . V`.
It is denoted by the `.` symbol, with the value to be applied as the first argument and function as second argument,
so that for `F = [A -> B := C]`, `A : V -> A'`, `x : V' -> A'` so that `[A <& x] : 1 -> A'`, we have `[x . F] = R`.

II.3.4. The **Run Operator**, given a DaTra function `[F : A -> B]`, is denoted using the postfix `.` symbol, and is
defined iff `A` is a total map, as `[F .] = [[] . F]`.

II.3.5. The **Specification Operator**, given a DaTra function `[F : A -> B]` and a DaTra map `X` so that `[A <& X]` is
defined, yields the DaTra function `[F : (A <& X) -> B]`. As such, it delays the execution of the function and simply
fills in values in the origin map. It is denoted by the space symbol, as `[F X]`. As such, if it is defined, we have
that `[F X .] = [X . F] = [[] . (F X)]`. In fact, `[F X .]` is considered the default notation for function
application. We do not seek to make the space operator eagerly apply a function, as to allow a function to be specified
in successive steps before application is forced, such as `[F X Y .]`.

II.3.6. The **Functional Assignment Operator**, given a DaTra function type and a fitting DaTra function, has a similar
action to the assignment operator, but is not defined if the left side is not a function, and has additional
functionality. It is denoted using the `::=` symbol, as `F ::= f`. On the right side of the operator, the simple
identifiers of the function type's origin map are introduced as immutable values, so that they can be utilized as part
of the function body. Additionally, the **Context Operator**, which is defined only on the right side of `::=`, is
denoted as `%`, and provides the fully specified origin map as an immutable value. For instance, a binary addition
function can be written as `[sum : [a : N, b : N] -> N ::= a + b]`.

II.3.7. A **DaTra Injective Function** has the property that, for all total maps with target as the origin map, the
function sends it to a different value. A **DaTra Surjective Function** has the property that, for all total maps with
target as the target map, there is a total map with target in the origin map that is sent to it. a **DaTra Isomorphic
Function** is a DaTra injective function that is a DaTra surjective function. Note that the existence of an isomorphic
function between DaTra maps does not make the DaTra maps isomorphic, since it is not an isomorphism in `DaTra`.

II.4.1. The **Collapse Operator**, given a Datra map of cardinality `C` with territory `Ter : A -> B`, yields a DaTra
map of cardinality `C` with territory `B`. As such, it obtains a DaTra collection from a DaTra map by forgetting the
arrow's origins. It is denoted by enclosing a DaTra map in `||` on both sides, such as `[|| X ||]`.

II.4.2. The **Interval Operator** is defined on DaTra natural numbers and has an infix and postfix version, so
that it accepts either one or two numbers. In both cases, it is denoted using the `..` symbol. In the infix version,
`[A .. B]` yields the DaTra map whose arrow at index `k` is `A + k`, and so that all arrows have a value smaller than
`B`. In the postfix version, `[A ..]` is similar, but imposes no restrictions on the largest value. One is also able
to combine different intervals by concatenation, such as `[2..9, 8..10]`. A DaTra map that is obtainable by the
concatenation of intervals is denoted a **DaTra Index Map**, and it is a DaTra collection. In particular, a coalition
of one natural number, such as `[3]`, is an index map.

II.4.3. The **Slice Operator** is defined on a DaTra map along with an index map, and yields a DaTra map whose
arrow at index `k` is the arrow of the DaTra map at the index provided by the arrow of the index map at `k`. It is
undefined if any of the values in the index map are out of bounds for the DaTra map's indices. It is denoted using the
`@` operator, as `[M @ i]`. As such, the slice operator provides the semantics for accessing a map at a collection of
indices, or in the simplest case, at one specific index. In combination with the context operator `%`, one can utilize
unlabelled values in a function body, such as `[sum : [N, N] -> N ::= (% @ 0) + (% @ 1)]`. In practice, the origin map
with unvalues could be transformed first into a version, before being utilized in the function body.

II.5.1. An **Ordered Index Map** is a DaTra index map that is a confederation, so that there exists a trivial
order embedding with origin as the cardinality of the map, and target as the map's arrow set.

II.5.2. A **Folio Strategy** is a DaTra function `[F : N -> N]` with the property that there exists an ordered index
map of cardinality `N` so that, by slicing and then collapsing the function, one obtains an index map with no values
equal to `0`. A **Sliced Folio Strategy** is the result of slicing a folio strategy with an ordered index map selecting
all arrows whose targets are not `0`.

II.5.3. A **Folio Pattern**, given a Folio Strategy, is a DaTra map with origin `[N]` and target as a subset of `[N]`,
which is encodable as a function `[F : N -> (N -> 2)]`, so that for all `n : N`, `F n` has the cardinality of the
value of the sliced folio strategy at `n`. Additionally, the folio pattern, seen as a pagination, must be navigable by
the trivial chart. There requirement mean that, given any Folio Strategy, it has a unique Folio Pattern.

II.5.4. A **DaTra Folio** is the result of slicing a folio pattern with an ordered indexed map. As such, given any
folio strategy, one can obtain a folio by slicing its unique folio pattern.

II.5.5. An **Indexing Strategy** is a DaTra injective function `[F : [N, N] -> N]`. For clarity, we may label the
arguments in the origin map as follows: `[F : [n : N; k : N] -> N]`. An **Indexing Tactic** is a DaTra injective
function `[F : [n : X; k : N] -> N]`, where `X` is a natural number, denoted the **Indexing Tactic's Cardinality**.

II.5.6. A **Folio Sum**, given a DaTra collection literal, a folio strategy and an indexing tactic of the same or
higher cardinality as the collection, is the DaTra map in the collection's coalition defined as follows: first,
create the map with origin as an ordered indexed map, so that each arrow sends the natural number to the total map with
target `[n : X; k : N]` the indexing tactic sends to that number. Compose this map with the function that sends total
maps with target `[n : X, k : N]` to the collection of cardinality `1` consisting of the imbuing of `\Arrow\` with the
`k`th arrow of the `n`th element. If such an arrow does not exist, the function sends the total map to the terminal
DaTra map, `[]`. Then, we collapse this function, obtaining what we denote the collection literal's **Collection of
Arrows**, where some arrows are missing. Obtain the folio strategy's folio pattern, and slice it on `0..K` where `K` is
the cardinality of the collection of arrows. Then, construct the remapping obtained by sending each element of the
folio pattern's arrow targets to the target of the collection of arrows sliced at that value, removing the element if
the arrow does not exist. Finally, slice the remapping with an ordered index map so that the arrows selected are the
ones not sent to the terminal object. The origin of the remapping is then the folio sum. As such, the horizontal sum
and concatenation operations are instances of folio sums.

II.5.7. The **Vertical Sum Operator** is defined for a non-terminal DaTra literal collection
of DaTra maps, let us denote its cardinality as `C`. Then, the **Vertical Folio Strategy** of cardinality `C`
sends each `x : N` to `C`. The **Vertical Indexing Tactic** of cardinality `C` sends `[n : C, k : N]` to `k * C + n`.
Thus, the vertical sum is the folio sum on the vertical folio strategy and the vertical indexing tactic. It is denoted
using the `|` symbol, either prefix as `| ||Col||`, or by writing the elements of the collection in order delineated
by `|`, such as `A | B | C`. For instance, `[[A ; B] | [C ; D] = [[A ; C]; [B ; D]]`.

II.5.8. A **Prime Folio Sum** is a Folio Sum whose indexing tactic is an indexing strategy. As such, it is able to
handle DaTra collections that are sequences, whose elements are themselves sequences. The naming is by analogy with the
infinite sequence of prime numbers, where each prime number yields an infinite sequence of prime powers, inducing an
isomorphism to the positive integers by prime factorization. In fact, this yields a valid indexing strategy, given
`[n : N, k : N]`, by writing `n` in base 2, selecting the primes at each index, and sending it to the `k`th number with
the given prime factors. As such, this can be denoted the **Canonical Prime Folio Sum**, which utilizes the **Trivial
Folio Strategy** sending `n : N` to `1`. The canonical prime folio sum is of largely theoretical interest due to its
computational complexity, and as such it does not have an operator. Given any two DaTra maps `A`, `B`, a prime folio
sum may be used in order to obtain a DaTra sequence in the coalition of `A * B`, containing all its inhabitants.

II.5.9. The **Diagonal Sum Operator** is defined on any DaTra collection. It is a prime folio sum defined on the
**Identity Folio Strategy**, which is defined as `id N`. Its indexing strategy, denoted the **Anti-Diagonal Indexing
Strategy**, sends `[n : N, k : N]` to the set in the folio pattern's image at `n - k`, so that each such set is
ordered by `n`. The specific formula for this indexing strategy can be implemented using the anti-diagonal traversal
algorithm. It is denoted by the `/\` symbol, either in infix notation as `/\ ||C||`, or by delineating the elements of
the collection, such as `A /\ B /\ C`. For instance, `[[A: B; C] /\ [D; E] /\ [F; G]] = [[A]; [B; D]; [C; E; F]; [G]]`.

## Future Work

> This document is merely an introductory exploration of the `DaTra` topos, and its mathematical aspects ought to be
> further explored. Furthermore, while we have provided an informal glance at a possible DaTra type theory, it is by
> no means complete or formal. In particular, the dependent products in DaTra have not been explored, although they
> exist by virtue of it being a topos. We believe DaTra provides the right semantics for **Dependent Identifiers**,
> wherein the value of the identifier varies based on value provided. DaTra maps with dependent identifiers can be
> shown to be confederations by constructing the identifiers to be constant in slices starting from 0, and making
> the slices differ. Alternatively, it can be shown in other slices provided the variability of the identifiers is
> itself structured in slices. We believe the algorithm for map filling confederations, provided that their elements
> are not coalitions whose maximal confederation is a sequence, has `O(n)` complexity, where `n` is the cardinality
> of the maximal confederation. It can be constructed by keeping track of the so-called **Symmetry Zones**, where
> argument order is variable. We believe DaTra is also the correct construction for the first-class handling of what
> in Python is denoted `*Args` and `**Kwargs`, by utilizing dependent products to define the types. We also believe
> it can act as a foundation for so-called **Intraidentifiers**, which are identifiers visible within a function's body
> but not during function call, by transforming the data before it is received. In general, we believe exploration of
> the `DaTra` topos can act as a source for innovative PL semantics, by regarding identifiers, arguments, partial maps
> and partially variable argument order as first class.
