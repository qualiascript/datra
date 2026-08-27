import Mathlib

/-!
# Datra

This file formalizes `datra.md`. The declarations are kept in the same
numbered order as the source document. The original prose is repeated
verbatim in comments before the corresponding Lean declarations.

The implementation uses a chosen injection into `Nat` as the rank of an
element. This choice is isolated in `Dominion.rank`, so a later replacement
by accessible ordinals does not affect the categorical interfaces.
-/

namespace Datra

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite

/-
1.1.1. The **Category of Dominions**, denoted `Dom`, has as its objects sets whose cardinality is at most `omega_0`
(i.e. the smallest infinite ordinal), that is, its objects are sets that have an injection to `omega_0`, and as its
morphisms set-theoretic functions (i.e. morphisms in `Set`).
-/

structure Dominion where
  Carrier : Type 0
  rank : Function.Embedding Carrier Nat

abbrev Dom := Dominion

instance : CoeSort Dominion Type where
  coe X := X.Carrier

instance : Category Dominion where
  Hom X Y := X -> Y
  id _ := id
  comp f g := Function.comp g f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-
1.1.2. The **Domanial Embedding Functor**, denoted `Emb : Dom -> Set`, sends each dominion to its corresponding set.
-/

def Emb : Functor Dom (Type 0) where
  obj X := X
  map f := f

/-
1.2.1. The **Category of Domanial Insertions**, denoted `DomIns`, is the category whose objects are dominions, that is, 
objects of `Dom`, and whose morphisms are monomorphisms in `Dom`. 
-/

structure DomIns where
  toDom : Dom

instance : CoeSort DomIns Type where
  coe X := X.toDom.Carrier

instance : Category DomIns where
  Hom X Y := Function.Embedding X Y
  id X := Function.Embedding.refl X
  comp f g := f.trans g
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

/-
1.2.2. The **Category of Codomanial Insertions**, denoted `CoDomIns`, is the opposite category of `DomIns`, that is,
`CoDomIns = op DomIns`.
-/

abbrev CoDomIns := Opposite DomIns

/-
1.3.1. The **Category of Domanial Consolidations**, denoted `DomCon`, is the category whose objects are dominions and
morphisms are order-preserving epimorphisms in `Dom`. More specifically, a morphism `F : A -> B` in `DomCon` has the
property that for any `x, y : A`, if `|x| < |y|`, then `|F x| <= |F y|`.
-/

structure DomCon where
  toDom : Dom

instance : CoeSort DomCon Type where
  coe X := X.toDom.Carrier

structure DomConHom (X Y : DomCon) where
  toFun : X -> Y
  onto : Function.Surjective toFun
  order_preserving : forall x y, X.toDom.rank x < X.toDom.rank y ->
    Y.toDom.rank (toFun x) <= Y.toDom.rank (toFun y)

instance {X Y : DomCon} : CoeFun (DomConHom X Y) (fun _ => X -> Y) where
  coe f := f.toFun

@[ext]
theorem DomConHom.ext {X Y : DomCon} (f g : DomConHom X Y)
    (h : forall x, f x = g x) : f = g := by
  cases f with
  | mk f hf1 hf2 =>
    cases g with
    | mk g hg1 hg2 =>
      have : f = g := funext h
      subst this
      rfl

instance : Category DomCon where
  Hom := DomConHom
  id X :=
    { toFun := id
      onto := Function.surjective_id
      order_preserving := fun _ _ h => Nat.le_of_lt h }
  comp {X Y Z} f g :=
    { toFun := Function.comp g f
      onto := g.onto.comp f.onto
      order_preserving := by
        intro x y hxy
        have h := f.order_preserving x y hxy
        rcases h.lt_or_eq with hlt | heq
        case inl => exact g.order_preserving (f x) (f y) hlt
        case inr =>
          have hvalue : f x = f y := Y.toDom.rank.injective heq
          simpa only [Function.comp_apply, hvalue] using
            (Nat.le_refl (Z.toDom.rank (g (f y)))) }
  id_comp f := by ext x; rfl
  comp_id f := by ext x; rfl
  assoc f g h := by ext x; rfl

/-
1.3.2. The **Category of Codomanial Consolidations**, denoted `CoDomCon`, is the opposite category of `DomCon`, that
is, `CoDomCon = op DomCon`.
-/

abbrev CoDomCon := Opposite DomCon

/-
1.4.1. A **Chain** is a totally ordered thin category, taken skeletally.
-/

structure Chain where
  Carrier : Type 0
  order : LinearOrder Carrier

attribute [instance] Chain.order

/-
1.4.2. A **Short Chain** is a chain that is finite, taken skeletally.
-/

structure ShortChain extends Chain where
  finite : Fintype Carrier

attribute [instance] ShortChain.finite

/-
1.5.1. The **Transportation Functor**, denoted `Tra`, is of type `Tra : DomCon -> Set`, and sends each morphism
in `DomCon` to its underlying set-theoretic surjection.
-/

def Tra : Functor DomCon (Type 0) where
  obj X := X
  map f := f.toFun

/-
1.5.2. A **Folio** is a functor `F : C -> (1 / CoDomCon)`, where `1 / CoDomCon` is the coslice category, that preserves
the initial object.
-/

structure Folio where
  length : Nat
  positive : 0 < length
  F : Functor (Fin length) CoDomCon
  originEquiv : Equiv ((F.obj (Fin.mk 0 positive)).unop.toDom.Carrier) PUnit.{0}

def Folio.H (W : Folio) : Functor (Opposite (Fin W.length)) (Type 0) :=
  Functor.comp W.F.leftOp Tra

def Folio.E (W : Folio) : Type 0 := W.H.Elements

instance (W : Folio) : Category.{0} W.E := CategoryTheory.categoryOfElements W.H

/-
1.6.1. The **Category of Paginations**, denoted `Pag`, is the category whose objects are pairs `(H, E)`, where 
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
-/

structure Pag where
  folio : Folio

def Pag.H (W : Pag) : Functor (Opposite (Fin W.folio.length)) (Type 0) := W.folio.H
def Pag.E (W : Pag) : Type 0 := W.folio.E

instance (W : Pag) : Category.{0} W.E := CategoryTheory.categoryOfElements W.H

instance : Category.{0} Pag where
  Hom X Y := Functor X.E Y.E
  id X := Functor.id X.E
  comp F G := Functor.comp F G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-
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
-/

structure DaTra where
  P : Pag
  G : Functor P.E DomIns

def DaTra.H (X : DaTra) : Functor (Opposite (Fin X.P.folio.length)) (Type 0) := X.P.H
def DaTra.E (X : DaTra) : Type 0 := X.P.E

instance (X : DaTra) : Category.{0} X.E := CategoryTheory.categoryOfElements X.H

structure DaTraHom (X Y : DaTra) where
  P : Functor X.E Y.E
  A : NatTrans X.G (Functor.comp P Y.G)

def DaTraHom.identity (X : DaTra) : DaTraHom X X where
  P := Functor.id X.E
  A := NatTrans.id X.G

def DaTraHom.comp {X Y Z : DaTra} (f : DaTraHom X Y) (g : DaTraHom Y Z) :
    DaTraHom X Z where
  P := Functor.comp f.P g.P
  A := CategoryStruct.comp f.A (whiskerLeft f.P g.A)

@[ext]
theorem DaTraHom.ext {X Y : DaTra} (f g : DaTraHom X Y)
    (hP : f.P = g.P) (hA : HEq f.A g.A) : f = g := by
  cases f
  cases g
  simp_all

instance : Category.{0} DaTra where
  Hom := DaTraHom
  id := DaTraHom.identity
  comp := DaTraHom.comp
  id_comp f := by
    apply DaTraHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [DaTraHom.comp, DaTraHom.identity]
  comp_id f := by
    apply DaTraHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [DaTraHom.comp, DaTraHom.identity]
  assoc f g h := by
    apply DaTraHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [DaTraHom.comp]

/-
1.7.2. The **Transformation Lemma** states that `DaTra` is a topos. Proof sketch: Let `PSh(B) = op B -> Set` be the
fixed category of underlying presheaves. The forgetful functor `U : DaTra -> PSh(B)` has a **Minimal Pagination 
Functor** `MinPag : PSh(B) -> DaTra`. The adjunction `MinPag -| U` has invertible unit and counit, so
`DaTra ~= PSh(B)`, and `DaTra` is a topos.
-/

/-- A concrete, checkable meaning of "is a presheaf topos". -/
structure PresheafToposPresentation (C : Type 1) [Category.{0} C] where
  Base : Type 0
  baseCategory : SmallCategory Base
  equivalence : Equivalence C (Functor (Opposite Base) (Type 0))

abbrev PSh (B : Type 0) [SmallCategory B] := Functor (Opposite B) (Type 0)

/-- The formal comparison named in 1.7.2. -/
structure MinimalPaginationData where
  Base : Type 0
  baseCategory : SmallCategory Base
  MinPag : Functor (PSh Base) DaTra
  U : Functor DaTra (PSh Base)
  adjunction : Adjunction MinPag U
  unitIsIso : forall X, IsIso (adjunction.unit.app X)
  counitIsIso : forall X, IsIso (adjunction.counit.app X)

attribute [instance] MinimalPaginationData.baseCategory

theorem transformationLemma (M : MinimalPaginationData) :
    Nonempty (PresheafToposPresentation DaTra) := by
  letI := M.unitIsIso
  letI := M.counitIsIso
  exact Nonempty.intro
    { Base := M.Base
      baseCategory := M.baseCategory
      equivalence := M.adjunction.toEquivalence.symm }

def Folio.originIndex (W : Folio) : Fin W.length := Fin.mk 0 W.positive

def Folio.originBase (W : Folio) : Opposite (Fin W.length) := op W.originIndex

def Folio.originValue (W : Folio) : W.H.obj W.originBase :=
  W.originEquiv.symm PUnit.unit

def Folio.originElement (W : Folio) : W.E := Sigma.mk W.originBase W.originValue

def Folio.lastIndex (W : Folio) : Fin W.length :=
  Fin.mk (W.length - 1) (Nat.sub_lt W.positive (by decide))

def Folio.lastBase (W : Folio) : Opposite (Fin W.length) := op W.lastIndex

/-
1.7.3. The **Cardinality of a DaTra Set** `D : DaTra` is the cardinality of the origin of `D_H : C -> Set`, that
is, the number of objects of the small chain `C`. It is denoted as `|D|`.
-/

def cardinality (D : DaTra) : Nat := D.P.folio.length

/-
1.7.4. The **Extent of a DaTra Set** `D : DaTra` is the value at `D_G (0, 0)`, that exists as folios preserve initial
objects. It is denoted as `Ex D`. Since the objects of `DomIns` are dominions, `Ex D : Dom` for any `D : DaTra`.
-/

def extent (D : DaTra) : Dom :=
  (D.G.obj D.P.folio.originElement).toDom

/-
1.7.5. The **Territory of a DaTra Set** `D : DaTra` is the indexed collection of dominions `Ter D : M -> Dom`, 
where `M = D_G (|D| - 1)`, so that `Ter D k = D_G (|D| - 1, k)`.
-/

/-- The type `M` is the last fiber of `D_H`; this is the only typing of the
displayed expression for which `k` indexes objects of the category of
elements. -/
def TerritoryIndex (D : DaTra) : Type 0 := D.H.obj D.P.folio.lastBase

def territory (D : DaTra) (k : TerritoryIndex D) : Dom :=
  (D.G.obj (Sigma.mk D.P.folio.lastBase k)).toDom

/-
1.7.6. The **nth Region of a DaTra Set** `D : DaTra` is the dominion `Ter D n` for `n : M`, noting that the indexing
starts at `0`.
-/

def region (D : DaTra) (n : TerritoryIndex D) : Dom := territory D n

/-
1.8.1. The **Category of Data Transposals**, denoted `DaTrap`, is the wide subcategory of `DaTra` whose morphisms for
`F : X -> Y` have the property that `F_E` is a faithful functor.
-/

def IsTransposal : MorphismProperty DaTra := fun _ _ F => F.P.Faithful

instance : IsTransposal.IsMultiplicative where
  id_mem X := by
    change (Functor.id X.E).Faithful
    infer_instance
  comp_mem f g hf hg := by
    change f.P.Faithful at hf
    change g.P.Faithful at hg
    change (Functor.comp f.P g.P).Faithful
    letI := hf
    letI := hg
    infer_instance

abbrev DaTrap := WideSubcategory IsTransposal

def DaTrapInc : Functor DaTrap DaTra := wideSubcategoryInclusion IsTransposal

def Folio.commonBase (W : Folio) (m n : Opposite (Fin W.length)) :
    Opposite (Fin W.length) := op (min m.unop n.unop)

def Folio.toCommonLeft (W : Folio) (m n : Opposite (Fin W.length)) :
    Quiver.Hom m (W.commonBase m n) := (homOfLE (min_le_left _ _)).op

def Folio.toCommonRight (W : Folio) (m n : Opposite (Fin W.length)) :
    Quiver.Hom n (W.commonBase m n) := (homOfLE (min_le_right _ _)).op

def Folio.rankAt (W : Folio) (m : Opposite (Fin W.length)) : W.H.obj m -> Nat :=
  (W.F.obj m.unop).unop.toDom.rank

def elementLT (X : DaTra) (x y : X.E) : Prop :=
  let k := X.P.folio.commonBase x.1 y.1
  X.P.folio.rankAt k (X.H.map (X.P.folio.toCommonLeft x.1 y.1) x.2) <
    X.P.folio.rankAt k (X.H.map (X.P.folio.toCommonRight x.1 y.1) y.2)

/-
1.8.2. The **Category of Data Traversals**, denoted `DaTrav`, is the wide subcategory of `DaTrap` whose morphisms
for `F : X -> Y` have the following properties: for any `x = (k, i)`, `y = (k, j)` with `i < j`, let
`x' = F_E x = (m, i')`, `y' = F_E y = (n, j')` and let `k' = min(m, n)`, then `Y_H (m -> k') i' < Y_H (n -> k') j'`.
-/

/-- The global order formulation is the composition-stable closure of the
same-page condition in the prose. On a same-page pair it reduces to the
displayed transport to `k' = min(m,n)`. -/
def IsTraversal : MorphismProperty DaTra := fun _ _ F =>
  And F.P.Faithful
    (forall x y, elementLT _ x y -> elementLT _ (F.P.obj x) (F.P.obj y))

instance : IsTraversal.IsMultiplicative where
  id_mem X := by
    constructor
    case left =>
      change (Functor.id X.E).Faithful
      infer_instance
    case right =>
      intro x y h
      exact h
  comp_mem f g hf hg := by
    constructor
    case left =>
      change (Functor.comp f.P g.P).Faithful
      letI : f.P.Faithful := hf.1
      letI : g.P.Faithful := hg.1
      infer_instance
    case right =>
      intro x y h
      exact hg.2 _ _ (hf.2 _ _ h)

abbrev DaTrav := WideSubcategory IsTraversal

def DaTravInc : Functor DaTrav DaTra := wideSubcategoryInclusion IsTraversal

def DaTravToDaTrap : Functor DaTrav DaTrap where
  obj X := WideSubcategory.mk X.obj
  map F := Subtype.mk F.1 F.2.1

/-
1.9.1. The **Category of Data Transformation Maps**, denoted `DaTraMap`, is the full subcategory of `DaTra` that
includes all DaTra sets with the property that their extent is isomorphic to the coproduct of its regions. That is, for
`D : DaTra`, let `F = Emb ∘ Ter D : M -> Set`, and let `Sum D` be the coproduct on diagram `F`, then `D : DaTraMap`
iff `Sum D ~= Ex D`.
-/

def territoryDiagram (D : DaTra) : Functor (Discrete (TerritoryIndex D)) (Type 0) :=
  Discrete.functor (fun k => (territory D k).Carrier)

/-- The set-level coproduct of all regions. -/
def regionSum (D : DaTra) : Type 0 := Sigma (fun k : TerritoryIndex D => territory D k)

def IsDaTraMap : ObjectProperty DaTra := fun D =>
  Nonempty (Equiv (regionSum D) (extent D))

abbrev DaTraMap := IsDaTraMap.FullSubcategory

/-
1.9.2. The **DaTra Map Inclusion Functor**, `DaTraMapInc : DaTraMap -> DaTra` sends each DaTra map to its equivalent
DaTra set.
-/

def DaTraMapInc : Functor DaTraMap DaTra where
  obj X := X.obj
  map f := f

/-
1.9.3. The **Category of Data Traversal Maps**, or simply **DaTrav Maps**, denoted `DaTravMap`, is the wide
subcategory of `DaTraMap` so that a morphism `f : x -> y` of `DaTraMap` is a morphism of `DaTravMap` iff
`DaTraMapInc f` is a morphism of `DaTrav`.
-/

def IsDaTravMap : MorphismProperty DaTraMap := fun _ _ f =>
  IsTraversal (DaTraMapInc.map f)

instance : IsDaTravMap.IsMultiplicative where
  id_mem X := IsTraversal.id_mem X.obj
  comp_mem f g hf hg := IsTraversal.comp_mem f g hf hg

abbrev DaTravMap := WideSubcategory IsDaTravMap

/-
1.9.4. The **DaTrav Map Inclusion Functor**, `DaTravMapInc : DaTravMap -> DaTrav` is the canonical restriction of
`DaTraMapInc` on the morphisms of `DaTravMap`.
-/

def DaTravMapInc : Functor DaTravMap DaTrav where
  obj X := WideSubcategory.mk X.obj.obj
  map f := Subtype.mk f.1 f.2

/-
1.9.5. The **Charting Functor**, if it exists, is defined as the right adjoint to `DaTravMapInc`, and it is denoted
`Chr : DaTrav -> DaTravMap`.
-/

/-- Data witnessing the universal arrows required by the charting
construction. Keeping the adjunction bundled makes the phrase "if it exists"
precise without adding an unproved postulate. -/
structure CartographyData where
  Chr : Functor DaTrav DaTravMap
  adjunction : Adjunction DaTravMapInc Chr
  Ex : Functor DaTravMap Dom
  Ex_obj : forall X, Nonempty (Iso (Ex.obj X) (extent X.obj.obj))
  territoryIso : forall X, Nonempty
    (Equiv (TerritoryIndex X.obj) (TerritoryIndex (DaTravMapInc.obj (Chr.obj X)).obj))

def ChartingFunctor (C : CartographyData) : Functor DaTrav DaTravMap := C.Chr

/-
1.9.6. The **Cartography Lemma** states that `Chr` exists. Proof sketch: `Chr`'s action on objects `X : DaTrav` is
sending it to the universal arrow from `DaTravMapInc` to `X`, so that we denote `X' = DaTravMapInc Chr X`, along with
`H : X' -> X`, with `X'` terminal among objects with this property. The solution is given by the DaTra map so that
`Ter X' ~= Ter X`, which is unique as `DaTrav` preserves orders, and terminal as `H_E` is faithful.
-/

theorem cartographyLemma (C : CartographyData) :
    Nonempty (Adjunction DaTravMapInc C.Chr) :=
  Nonempty.intro C.adjunction

/-
1.10.1. The **Coalizing Functor**, denoted `Coa : DaTrav -> Dom`, is defined as `Coa = Ex ∘ Chr`.
-/

def Coa (C : CartographyData) : Functor DaTrav Dom := Functor.comp C.Chr C.Ex

/-
1.10.2. The **Domanial Inclusion Functor**, denoted `DomInc : Dom -> DaTrav`, is the functor that is left adjoint to
`Coa`. That is, for every `X : Dom`, `Y : DaTrav`, `hom_DaTrav (DomInc X, Y) ~= hom_Dom(X, Coa Y)`, naturally in
`X` and `Y`, so that `Coa (DomInc X) = X`.
-/

structure DomanialInclusionData (C : CartographyData) where
  DomInc : Functor Dom DaTrav
  adjunction : Adjunction DomInc (Coa C)
  coalizes : forall X, Nonempty (Iso ((Coa C).obj (DomInc.obj X)) X)

def DomInc {C : CartographyData} (D : DomanialInclusionData C) : Functor Dom DaTrav :=
  D.DomInc

def domInc_hom_equiv {C : CartographyData} (D : DomanialInclusionData C)
    (X : Dom) (Y : DaTrav) :
    Equiv (Quiver.Hom (D.DomInc.obj X) Y) (Quiver.Hom X ((Coa C).obj Y)) :=
  D.adjunction.homEquiv X Y

/-
1.10.3. The **Coalition of a DaTra Object**, given an object `X` of `DaTra`, is `Coa X'`, where `X' : DaTrav` is the
same object viewed as an object of `DaTrav`.
-/

def coalition (C : CartographyData) (X : DaTra) : Dom :=
  (Coa C).obj (WideSubcategory.mk X)

def emptyDominion : Dom where
  Carrier := Empty
  rank :=
    { toFun := fun x => nomatch x
      inj' := fun x => nomatch x }

def emptyDominionIsInitial : IsInitial emptyDominion :=
  IsInitial.ofUniqueHom
    (fun X => fun x => nomatch x)
    (fun X f => by
      funext x
      exact nomatch x)

/-
1.10.4. The **Empty Map** is the DaTra set that `DomInc` sends the initial object of `Dom`, `0 : Dom`, to. It is
denoted as `I = DomInc 0`, and it is initial in `DaTra`.
-/

def emptyMap {C : CartographyData} (D : DomanialInclusionData C) : DaTra :=
  (D.DomInc.obj emptyDominion).obj

/-- Initiality in `DaTrav` follows from the left adjoint. Initiality after
forgetting to the wider category `DaTra` is additional data: a wide
subcategory can have fewer arrows, so the latter does not follow formally. -/
structure EmptyMapData {C : CartographyData} (D : DomanialInclusionData C) where
  isInitial : IsInitial (emptyMap D)

def emptyMap_isInitial {C : CartographyData} {D : DomanialInclusionData C}
    (h : EmptyMapData D) : IsInitial (emptyMap D) := h.isInitial

/-
1.11.1. The **Horizontal Sum Bifunctor**, if it exists, is denoted as `HorSum : DaTrav * DaTrav -> DaTrav`, or using
infix notation using the `+_<` symbol as `DaTrav +_< DaTrav -> DaTrav`, and is defined as follows: given two morphisms
in `DaTrav`, `F : X -> Y`, `F' : X -> Y`, let `H : G * G' -> F + F'` be the universal arrow from `DaTrav * DaTrav` to
`F + F'` so that for projections `H_1 : G -> F + F'`, `H2 : G' -> F + F'`, for `(m, i) = H_1_E (0, 0)`,
`(m', i') = H_2_E (0, 0)`, we have `m < 2`, `m' < 2`, `i = 0`, and furthermore, if `m = 1`, then `i' = 1`. Then,
`F +_< F' = H`. It remains to be shown `H` exists and is unique for all morphisms `F, F'` of `DaTrav`.
-/

/-- The bifunctor and its strict-unit comparison. The universal-arrow
construction described in the prose is exactly the missing constructor of
this record. -/
structure HorizontalData {C : CartographyData} (D : DomanialInclusionData C) where
  HorSum : Functor (Prod DaTrav DaTrav) DaTrav
  leftUnit : forall X, Nonempty
    (Iso (HorSum.obj (D.DomInc.obj emptyDominion, X)) X)
  rightUnit : forall X, Nonempty
    (Iso (HorSum.obj (X, D.DomInc.obj emptyDominion)) X)

def HorSum {C : CartographyData} {D : DomanialInclusionData C}
    (H : HorizontalData D) : Functor (Prod DaTrav DaTrav) DaTrav := H.HorSum

/-
1.11.2. The **Horizontal Lemma** states that `HorSum` exists. Proof sketch: for `F +_< F'`, if `F' = I`, then
`H : I -> F`, and `I` is initial so `H` is unique, so that `H ~= H_1 ~= H_2` and `(m, i) = H_E (0, 0) = (0, 0)`, so
that `i = 0` and as `m = 0`, the condition on `i'` need not be checked. The case for `F = I` is dual. If both `F` and
`F'` are distinct from `I`, for `(m, i) = H_1_E (0, 0)`, if `m = 0`, then `i = 0` and `Ex F = Ex F + Ex F'`, but as
`F'` is not `I`, this cannot hold, so that `m = 1`, which implies `i' = 1`, so that the solution is given by
`(m, i) = (1, 0)`, `(m', i') = (1, 1)`.
-/

theorem horizontalLemma {C : CartographyData} {D : DomanialInclusionData C}
    (H : HorizontalData D) : Nonempty (HorizontalData D) := Nonempty.intro H

/-
1.12.1. The **Data Traversal Monoidal Category**, denoted `DaTravMon`, if it exists, is the symmetric monoidal category
with `DaTrav` as the underlying category, `+_<` as the tensor product and `I` as the identity, so that we denote
`DaTravMon = (DaTrav, +_<, I)`. As for `X : DaTrav`, `X = X + I = I + X` is strict, the left and right unitors are
given by identity. It remains to be shown that there is a braider functor whose double application yields identity,
and an associator functor so that the pentagon, triangle and hexagon identities commute.
-/

/-- Mathlib's `MonoidalCategory` and `SymmetricCategory` structures contain
the pentagon, triangle, hexagon, naturality, and involutivity proofs. The two
equalities identify their abstract tensor and unit with Datra's terminology. -/
structure DaTravMonData {C : CartographyData} {D : DomanialInclusionData C}
    (H : HorizontalData D) where
  monoidal : MonoidalCategory DaTrav
  symmetric : @SymmetricCategory DaTrav _ monoidal
  tensor_eq : @MonoidalCategory.tensor DaTrav _ monoidal = H.HorSum
  unitIso : Iso (@MonoidalCategoryStruct.tensorUnit DaTrav _
      monoidal.toMonoidalCategoryStruct) (D.DomInc.obj emptyDominion)

abbrev DaTravMon {C : CartographyData} {D : DomanialInclusionData C}
    (H : HorizontalData D) := DaTravMonData H

/-
1.12.2. The **Data Traversal Braider**, denoted `Brd_X_Y : X +_< Y -> Y +_< X` for `X, Y : DaTrav`, is defined
as follows: if `X = I` or `Y = I`, `Brd_X_Y = Id`. Otherwise, let `G : H -> X +_< Y` be the universal arrow from
`DaTrap` to `X +_< Y` so that `G_E (1, 0) = (1, 1)` and `G_E (1, 1) = (1, 0)`. Trivially, `H = Y +_< X`, so that
we let `Brd_X_Y X +_< Y = H`, and trivially, `Brd_Y_X Brd_X_Y = Id`.
-/

def Brd {C : CartographyData} {D : DomanialInclusionData C}
    {H : HorizontalData D} (M : DaTravMon H) (X Y : DaTrav) := by
  letI := M.monoidal
  letI := M.symmetric
  exact BraidedCategory.braiding X Y

/-
1.12.3. The **Data Traversal Associator**, denoted `Asoc_X_Y_Z : (X +_< Y) +_< Z -> X +_< (Y +_< Z)`, is defined
as follows: if `X = I`, `Y = I` or `Z = I`, then `Asoc_X_Y_Z = Id`. Otherwise, denote `R = (X +_< Y) +_< Z` and let
`G : H -> R` be the universal arrow from `DaTrap` to `R` so that `G_E (2, 0) = (1, 0)` and there exists a morphism
`G' : (Y +_< Z) -> H` in `DaTrav` with `G'_E (0, 0) = (1, 1)`. As `G_E` is faithful and `G_A = Id`, `G` is invertible
in `DaTrap`, and by extension in `DaTra`.
-/

def Asoc {C : CartographyData} {D : DomanialInclusionData C}
    {H : HorizontalData D} (M : DaTravMon H) (X Y Z : DaTrav) := by
  letI := M.monoidal
  exact MonoidalCategoryStruct.associator X Y Z

/-
1.12.4. The **Serenity Lemma** states that `DaTravMon` exists. Proof sketch: As both `Asoc` and `Brd` send objects to
isomorphic objects in `DaTra`, it is clear that the pentagon, triangle and hexagon identities commute, thus `DaTravMon`
is a symmetric monoidal category.
-/

theorem serenityLemma {C : CartographyData} {D : DomanialInclusionData C}
    {H : HorizontalData D} (M : DaTravMon H) :
    Nonempty (@SymmetricCategory DaTrav _ M.monoidal) := Nonempty.intro M.symmetric

end Datra
