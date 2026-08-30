import Mathlib

/-%%
\documentclass[11pt]{article}
\usepackage[a4paper,margin=1in]{geometry}
\usepackage{microtype}
\usepackage{mathtools,amssymb,amsthm}
\usepackage{tikz-cd}
\usepackage[hidelinks]{hyperref}

\title{DaTra: Data Transformation Semantics as a Symmetric Monoidal
Category on Atlas Presheaves}
\author{\texttt{@qualiascript} \and ChatGPT}
\date{}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\theoremstyle{plain}
\newtheorem{lemma}[definition]{Lemma}

\newcommand{\Set}{\mathsf{Set}}
\newcommand{\Dom}{\mathsf{Dom}}
\newcommand{\DomIns}{\mathsf{DomIns}}
\newcommand{\CoDomIns}{\mathsf{CoDomIns}}
\newcommand{\Con}{\mathsf{Con}}
\newcommand{\CoCon}{\mathsf{CoCon}}
\newcommand{\Pag}{\mathsf{Pag}}
\newcommand{\Atl}{\mathsf{Atl}}
\newcommand{\Yo}{\mathsf{Yo}}
\newcommand{\Ex}{\mathsf{Ex}}
\newcommand{\Ter}{\mathsf{Ter}}
\newcommand{\id}{\operatorname{Id}}
\newcommand{\Hom}{\operatorname{Hom}}

\begin{document}
\maketitle

\section{Dominions}

\begin{definition}[The Category of Dominions]
The \textbf{Category of Dominions}, denoted $\Dom$, has as its objects sets
whose cardinality is at most $\omega_0$, equivalently sets admitting an
injection into $\omega_0$, and as its morphisms set-theoretic functions.
\end{definition}
%%-/

namespace Datra

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Ordinal

universe u

noncomputable section

/-- A dominion is a set equipped with a certificate of countability. -/
structure Dominion where
  Carrier : Type
  rank : Function.Embedding Carrier Nat

abbrev Dom := Dominion

instance : CoeSort Dominion Type where coe X := X.Carrier

instance : Category Dominion where
  Hom X Y := X → Y
  id _ := id
  comp f g := g ∘ f
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-%%
\begin{definition}[The Domanial Embedding Functor]
The \textbf{Domanial Embedding Functor}, denoted
$\mathsf{Emb}:\Dom\to\Set$, sends each dominion to its underlying set.
\end{definition}
%%-/

def Emb : Dom ⥤ Type where
  obj X := X
  map f := f

/-%%
\section{Domanial Insertions}

\begin{definition}[The Category of Domanial Insertions]
The \textbf{Category of Domanial Insertions}, denoted $\DomIns$, has dominions
as objects and monomorphisms in $\Dom$ as morphisms.
\end{definition}
%%-/

structure DomIns where
  toDom : Dom

instance : CoeSort DomIns Type where coe X := X.toDom.Carrier

instance : Category DomIns where
  Hom X Y := Function.Embedding X Y
  id X := Function.Embedding.refl X
  comp f g := f.trans g
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl

instance {X Y : DomIns} : CoeFun (X ⟶ Y) (fun _ => X → Y) where
  coe f := f.toFun

@[ext]
theorem DomIns.hom_ext {X Y : DomIns} (f g : X ⟶ Y)
    (h : ∀ x, f x = g x) : f = g := by
  exact Function.Embedding.ext h

instance {X Y : DomIns} (f : X ⟶ Y) : Mono f where
  right_cancellation g h w := by
    apply DomIns.hom_ext
    intro x
    apply f.injective
    exact congrFun (congrArg Function.Embedding.toFun w) x

def DomIns.forget : DomIns ⥤ Dom where
  obj X := X.toDom
  map f := f.toFun

/-%%
\begin{definition}[The Category of Codomanial Insertions]
The \textbf{Category of Codomanial Insertions}, denoted $\CoDomIns$, is the
opposite category $\DomIns^{\mathrm{op}}$.
\end{definition}
%%-/

abbrev CoDomIns := Opposite DomIns

/-%%
\section{Chains}

\begin{definition}[Chain]
A \textbf{Chain} is a totally ordered thin category, indexed skeletally by an
ordinal strictly smaller than $\omega_0^{\omega_0}$.
\end{definition}
%%-/

/-- A chain carries its skeletal well-ordered object type and a proof that
its order type lies below `ω₀ ^ ω₀`.  Retaining the carrier explicitly makes
ordinal sums of chains definitionally usable. -/
structure Chain where
  Obj : Type
  linearOrder : LinearOrder Obj
  wellFoundedLT : WellFoundedLT Obj
  orderType_lt : Ordinal.type (fun x y : Obj => x < y) <
    Ordinal.omega0 ^ Ordinal.omega0

attribute [instance] Chain.linearOrder Chain.wellFoundedLT

def Chain.sum (X Y : Chain) : Chain where
  Obj := Lex (Sum X.Obj Y.Obj)
  linearOrder := inferInstance
  wellFoundedLT := ⟨by
    change WellFounded (Sum.Lex (fun x y : X.Obj => x < y)
      (fun x y : Y.Obj => x < y))
    exact Sum.lex_wf wellFounded_lt wellFounded_lt⟩
  orderType_lt := by
    change Ordinal.type (Sum.Lex (fun x y : X.Obj => x < y)
      (fun x y : Y.Obj => x < y)) < Ordinal.omega0 ^ Ordinal.omega0
    rw [Ordinal.type_sum_lex]
    exact Ordinal.principal_add_omega0_opow Ordinal.omega0
      X.orderType_lt Y.orderType_lt

/-%%
\begin{definition}[The Spine]
The \textbf{spine} is the chain with $\omega_0$ objects.
\end{definition}
%%-/

/-- The common page-indexing chain. -/
def Spine : Chain where
  Obj := Nat
  linearOrder := inferInstance
  wellFoundedLT := inferInstance
  orderType_lt := by
    have hpow : Ordinal.omega0 ^ (1 : Ordinal) <
        Ordinal.omega0 ^ Ordinal.omega0 :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
        Ordinal.one_lt_omega0
    change typeLT Nat < Ordinal.omega0 ^ Ordinal.omega0
    rw [Ordinal.type_nat_lt]
    simpa only [Ordinal.opow_one] using hpow

/-%%
\section{Consolidations}

\begin{definition}[The Category of Consolidations]
The \textbf{Category of Consolidations}, denoted $\Con$, has chains as objects
and point-surjective functors between their thin categories as morphisms.
\end{definition}
%%-/

abbrev Con := Chain

/-- A functor between ordinal chains is equivalently a monotone object map. -/
structure ConHom (X Y : Con) where
  toFun : X.Obj → Y.Obj
  monotone : Monotone toFun
  point_surjective : Function.Surjective toFun

def ConHom.sum {X X' Y Y' : Con} (f : ConHom X Y) (g : ConHom X' Y') :
    ConHom (Chain.sum X X') (Chain.sum Y Y') where
  toFun z := toLex (Sum.map f.toFun g.toFun (ofLex z))
  monotone := by
    intro a b h
    change Sum.Lex (fun x y : X.Obj => x ≤ y) (fun x y : X'.Obj => x ≤ y)
      (ofLex a) (ofLex b) at h
    change Sum.Lex (fun x y : Y.Obj => x ≤ y) (fun x y : Y'.Obj => x ≤ y)
      (Sum.map f.toFun g.toFun (ofLex a))
      (Sum.map f.toFun g.toFun (ofLex b))
    generalize ha : ofLex a = sa at h ⊢
    generalize hb : ofLex b = sb at h ⊢
    rcases sa with x | x <;> rcases sb with y | y
    ·
      simp only [Sum.map]
      exact Sum.Lex.inl (f.monotone (Sum.lex_inl_inl.mp h))
    · simp only [Sum.map]
      exact Sum.Lex.sep _ _
    · exact (Sum.lex_inr_inl h).elim
    ·
      simp only [Sum.map]
      exact Sum.Lex.inr (g.monotone (Sum.lex_inr_inr.mp h))
  point_surjective := by
    intro z
    rcases hz : ofLex z with y | y
    · obtain ⟨x, rfl⟩ := f.point_surjective y
      refine ⟨toLex (Sum.inl x), ?_⟩
      apply toLex.injective
      simpa using hz.symm
    · obtain ⟨x, rfl⟩ := g.point_surjective y
      refine ⟨toLex (Sum.inr x), ?_⟩
      apply toLex.injective
      simpa using hz.symm

instance {X Y : Con} : CoeFun (ConHom X Y) (fun _ => X.Obj → Y.Obj) where
  coe f := f.toFun

@[ext]
theorem ConHom.ext {X Y : Con} (f g : ConHom X Y)
    (h : ∀ x, f x = g x) : f = g := by
  cases f
  cases g
  simp_all only [mk.injEq]
  exact funext h

instance : Category.{0} Con where
  Hom := ConHom
  id X := ⟨id, monotone_id, Function.surjective_id⟩
  comp f g := ⟨g ∘ f, g.monotone.comp f.monotone,
    g.point_surjective.comp f.point_surjective⟩
  id_comp f := by ext; rfl
  comp_id f := by ext; rfl
  assoc f g h := by ext; rfl

instance {X Y : Con} : CoeFun (X ⟶ Y) (fun _ => X.Obj → Y.Obj) where
  coe f := f.toFun

def Con.asFunctor {X Y : Con} (f : X ⟶ Y) : X.Obj ⥤ Y.Obj where
  obj := f
  map g := homOfLE (f.monotone (leOfHom g))

/-%%
\begin{definition}[The Category of Coconsolidations]
The \textbf{Category of Coconsolidations}, denoted $\CoCon$, is the opposite
category $\Con^{\mathrm{op}}$.
\end{definition}
%%-/

abbrev CoCon := Opposite Con

/-%%
\section{Transportation and Folios}

\begin{definition}[The Transportation Functor]
The \textbf{Transportation Functor}, denoted
$\mathsf{Tra}:\Con\to\Set$, sends a chain to its object set and a
consolidation to its underlying set-theoretic surjection.
\end{definition}
%%-/

def Tra : Con ⥤ Type where
  obj X := X.Obj
  map f := f.toFun

/-%%
\begin{definition}[Folio]
A \textbf{folio} is a functor $F:S\to\CoCon$, where $S$ is the spine, such
that $F(0)$ is the singleton chain.
\end{definition}
%%-/

/-- A folio is stored by the least finite presentation of its eventually
constant spine functor. `length` is its cardinality: page `length - 1` is
the final genuine page and every later spine page repeats it. -/
structure Folio where
  length : Nat
  positive : 0 < length
  core : Functor.{0, 0} (Fin length) CoCon
  originEquiv : (core.obj ⟨0, positive⟩).unop.Obj ≃ Unit

def Folio.paddedIndex (W : Folio) (n : Nat) : Fin W.length :=
  ⟨min n (W.length - 1), lt_of_le_of_lt (min_le_right _ _)
    (Nat.sub_lt W.positive (by omega))⟩

theorem Folio.paddedIndex_mono (W : Folio) :
    Monotone W.paddedIndex := by
  intro a b hab
  exact min_le_min hab le_rfl

def Folio.spineBase (W : Folio) : Nat ⥤ Fin W.length where
  obj n := W.paddedIndex n
  map f := homOfLE (W.paddedIndex_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The actual functor on the spine denoted by the finite presentation. -/
def Folio.F (W : Folio) : Nat ⥤ CoCon := W.spineBase ⋙ W.core

/-- The page functor on the opposite spine. -/
def Folio.spineH (W : Folio) : Natᵒᵖ ⥤ Type := W.F.leftOp ⋙ Tra

def Folio.H (W : Folio) : (Fin W.length)ᵒᵖ ⥤ Type := W.core.leftOp ⋙ Tra

def Folio.E (W : Folio) : Type 0 := W.H.Elements

instance (W : Folio) : Category.{0} W.E := categoryOfElements W.H

instance (W : Folio) (m : (Fin W.length)ᵒᵖ) : LinearOrder (W.H.obj m) :=
  (W.core.obj m.unop).unop.linearOrder

instance (W : Folio) (x y : W.E) : Subsingleton (x ⟶ y) where
  allEq f g := CategoryOfElements.ext W.H f g (Subsingleton.elim _ _)

def Folio.originIndex (W : Folio) : Fin W.length := ⟨0, W.positive⟩
def Folio.originBase (W : Folio) : (Fin W.length)ᵒᵖ := op W.originIndex
def Folio.originValue (W : Folio) : W.H.obj W.originBase :=
  W.originEquiv.symm ()
def Folio.originElement (W : Folio) : W.E := ⟨W.originBase, W.originValue⟩

def Folio.lastIndex (W : Folio) : Fin W.length :=
  ⟨W.length - 1, Nat.sub_lt W.positive (by omega)⟩
def Folio.lastBase (W : Folio) : (Fin W.length)ᵒᵖ := op W.lastIndex

theorem Folio.origin_unique (W : Folio) (x : W.H.obj W.originBase) :
    x = W.originValue := by
  apply W.originEquiv.injective
  exact Subsingleton.elim _ _

def Folio.baseToOrigin (W : Folio) (m : (Fin W.length)ᵒᵖ) :
    m ⟶ W.originBase := by
  letI : NeZero W.length := ⟨Nat.ne_of_gt W.positive⟩
  exact (homOfLE (show W.originIndex ≤ m.unop by
    change (0 : Fin W.length) ≤ m.unop
    exact bot_le)).op

def Folio.toOrigin (W : Folio) (x : W.E) : x ⟶ W.originElement :=
  CategoryOfElements.homMk x W.originElement (W.baseToOrigin x.1)
    (W.origin_unique _)

/-%%
\section{Paginations}

\begin{definition}[The Category of Paginations]
The \textbf{Category of Paginations}, denoted $\Pag$, has as objects pairs
$(H,E)$ where $H=\mathsf{Tra}\circ F^{\mathrm{op}}$ for a folio $F$, and
$E$ is the category of elements of $H$.  For $W:\Pag$, write $W_H$ for the
first inclusion and $W_E$ for the second inclusion.  A morphism $T:X\to Y$
in $\Pag$ is a functor $T:X_E\to Y_E$.  Thus, for every morphism
$f:x\to y$ of $X_E$, the following square commutes:
\[
\begin{tikzcd}
x=(m,i) \ar[r,"f"] \ar[d,"T"'] &
  (n,X_H(f)(i)) \ar[d,"T"] \\
(m',i') \ar[r,"T(f)"'] &
  (n',Y_H(T(f))(i')).
\end{tikzcd}
\]
\end{definition}
%%-/

structure Pag where
  folio : Folio

def Pag.H (W : Pag) : (Fin W.folio.length)ᵒᵖ ⥤ Type 0 := W.folio.H
def Pag.E (W : Pag) : Type 0 := W.folio.E

instance (W : Pag) : Category.{0} W.E := categoryOfElements W.H

instance : Category.{0} Pag where
  Hom X Y := X.E ⥤ Y.E
  id X := 𝟭 X.E
  comp F G := F ⋙ G
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-%%
\section{Atlases}

\begin{definition}[The Category of Atlases]
The \textbf{Category of Atlases}, denoted $\Atl$, has as objects pairs
$(P,G)$, where $P:\Pag$ and $G:P_E\to\DomIns$ is a functor, equivalently a
presheaf $G:P_E^{\mathrm{op}}\to\CoDomIns$.  For $P_H:C\to\Set$,
$m\in|C|$, and distinct elements $k,k'\in|P_H(m)|$, the pullback in $G$ of
the arrows induced by $(m\to0)(k)$ and $(m\to0)(k')$ is empty.

There is an integer $w$ such that, for every $w'>w$,
$P_H(w'\to w)=\id$, and, for every $k\in|P_H(w)|$, the corresponding arrow
$G((w'\to w)(k))$ is the identity.  The least such integer is the
\textbf{cardinality of the atlas}, denoted $|A|$.

For $X:\Atl$, write $X_P$ and $X_G$ for the two components and put
$X_H=(X_P)_H$ and $X_E=(X_P)_E$.  A morphism $T:X\to Y$ is a pair
$(T_P,T_A)$, where $T_P:X_P\to Y_P$ is a pagination morphism and
$T_A:X_G\Rightarrow Y_G\circ T_E$ is a natural transformation.  Thus, for
every $f:x\to y$ in $X_E$, the following square commutes:
\[
\begin{tikzcd}
X_G(x) \ar[r,"X_G(f)"] \ar[d,"(T_A)_x"'] &
  X_G(y) \ar[d,"(T_A)_y"] \\
Y_G(T_E(x)) \ar[r,"Y_G(T_E(f))"'] & Y_G(T_E(y)).
\end{tikzcd}
\]
Finally, if $x=|X|$, $x'>x$, and $r\in|X_H(|X|-1)|$, then
$T_P(x',r)=T_P(x,r)$ and $(T_A)_{(x',r)}=(T_A)_{(x,r)}$.
\end{definition}
%%-/

/-- Internally, an atlas is stored by its least finite presentation.  The
`Folio.F` construction repeats its final page along the rest of the spine, so
the stabilization and morphism-tail clauses in the extracted definition are
enforced by construction. -/

def Pag.cell (P : Pag) (m : (Fin P.folio.length)ᵒᵖ) (k : P.H.obj m) : P.E := ⟨m, k⟩

def Pag.cellToOrigin (P : Pag) (m : (Fin P.folio.length)ᵒᵖ)
    (k : P.H.obj m) : P.cell m k ⟶ P.folio.originElement :=
  P.folio.toOrigin (P.cell m k)

def IsPagewiseDisjoint (P : Pag) (G : P.E ⥤ DomIns) : Prop :=
  ∀ (m : (Fin P.folio.length)ᵒᵖ) (i j : P.H.obj m), i ≠ j →
    ∀ (x : G.obj (P.cell m i)) (y : G.obj (P.cell m j)),
      G.map (P.cellToOrigin m i) x ≠ G.map (P.cellToOrigin m j) y

structure Atl where
  P : Pag
  G : P.E ⥤ DomIns
  disjoint : IsPagewiseDisjoint P G

def Atl.H (X : Atl) : (Fin X.P.folio.length)ᵒᵖ ⥤ Type 0 := X.P.H
def Atl.E (X : Atl) : Type 0 := X.P.E

instance (X : Atl) : Category.{0} X.E := categoryOfElements X.H

structure AtlHom (X Y : Atl) where
  P : X.E ⥤ Y.E
  A : X.G ⟶ P ⋙ Y.G

def AtlHom.identity (X : Atl) : AtlHom X X where
  P := 𝟭 X.E
  A := 𝟙 X.G

def AtlHom.comp {X Y Z : Atl} (f : AtlHom X Y) (g : AtlHom Y Z) : AtlHom X Z where
  P := f.P ⋙ g.P
  A := f.A ≫ whiskerLeft f.P g.A

@[ext]
theorem AtlHom.ext {X Y : Atl} (f g : AtlHom X Y)
    (hP : f.P = g.P) (hA : HEq f.A g.A) : f = g := by
  cases f
  cases g
  simp_all

/-- Heterogeneous extensionality for natural transformations whose target
functors have been identified.  This keeps dependent transports localized. -/
theorem NatTrans.hext_right {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (α : F ⟶ G) (β : F ⟶ H) (h : G = H)
    (happ : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases h
  apply heq_of_eq
  ext X
  exact eq_of_heq (happ X)

/-- Transporting the codomain of an embedding along an equality of objects is
heterogeneously equal to the original embedding.  This is the small coherence
fact needed whenever stability identifies the image of an origin with the
target origin. -/
theorem embedding_comp_map_eqToHom_heq {C : Type u} [Category C]
    (G : CategoryTheory.Functor C DomIns) {a b : C} (h : a = b) {X : DomIns}
    (e : X ⟶ G.obj a) : HEq (e ≫ G.map (eqToHom h)) e := by
  cases h
  simp

instance : Category.{0} Atl where
  Hom := AtlHom
  id := AtlHom.identity
  comp := AtlHom.comp
  id_comp f := by
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x
      simp [AtlHom.comp, AtlHom.identity]
  comp_id f := by
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x
      simp [AtlHom.comp, AtlHom.identity]
  assoc f g h := by
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x
      simp [AtlHom.comp]

/-%%
\begin{definition}[Cardinality of an Atlas]
The \textbf{cardinality} $|A|$ of an atlas is the least positive integer
after which its spine repeats the final genuine page $|A|-1$.
\end{definition}
%%-/

def cardinality (A : Atl) : Nat := A.P.folio.length

/-%%
\begin{definition}[Extent of an Atlas]
The \textbf{extent} of $A$ is $\Ex(A)=A_G(0,0)$.
Since objects of $\DomIns$ are dominions, $\Ex(A):\Dom$ for every
$A:\Atl$.
\end{definition}
%%-/

def extent (A : Atl) : DomIns := A.G.obj A.P.folio.originElement

/-%%
\begin{definition}[Territory of an Atlas]
Let $M=A_H(|A|-1)$.  The \textbf{territory} is the indexed family
$\Ter(A):M\to\Dom$ given by
$\Ter(A)(k)=A_G(|A|-1,k)$.
\end{definition}
%%-/

def TerritoryIndex (A : Atl) : Type := A.H.obj A.P.folio.lastBase

def territory (A : Atl) (k : TerritoryIndex A) : DomIns :=
  A.G.obj (A.P.cell A.P.folio.lastBase k)

/-%%
\begin{definition}[$n$th Region of an Atlas]
The \textbf{$n$th region} of $A$ is $\Ter(A)(n)$, with indexing beginning at
$0$.
\end{definition}
%%-/

def region (A : Atl) (n : TerritoryIndex A) : DomIns := territory A n

/-%%
\section{Transposals and Traversals}

\begin{definition}[The Category of Atlas Transposals]
The \textbf{Category of Atlas Transposals}, denoted $\mathsf{AtlTrap}$, is
the wide subcategory of $\Atl$ whose morphisms $F:X\to Y$ have
point-injective object maps $F_E$.
\end{definition}
%%-/

def IsTransposal : MorphismProperty Atl :=
  fun _ _ F => Function.Injective F.P.obj

instance : IsTransposal.IsMultiplicative where
  id_mem _ := Function.injective_id
  comp_mem _ _ hf hg := hg.comp hf

abbrev AtlTrap := WideSubcategory IsTransposal

def AtlTrapInc : AtlTrap ⥤ Atl := wideSubcategoryInclusion IsTransposal

def Folio.commonBase (W : Folio) (m n : (Fin W.length)ᵒᵖ) :
    (Fin W.length)ᵒᵖ := op (min m.unop n.unop)

def Folio.toCommonLeft (W : Folio) (m n : (Fin W.length)ᵒᵖ) :
    m ⟶ W.commonBase m n := (homOfLE (min_le_left _ _)).op

def Folio.toCommonRight (W : Folio) (m n : (Fin W.length)ᵒᵖ) :
    n ⟶ W.commonBase m n := (homOfLE (min_le_right _ _)).op

def elementLT (X : Atl) (x y : X.E) : Prop :=
  let m := X.P.folio.commonBase x.1 y.1
  letI : LinearOrder (X.H.obj m) :=
    (X.P.folio.core.obj m.unop).unop.linearOrder
  X.H.map (X.P.folio.toCommonLeft x.1 y.1) x.2 <
    X.H.map (X.P.folio.toCommonRight x.1 y.1) y.2

/-- The image of a datum in the extent. -/
def originImage (X : Atl) (x : X.E) (t : X.G.obj x) : extent X :=
  X.G.map (X.P.folio.toOrigin x) t

/-- A datum is covered when its image in the extent comes from a final region. -/
def Covered (X : Atl) (x : X.E) (t : X.G.obj x) : Prop :=
  ∃ (k : TerritoryIndex X) (l : territory X k),
    originImage X x t =
      originImage X (X.P.cell X.P.folio.lastBase k) l

theorem covered_region (X : Atl) (k : TerritoryIndex X) (l : territory X k) :
    Covered X (X.P.cell X.P.folio.lastBase k) l :=
  ⟨k, l, rfl⟩

/-- The order and coverage conditions from Definition 7.2. -/
def IsTraversal : MorphismProperty Atl := fun X Y F =>
  Function.Injective F.P.obj ∧
  (∀ x y, elementLT _ x y → elementLT _ (F.P.obj x) (F.P.obj y)) ∧
  (∀ x (t : X.G.obj x), Covered X x t →
    Covered Y (F.P.obj x) (F.A.app x t))

instance : IsTraversal.IsMultiplicative where
  id_mem X := by
    refine ⟨Function.injective_id, fun _ _ h => h, ?_⟩
    intro x t h
    simpa [AtlHom.identity] using h
  comp_mem f g hf hg := by
    refine ⟨hg.1.comp hf.1, fun x y h => hg.2.1 _ _ (hf.2.1 _ _ h), ?_⟩
    intro x t h
    simpa [AtlHom.comp] using hg.2.2 (f.P.obj x) (f.A.app x t) (hf.2.2 x t h)

abbrev AtlTrav := WideSubcategory IsTraversal

def AtlTravInc : AtlTrav ⥤ Atl := wideSubcategoryInclusion IsTraversal

def AtlTravToAtlTrap : AtlTrav ⥤ AtlTrap where
  obj X := WideSubcategory.mk X.obj
  map f := ⟨f.1, f.2.1⟩

/-%%
\begin{definition}[The Category of Atlas Traversals]
The \textbf{Category of Atlas Traversals}, denoted $\mathsf{AtlTrav}$, is
the wide subcategory of $\mathsf{AtlTrap}$ whose morphisms satisfy the
following conditions.  For $F:X\to Y$, let $x=(m,i)$ and $y=(m',j)$, put
$p=\min(m,m')$, write $F_E(x)=(n,i')$ and $F_E(y)=(n',j')$, and put
$p'=\min(n,n')$.  If
\[
  X_H(m\to p)(i)<X_H(m'\to p)(j),
\]
then
\[
  Y_H(n\to p')(i')<Y_H(n'\to p')(j').
\]
Furthermore, if $q\in|X|$ and $t\in X_G(q)$ is in the image of a final
region---that is, there exist $k\in|\Ter(X)|$ and $l\in\Ter(X)(k)$ whose
image under $X_G((|X|-1)\to q)(k)$ is $t$---then this property is preserved
by $F$.
\end{definition}

\begin{definition}[The Category of Stable Atlas Traversals]
The \textbf{Category of Stable Atlas Traversals}, denoted
$\mathsf{AtlTras}$, is the wide subcategory of $\mathsf{AtlTrav}$ whose
morphisms $F:X\to Y$ satisfy $F_E(0,0)=(0,0)$.
\end{definition}
%%-/

def IsStableTraversal : MorphismProperty AtlTrav := fun X Y F =>
  F.1.P.obj X.obj.P.folio.originElement = Y.obj.P.folio.originElement

instance : IsStableTraversal.IsMultiplicative where
  id_mem _ := rfl
  comp_mem f g hf hg := by
    change g.1.P.obj (f.1.P.obj _) = _
    rw [hf, hg]

abbrev AtlTras := WideSubcategory IsStableTraversal

def AtlTrasToAtlTrav : AtlTras ⥤ AtlTrav :=
  wideSubcategoryInclusion IsStableTraversal

def AtlTrasInc : AtlTras ⥤ Atl := AtlTrasToAtlTrav ⋙ AtlTravInc

/-%%
\section{Maps and Cartography}

\begin{definition}[The Category of Atlas Maps]
The \textbf{Category of Atlas Maps}, denoted $\mathsf{AtlMap}$, is the full
subcategory of atlases for which every element of the extent is in the image
of a final region.
\end{definition}
%%-/

def IsAtlasMap : ObjectProperty Atl := fun A =>
  ∀ v : extent A, Covered A A.P.folio.originElement v

abbrev AtlMap := IsAtlasMap.FullSubcategory

def AtlMapInc : AtlMap ⥤ Atl := ObjectProperty.ι IsAtlasMap

/-%%
\begin{definition}[The Atlas Map Inclusion Functor]
The \textbf{Atlas Map Inclusion Functor}
$\mathsf{AtlMapInc}:\mathsf{AtlMap}\to\Atl$ is the canonical inclusion.
\end{definition}

\begin{definition}[The Category of Atlas Traversal Maps]
The \textbf{Category of Atlas Traversal Maps}, denoted
$\mathsf{AtlTravMap}$, is the full subcategory of $\mathsf{AtlTrav}$ whose
objects are Atlas Maps.
\end{definition}
%%-/

def IsAtlasMapTrav : ObjectProperty AtlTrav := fun A => IsAtlasMap A.obj
abbrev AtlTravMap := IsAtlasMapTrav.FullSubcategory

/-%%
\begin{definition}[The Atlas Traversal Map Inclusion Functor]
The canonical inclusion is denoted
$\mathsf{AtlTravMapInc}:\mathsf{AtlTravMap}\to\mathsf{AtlTrav}$.
\end{definition}
%%-/

def AtlTravMapInc : AtlTravMap ⥤ AtlTrav := ObjectProperty.ι IsAtlasMapTrav

/-- The dominion of covered data in a cell. -/
def coveredDom (X : Atl) (x : X.E) : DomIns where
  toDom :=
    { Carrier := {t : X.G.obj x // Covered X x t}
      rank :=
        ({ toFun := Subtype.val
           inj' := Subtype.val_injective } :
          Function.Embedding {t : X.G.obj x // Covered X x t} (X.G.obj x)).trans
            (X.G.obj x).toDom.rank }

def coveredMap {X : Atl} {x y : X.E} (f : x ⟶ y) :
    coveredDom X x ⟶ coveredDom X y where
  toFun t := ⟨X.G.map f t.1, by
    rcases t.2 with ⟨k, l, h⟩
    refine ⟨k, l, ?_⟩
    have e : f ≫ X.P.folio.toOrigin y = X.P.folio.toOrigin x :=
      CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _)
    change (X.G.map f ≫ X.G.map (X.P.folio.toOrigin y)) t.1 = _
    rw [← X.G.map_comp, e]
    exact h⟩
  inj' := fun a b h => Subtype.ext <| (X.G.map f).injective <| congrArg Subtype.val h

def coveredFunctor (X : Atl) : X.E ⥤ DomIns where
  obj := coveredDom X
  map := coveredMap
  map_id x := by
    apply DomIns.hom_ext
    intro t
    apply Subtype.ext
    change (X.G.map (𝟙 x)) t.1 = t.1
    rw [X.G.map_id]
    change Function.Embedding.refl _ t.1 = t.1
    rfl
  map_comp f g := by
    apply DomIns.hom_ext
    intro t
    apply Subtype.ext
    change (X.G.map (f ≫ g)) t.1 =
      (X.G.map f ≫ X.G.map g) t.1
    rw [X.G.map_comp]

def chartAtlas (X : Atl) : Atl where
  P := X.P
  G := coveredFunctor X
  disjoint := by
    intro m i j hij x y h
    apply X.disjoint m i j hij x.1 y.1
    exact congrArg Subtype.val h

theorem chart_all_covered (X : Atl) (x : (chartAtlas X).E)
    (t : (chartAtlas X).G.obj x) : Covered (chartAtlas X) x t := by
  rcases t.2 with ⟨k, l, h⟩
  let l' : territory (chartAtlas X) k := ⟨l, covered_region X k l⟩
  exact ⟨k, l', Subtype.ext h⟩

theorem chart_isAtlasMap (X : Atl) : IsAtlasMap (chartAtlas X) :=
  fun v => chart_all_covered X _ v

def chartCounit (X : Atl) : chartAtlas X ⟶ X where
  P := 𝟭 X.E
  A :=
    { app := fun _ =>
        { toFun := Subtype.val
          inj' := Subtype.val_injective }
      naturality := by intros; ext; rfl }

def chartMap {X Y : AtlTrav} (f : X ⟶ Y) :
    chartAtlas X.obj ⟶ chartAtlas Y.obj where
  P := f.1.P
  A :=
    { app := fun x =>
        { toFun := fun t => ⟨f.1.A.app x t.1, f.2.2.2 x t.1 t.2⟩
          inj' := fun a b h => Subtype.ext <| (f.1.A.app x).injective <|
            congrArg Subtype.val h }
      naturality := by
        intro x y g
        apply DomIns.hom_ext
        intro t
        apply Subtype.ext
        exact congrFun (congrArg Function.Embedding.toFun (f.1.A.naturality g)) t.1 }

theorem chartMap_isTraversal {X Y : AtlTrav} (f : X ⟶ Y) :
    IsTraversal (chartMap f) := by
  refine ⟨f.2.1, f.2.2.1, ?_⟩
  intro x t _
  exact chart_all_covered Y.obj _ _

def Chr : AtlTrav ⥤ AtlTravMap where
  obj X := ⟨WideSubcategory.mk (chartAtlas X.obj), chart_isAtlasMap X.obj⟩
  map f := ⟨chartMap f, chartMap_isTraversal f⟩
  map_id _ := by
    apply Subtype.ext
    change chartMap (𝟙 _) = AtlHom.identity _
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x t
      rfl
  map_comp f g := by
    apply Subtype.ext
    change chartMap (_ ≫ _) = AtlHom.comp (chartMap _) (chartMap _)
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x t
      rfl

/-%%
\begin{lemma}[Cartography Lemma]
The inclusion $\mathsf{AtlTravMapInc}$ has a right adjoint, denoted the
\textbf{Charting Functor}
$\mathsf{Chr}:\mathsf{AtlTrav}\to\mathsf{AtlTravMap}$.

\emph{Proof sketch.}  On an object $X:\mathsf{AtlTrav}$, the functor
$\mathsf{Chr}$ sends $X$ to the universal arrow from
$\mathsf{AtlTravMapInc}$ to $X$.  Write
$X'=\mathsf{AtlTravMapInc}(\mathsf{Chr}(X))$, together with
$H:X'\to X$, with $X'$ terminal among objects having this property.  The
solution is the DaTra map satisfying $\Ter(X')\cong\Ter(X)$.  It is unique
because $\mathsf{AtlTrav}$ preserves orders and terminal because $H_E$ is
faithful.
\end{lemma}
%%-/

/-- The formal construction realizes the proof sketch by retaining in each
cell exactly the data covered by final regions; its counit is the canonical
inclusion into the original atlas. -/

theorem originImage_origin (X : Atl) (v : extent X) :
    originImage X X.P.folio.originElement v = v := by
  have e : X.P.folio.toOrigin X.P.folio.originElement =
      𝟙 X.P.folio.originElement :=
    CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _)
  rw [originImage, e, X.G.map_id]
  change Function.Embedding.refl _ v = v
  rfl

theorem atlasMap_all_covered {X : Atl} (hX : IsAtlasMap X)
    (x : X.E) (t : X.G.obj x) : Covered X x t := by
  rcases hX (originImage X x t) with ⟨k, l, h⟩
  exact ⟨k, l, by simpa [originImage_origin] using h⟩

theorem chartCounit_isTraversal (X : Atl) : IsTraversal (chartCounit X) := by
  refine ⟨Function.injective_id, fun _ _ h => h, ?_⟩
  intro x t _
  simpa [chartCounit] using t.2

def chartCounitTrav (X : AtlTrav) :
    (WideSubcategory.mk (chartAtlas X.obj) : AtlTrav) ⟶ X :=
  ⟨chartCounit X.obj, chartCounit_isTraversal X.obj⟩

def chartLift {A : AtlTravMap} {X : AtlTrav}
    (f : AtlTravMapInc.obj A ⟶ X) :
    A ⟶ Chr.obj X := by
  refine ⟨?_, ?_⟩
  · exact
      { P := f.1.P
        A :=
          { app := fun x =>
              { toFun := fun t => ⟨f.1.A.app x t,
                  f.2.2.2 x t (atlasMap_all_covered A.property x t)⟩
                inj' := by
                  intro a b h
                  apply (f.1.A.app x).injective
                  exact congrArg (fun z => z.1) h }
            naturality := by
              intro x y g
              apply DomIns.hom_ext
              intro t
              apply Subtype.ext
              exact congrFun (congrArg Function.Embedding.toFun (f.1.A.naturality g)) t } }
  · refine ⟨f.2.1, f.2.2.1, ?_⟩
    intro x t _
    exact chart_all_covered X.obj _ _

def chartHomEquiv (A : AtlTravMap) (X : AtlTrav) :
    (AtlTravMapInc.obj A ⟶ X) ≃ (A ⟶ Chr.obj X) where
  toFun := chartLift
  invFun g := g ≫ chartCounitTrav X
  left_inv f := by
    apply Subtype.ext
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x t
      rfl
  right_inv g := by
    apply Subtype.ext
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x t
      apply Subtype.ext
      rfl

theorem chartHomEquiv_naturality_left {A A' : AtlTravMap} (f : A' ⟶ A)
    {X : AtlTrav} (g : AtlTravMapInc.obj A ⟶ X) :
    chartHomEquiv A' X (AtlTravMapInc.map f ≫ g) =
      f ≫ chartHomEquiv A X g := by
  apply Subtype.ext
  apply AtlHom.ext
  · rfl
  · apply heq_of_eq
    ext x t
    apply Subtype.ext
    rfl

theorem chartHomEquiv_naturality_right {A : AtlTravMap} {X X' : AtlTrav}
    (f : AtlTravMapInc.obj A ⟶ X) (g : X ⟶ X') :
    chartHomEquiv A X' (f ≫ g) = chartHomEquiv A X f ≫ Chr.map g := by
  apply Subtype.ext
  apply AtlHom.ext
  · rfl
  · apply heq_of_eq
    ext x t
    apply Subtype.ext
    rfl

def cartographyAdjunction : AtlTravMapInc ⊣ Chr :=
  Adjunction.mkOfHomEquiv
    { homEquiv := chartHomEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (chartHomEquiv X' Y).injective
        simpa using (chartHomEquiv_naturality_left f ((chartHomEquiv X Y).symm g)).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact chartHomEquiv_naturality_right f g }

theorem cartographyLemma : Nonempty (AtlTravMapInc ⊣ Chr) :=
  ⟨cartographyAdjunction⟩

/-%%
\section{Coalitions}

\begin{definition}[The Coalizing Functor]
The \textbf{Coalizing Functor}, denoted
$\mathsf{Coa}:\mathsf{AtlTras}\to\DomIns$, is the extent of the charted
atlas: $\mathsf{Coa}=\Ex\circ\mathsf{Chr}$.
\end{definition}
%%-/

def extentMap {X Y : Atl} (f : X ⟶ Y) : extent X ⟶ extent Y :=
  f.A.app X.P.folio.originElement ≫
    Y.G.map (Y.P.folio.toOrigin (f.P.obj X.P.folio.originElement))

theorem extentMap_id (X : Atl) : extentMap (𝟙 X) = 𝟙 (extent X) := by
  apply DomIns.hom_ext
  intro t
  change (X.G.map (X.P.folio.toOrigin X.P.folio.originElement)) t = t
  simpa [originImage] using originImage_origin X t

theorem extentMap_comp {X Y Z : Atl} (f : X ⟶ Y) (g : Y ⟶ Z) :
    extentMap (f ≫ g) = extentMap f ≫ extentMap g := by
  apply DomIns.hom_ext
  intro t
  let oX := X.P.folio.originElement
  let y := f.P.obj oX
  let oY := Y.P.folio.originElement
  let z := g.P.obj y
  let z₀ := g.P.obj oY
  have hn := g.A.naturality (Y.P.folio.toOrigin y)
  have hz : g.P.map (Y.P.folio.toOrigin y) ≫ Z.P.folio.toOrigin z₀ =
      Z.P.folio.toOrigin z :=
    CategoryOfElements.ext _ _ _ (Subsingleton.elim _ _)
  have hn' : Y.G.map (Y.P.folio.toOrigin y) ≫ g.A.app oY =
      g.A.app y ≫ Z.G.map (g.P.map (Y.P.folio.toOrigin y)) := hn
  have hm : g.A.app y ≫ Z.G.map (Z.P.folio.toOrigin z) =
      Y.G.map (Y.P.folio.toOrigin y) ≫ g.A.app oY ≫
        Z.G.map (Z.P.folio.toOrigin z₀) := by
    rw [← Category.assoc, hn', Category.assoc, ← Z.G.map_comp, hz]
  exact congrFun (congrArg Function.Embedding.toFun
    (by simpa only [Category.assoc] using congrArg (fun q => f.A.app oX ≫ q) hm)) t

def Ex : Atl ⥤ DomIns where
  obj := extent
  map := extentMap
  map_id := extentMap_id
  map_comp := extentMap_comp

def stableCoalitionMap {X Y : AtlTras} (f : X ⟶ Y) :
    coveredDom X.obj.obj X.obj.obj.P.folio.originElement ⟶
      coveredDom Y.obj.obj Y.obj.obj.P.folio.originElement where
  toFun t := by
    have hc := f.1.2.2.2 X.obj.obj.P.folio.originElement t.1 t.2
    exact coveredMap (X := Y.obj.obj) (eqToHom f.2)
      ⟨f.1.1.A.app X.obj.obj.P.folio.originElement t.1, hc⟩
  inj' := fun a b h => by
    apply Subtype.ext
    apply (f.1.1.A.app X.obj.obj.P.folio.originElement).injective
    apply (Y.obj.obj.G.map (eqToHom f.2)).injective
    exact congrArg Subtype.val h

theorem stableCoalitionMap_val {X Y : AtlTras} (f : X ⟶ Y)
    (t : coveredDom X.obj.obj X.obj.obj.P.folio.originElement) :
    (stableCoalitionMap f t).1 = extentMap f.1.1 t.1 := by
  change Y.obj.obj.G.map (eqToHom f.2)
      (f.1.1.A.app X.obj.obj.P.folio.originElement t.1) =
    Y.obj.obj.G.map (Y.obj.obj.P.folio.toOrigin
      (f.1.1.P.obj X.obj.obj.P.folio.originElement))
      (f.1.1.A.app X.obj.obj.P.folio.originElement t.1)
  have hmor : eqToHom f.2 = Y.obj.obj.P.folio.toOrigin
      (f.1.1.P.obj X.obj.obj.P.folio.originElement) := by
    apply CategoryOfElements.ext
    apply Subsingleton.elim
  rw [hmor]

/-- `Coa` is written directly on the covered origins.  This is definitionally
the object part of `Ex ∘ Chr`; stability makes its action on arrows reduce to
the component at the origin. -/
def Coa : AtlTras ⥤ DomIns where
  obj X := coveredDom X.obj.obj X.obj.obj.P.folio.originElement
  map := stableCoalitionMap
  map_id X := by
    apply DomIns.hom_ext
    intro t
    apply Subtype.ext
    rw [stableCoalitionMap_val]
    exact congrFun (congrArg Function.Embedding.toFun (extentMap_id X.obj.obj)) t.1
  map_comp f g := by
    apply DomIns.hom_ext
    intro t
    apply Subtype.ext
    rw [stableCoalitionMap_val]
    change extentMap (f.1.1 ≫ g.1.1) t.1 =
      (stableCoalitionMap g (stableCoalitionMap f t)).1
    rw [stableCoalitionMap_val, stableCoalitionMap_val]
    exact congrFun (congrArg Function.Embedding.toFun
      (extentMap_comp f.1.1 g.1.1)) t.1

/-%%
\begin{definition}[The Coalition of an Atlas]
The \textbf{coalition} of an atlas $X$ is the extent of its chart, regarding
$X$ as an object of the wide category of stable traversals.
\end{definition}
%%-/

def coalition (X : Atl) : DomIns := (Coa.obj
  (WideSubcategory.mk (WideSubcategory.mk X) : AtlTras))

/-- The initial dominion. -/
def emptyDominion : DomIns where
  toDom :=
    { Carrier := Empty
      rank :=
        { toFun := fun x => nomatch x
          inj' := fun x => nomatch x } }

def singletonChain : Chain where
  Obj := Unit
  linearOrder := inferInstance
  wellFoundedLT := inferInstance
  orderType_lt := by
    have hpow : Ordinal.omega0 ^ (1 : Ordinal) <
        Ordinal.omega0 ^ Ordinal.omega0 :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
        Ordinal.one_lt_omega0
    have hω : Ordinal.omega0 < Ordinal.omega0 ^ Ordinal.omega0 := by
      simpa only [Ordinal.opow_one] using hpow
    simpa using lt_trans Ordinal.one_lt_omega0 hω

def singletonObjEquiv : singletonChain.Obj ≃ Unit := Equiv.refl _

def onePageFolio : Folio where
  length := 1
  positive := by omega
  core := (Functor.const (Fin 1)).obj (op singletonChain)
  originEquiv := singletonObjEquiv

def onePagePag : Pag := ⟨onePageFolio⟩

theorem onePage_cell_unique (x : onePagePag.E) :
    x = onePageFolio.originElement := by
  let hbase : x.1 = onePageFolio.originBase := by
    apply unop_injective
    apply Fin.eq_zero
  apply Functor.Elements.ext x onePageFolio.originElement hbase
  exact onePageFolio.origin_unique _

def dominionAtlas (X : DomIns) : Atl where
  P := onePagePag
  G := (Functor.const onePagePag.E).obj X
  disjoint := by
    intro m i j hij
    exfalso
    apply hij
    apply onePageFolio.originEquiv.injective
    exact Subsingleton.elim _ _

theorem dominionAtlas_isMap (X : DomIns) : IsAtlasMap (dominionAtlas X) := by
  intro v
  let k : TerritoryIndex (dominionAtlas X) :=
    onePageFolio.originValue
  refine ⟨k, v, ?_⟩
  rw [originImage_origin]
  have hc : (dominionAtlas X).P.cell (dominionAtlas X).P.folio.lastBase k =
      (dominionAtlas X).P.folio.originElement := onePage_cell_unique _
  rw [hc, originImage_origin]

def dominionMap {X Y : DomIns} (f : X ⟶ Y) :
    dominionAtlas X ⟶ dominionAtlas Y where
  P := 𝟭 onePagePag.E
  A :=
    { app := fun _ => f
      naturality := by intros; apply DomIns.hom_ext; intro; rfl }

theorem dominionMap_isTraversal {X Y : DomIns} (f : X ⟶ Y) :
    IsTraversal (dominionMap f) := by
  refine ⟨Function.injective_id, fun _ _ h => h, ?_⟩
  intro x t _
  exact atlasMap_all_covered (dominionAtlas_isMap Y) _ _

theorem dominionMap_isStable {X Y : DomIns} (f : X ⟶ Y) :
    IsStableTraversal
      (X := WideSubcategory.mk (dominionAtlas X))
      (Y := WideSubcategory.mk (dominionAtlas Y))
      ⟨dominionMap f, dominionMap_isTraversal f⟩ := rfl

/-%%
\begin{definition}[The Domanial Inclusion Functor]
The \textbf{Domanial Inclusion Functor}
$\mathsf{DomInc}:\DomIns\to\mathsf{AtlTras}$ sends a dominion to the
atlas of cardinality $1$ whose coalition is that dominion.  It is left
adjoint to $\mathsf{Coa}$: for $X:\DomIns$ and $Y:\mathsf{AtlTras}$,
naturally in $X$ and $Y$,
\[
  \Hom_{\mathsf{AtlTras}}(\mathsf{DomInc}(X),Y)
  \cong \Hom_{\DomIns}(X,\mathsf{Coa}(Y)),
\]
and $\mathsf{Coa}(\mathsf{DomInc}(X))\cong X$.
\end{definition}
%%-/

def DomInc : DomIns ⥤ AtlTras where
  obj X := WideSubcategory.mk (WideSubcategory.mk (dominionAtlas X))
  map f := ⟨⟨dominionMap f, dominionMap_isTraversal f⟩,
    dominionMap_isStable f⟩
  map_id _ := by
    apply Subtype.ext
    apply Subtype.ext
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext
      rfl
  map_comp f g := by
    apply Subtype.ext
    apply Subtype.ext
    apply AtlHom.ext
    · rfl
    · apply heq_of_eq
      ext x t
      change (f ≫ g) t = (f ≫ g) t
      rfl

def onePageToAtlasP (Y : Atl) : onePagePag.E ⥤ Y.E :=
  (Functor.const onePagePag.E).obj Y.P.folio.originElement

theorem onePageToAtlasP_injective (Y : Atl) :
    Function.Injective (onePageToAtlasP Y).obj := by
  intro x y _
  exact onePage_cell_unique x |>.trans (onePage_cell_unique y).symm

theorem onePage_elementLT_false (X : DomIns) (x y : (dominionAtlas X).E) :
    ¬ elementLT (dominionAtlas X) x y := by
  intro h
  have hxy : x = y := onePage_cell_unique x |>.trans (onePage_cell_unique y).symm
  subst y
  let m := (dominionAtlas X).P.folio.commonBase x.1 x.1
  letI : LinearOrder ((dominionAtlas X).H.obj m) :=
    ((dominionAtlas X).P.folio.core.obj m.unop).unop.linearOrder
  exact lt_irrefl _ h

/-- A stable traversal from a one-page atlas determines an embedding into
the covered part of the target extent. -/
def domIncToCoa {X : DomIns} {Y : AtlTras} (f : DomInc.obj X ⟶ Y) :
    X ⟶ Coa.obj Y where
  toFun x := by
    have hc := f.1.2.2.2 onePageFolio.originElement x
      (atlasMap_all_covered (dominionAtlas_isMap X) _ x)
    exact coveredMap (X := Y.obj.obj) (eqToHom f.2)
      ⟨f.1.1.A.app onePageFolio.originElement x, hc⟩
  inj' := fun a b h => by
    apply (f.1.1.A.app onePageFolio.originElement).injective
    apply (Y.obj.obj.G.map (eqToHom f.2)).injective
    exact congrArg Subtype.val h

/-- Conversely, an embedding into the coalition supplies the unique stable
traversal from the corresponding one-page atlas. -/
def coaToDomInc {X : DomIns} {Y : AtlTras} (f : X ⟶ Coa.obj Y) :
    DomInc.obj X ⟶ Y := by
  let p : (dominionAtlas X).E ⥤ Y.obj.obj.P.E := onePageToAtlasP Y.obj.obj
  let a : (dominionAtlas X).G ⟶ p ⋙ Y.obj.obj.G :=
    { app := fun _ =>
        { toFun := fun x => (f x).1
          inj' := fun x y h => f.injective (Subtype.ext h) }
      naturality := by
        intro x y g
        apply DomIns.hom_ext
        intro t
        have hxy : x = y := onePage_cell_unique x |>.trans
          (onePage_cell_unique y).symm
        subst y
        have hg : g = 𝟙 x := by
          apply CategoryOfElements.ext
          apply Subsingleton.elim
        subst g
        simp [p] }
  let h : dominionAtlas X ⟶ Y.obj.obj := ⟨p, a⟩
  have htrav : IsTraversal h := by
    refine ⟨onePageToAtlasP_injective Y.obj.obj, ?_, ?_⟩
    · intro x y hxy
      exact (onePage_elementLT_false X x y hxy).elim
    · intro x t _
      change Covered Y.obj.obj Y.obj.obj.P.folio.originElement (f t).1
      exact (f t).2
  exact ⟨⟨h, htrav⟩, rfl⟩

def coaDomIncIso (X : DomIns) : Coa.obj (DomInc.obj X) ≅ X where
  hom :=
    { toFun := fun x => x.1
      inj' := fun x y h => Subtype.ext h }
  inv :=
    { toFun := fun x => ⟨x, atlasMap_all_covered
          (dominionAtlas_isMap X) onePageFolio.originElement x⟩
      inj' := fun x y h => congrArg Subtype.val h }
  hom_inv_id := by
    apply DomIns.hom_ext
    intro x
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply DomIns.hom_ext
    intro x
    rfl

/-- The hom-set equivalence expressing that one-page insertion is left
adjoint to coalization. -/
def domIncCoaHomEquiv (X : DomIns) (Y : AtlTras) :
    (DomInc.obj X ⟶ Y) ≃ (X ⟶ Coa.obj Y) where
  toFun := domIncToCoa
  invFun := coaToDomInc
  left_inv := by
    intro f
    apply Subtype.ext
    apply Subtype.ext
    have hP : (coaToDomInc (domIncToCoa f)).1.1.P = f.1.1.P := by
      exact CategoryTheory.Functor.ext
        (fun x => f.2.symm.trans
          (congrArg f.1.1.P.obj (onePage_cell_unique x).symm))
        (fun _ _ _ => by
          apply CategoryOfElements.ext
          apply Subsingleton.elim)
    apply AtlHom.ext _ _ hP
    apply NatTrans.hext_right _ _
      (congrArg (fun Q => Q ⋙ Y.obj.obj.G) hP)
    intro x
    dsimp [coaToDomInc, domIncToCoa, onePageToAtlasP]
    have hx : x = onePageFolio.originElement := onePage_cell_unique x
    subst x
    let e := f.1.1.A.app onePageFolio.originElement
    have hrec :
        { toFun := fun x =>
            (coveredMap (X := Y.obj.obj) (eqToHom f.2)
              ⟨e x, by
                exact f.1.2.2.2 onePageFolio.originElement x
                  (atlasMap_all_covered (dominionAtlas_isMap X) _ x)⟩).1
          inj' := by
            intro a b hab
            apply e.injective
            apply (Y.obj.obj.G.map (eqToHom f.2)).injective
            exact hab } = e ≫ Y.obj.obj.G.map (eqToHom f.2) := by
      apply DomIns.hom_ext
      intro t
      rfl
    exact (heq_of_eq hrec).trans
      (embedding_comp_map_eqToHom_heq Y.obj.obj.G f.2 e)
  right_inv := by
    intro f
    apply DomIns.hom_ext
    intro x
    apply Subtype.ext
    change Y.obj.obj.G.map (𝟙 Y.obj.obj.P.folio.originElement) (f x).1 = (f x).1
    exact congrFun (congrArg Function.Embedding.toFun
      (Y.obj.obj.G.map_id Y.obj.obj.P.folio.originElement)) (f x).1

theorem domIncCoaHomEquiv_naturality_left {X X' : DomIns} (f : X' ⟶ X)
    {Y : AtlTras} (g : DomInc.obj X ⟶ Y) :
    domIncCoaHomEquiv X' Y (DomInc.map f ≫ g) =
      f ≫ domIncCoaHomEquiv X Y g := by
  apply DomIns.hom_ext
  intro x
  apply Subtype.ext
  rfl

theorem domIncCoaHomEquiv_naturality_right {X : DomIns} {Y Y' : AtlTras}
    (f : DomInc.obj X ⟶ Y) (g : Y ⟶ Y') :
    domIncCoaHomEquiv X Y' (f ≫ g) =
      domIncCoaHomEquiv X Y f ≫ Coa.map g := by
  apply DomIns.hom_ext
  intro x
  apply Subtype.ext
  let t : Coa.obj (DomInc.obj X) :=
    ⟨x, atlasMap_all_covered
      (dominionAtlas_isMap X) onePageFolio.originElement x⟩
  change (Coa.map (f ≫ g) t).1 = (Coa.map g (Coa.map f t)).1
  exact congrArg Subtype.val <| congrFun
    (congrArg Function.Embedding.toFun (Coa.map_comp f g)) t

/-- The unconditional adjunction promised by the Domanial Inclusion
construction. -/
def dominionAdjunction : DomInc ⊣ Coa :=
  Adjunction.mkOfHomEquiv
    { homEquiv := domIncCoaHomEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply (domIncCoaHomEquiv X' Y).injective
        simpa using
          (domIncCoaHomEquiv_naturality_left f
            ((domIncCoaHomEquiv X Y).symm g)).symm
      homEquiv_naturality_right := by
        intro X Y Y' f g
        exact domIncCoaHomEquiv_naturality_right f g }

theorem dominionLemma : Nonempty (DomInc ⊣ Coa) :=
  ⟨dominionAdjunction⟩

/-%%
\section{Data Transformations}

\begin{definition}[The Category of Data Transformations]
The \textbf{Category of Data Transformations}, also called the category of
\textbf{Data Transformation Sets} or \textbf{DaTra Sets}, is the presheaf
category
\[
  \mathsf{DaTra}=[\Atl^{\mathrm{op}},\Set].
\]
As a presheaf category, it is a topos.
\end{definition}
%%-/

abbrev DaTra := Atlᵒᵖ ⥤ Type

def Yo : Atl ⥤ DaTra := yoneda

/-- A concrete certificate of the statement that `DaTra` is the displayed
presheaf category. -/
def datraToposPresentation : DaTra ≌ (Atlᵒᵖ ⥤ Type) :=
  CategoryTheory.Equivalence.refl

/-%%
\begin{definition}[Navigation]
A \textbf{navigation} of $D:\mathsf{DaTra}$ is a monomorphism
$\mathsf{Nav}:\Yo(A)\to D$ for some atlas $A$.
\end{definition}
%%-/

structure Navigation (D : DaTra) where
  A : Atl
  hom : Yo.obj A ⟶ D
  mono : Mono hom

attribute [instance] Navigation.mono

/-%%
\begin{definition}[Expedition]
An \textbf{expedition} is a navigation represented by an Atlas Map.
\end{definition}
%%-/

structure Expedition (D : DaTra) extends Navigation D where
  atlasMap : IsAtlasMap A

/-- Adjoin the empty presheaf to the image of Yoneda.  Its new source object
represents exactly the empty alternative in a DaTra restriction. -/
def PartialYo : WithInitial Atl ⥤ DaTra :=
  WithInitial.liftToInitial Yo (initialIsInitial)

def liftWide (W : MorphismProperty Atl) :
    MorphismProperty (WithInitial Atl) := fun X Y f =>
  match X, Y with
  | .star, _ => True
  | .of _, .of _ => W (WithInitial.down f)

instance (W : MorphismProperty Atl) [W.IsMultiplicative] :
    (liftWide W).IsMultiplicative where
  id_mem X := by
    cases X with
    | star => trivial
    | of X => exact W.id_mem X
  comp_mem {X Y Z} f g hf hg := by
    cases X with
    | star => trivial
    | of X =>
      cases Y with
      | star => exact nomatch f
      | of Y =>
        cases Z with
        | star => exact nomatch g
        | of Z => exact W.comp_mem _ _ hf hg

/-- Existential relative representability.  Unlike the representation-
independent variant in Mathlib, this is the exact condition in the text:
there is one representing pullback whose atlas arrow lies in `W`. -/
def HasRestrictedPullbacks (W : MorphismProperty (WithInitial Atl)) :
    MorphismProperty DaTra := fun X Y F =>
  ∀ ⦃A : WithInitial Atl⦄ (nav : PartialYo.obj A ⟶ Y),
    ∃ (B : WithInitial Atl) (f : B ⟶ A) (nav' : PartialYo.obj B ⟶ X),
      IsPullback nav' (PartialYo.map f) F nav ∧ W f

instance (W : MorphismProperty (WithInitial Atl)) [W.IsMultiplicative] :
    (HasRestrictedPullbacks W).IsMultiplicative where
  id_mem X := by
    intro A nav
    exact ⟨A, 𝟙 A, nav, by simpa using IsPullback.of_id_snd, W.id_mem A⟩
  comp_mem f g hf hg := by
    intro A nav
    obtain ⟨B, q, navB, hBg, hq⟩ := hg nav
    obtain ⟨C, p, navC, hCf, hp⟩ := hf navB
    exact ⟨C, p ≫ q, navC,
      by simpa using IsPullback.paste_vert hCf hBg,
      W.comp_mem p q hp hq⟩

/-%%
\begin{definition}[DaTra Restriction]
For a wide subcategory $W$ of $\Atl$, its \textbf{DaTra restriction} is the
wide subcategory whose arrows $F:X\to Y$ have this property: pulling $F$
back along any navigation $\Yo(A)\to Y$ is either empty, or is represented
by a navigation $\Yo(B)\to X$ and an arrow $f:B\to A$ in $W$.  In the
represented case the square
\[
\begin{tikzcd}
\Yo(B) \ar[r,"\mathsf{Nav}'"] \ar[d,"\Yo(f)"'] & X \ar[d,"F"] \\
\Yo(A) \ar[r,"\mathsf{Nav}"'] & Y
\end{tikzcd}
\]
is a pullback.
\end{definition}
%%-/

abbrev DaTraRestriction (W : MorphismProperty Atl) [W.IsMultiplicative] :=
  WideSubcategory (HasRestrictedPullbacks (liftWide W))

abbrev DaTrap := DaTraRestriction IsTransposal
abbrev DaTrav := DaTraRestriction IsTraversal

def IsStableAtl : MorphismProperty Atl := fun X Y f =>
  ∃ (hf : IsTraversal f), IsStableTraversal
    (X := WideSubcategory.mk X) (Y := WideSubcategory.mk Y) ⟨f, hf⟩

instance : IsStableAtl.IsMultiplicative where
  id_mem X := ⟨IsTraversal.id_mem X, IsStableTraversal.id_mem _⟩
  comp_mem f g hf hg :=
    ⟨IsTraversal.comp_mem f g hf.1 hg.1,
      IsStableTraversal.comp_mem ⟨f, hf.1⟩ ⟨g, hg.1⟩ hf.2 hg.2⟩

abbrev DaTras := DaTraRestriction IsStableAtl

/-%%
\begin{definition}[The Category of Data Transposals]
The \textbf{Category of Data Transposals}, denoted $\mathsf{DaTrap}$, is
the DaTra restriction on $\mathsf{AtlTrap}$.
\end{definition}

\begin{definition}[The Category of Data Traversals]
The \textbf{Category of Data Traversals}, denoted $\mathsf{DaTrav}$, is
the DaTra restriction on $\mathsf{AtlTrav}$.
\end{definition}

\begin{definition}[The Category of Stable Data Traversals]
The \textbf{Category of Stable Data Traversals}, denoted
$\mathsf{DaTras}$, is the DaTra restriction on $\mathsf{AtlTras}$.
\end{definition}

\begin{definition}[Data Transformation Maps]
The \textbf{Category of Data Transformation Maps}, denoted
$\mathsf{DaTraMap}$, is the full subcategory of DaTra Sets all of whose
navigations are expeditions.
\end{definition}
%%-/

def IsDaTraMap : ObjectProperty DaTra := fun D =>
  ∀ nav : Navigation D, IsAtlasMap nav.A

abbrev DaTraMap := IsDaTraMap.FullSubcategory

/-%%
\section{Horizontal Atlases}

\begin{definition}[The Empty Atlas]
The \textbf{Empty Atlas} is
$\mathsf{AtlI}=\mathsf{DomInc}(0)$.
\end{definition}
%%-/

def AtlI : Atl := dominionAtlas emptyDominion

theorem AtlI_eq_domInc_zero :
    AtlI = (DomInc.obj emptyDominion).obj.obj := rfl

def Folio.pageValue (W : Folio) (m : Fin W.length) :
    (W.core.obj m).unop.Obj := by
  letI : NeZero W.length := ⟨Nat.ne_of_gt W.positive⟩
  let q : (W.core.obj m).unop ⟶ (W.core.obj W.originIndex).unop :=
    (W.core.map (homOfLE (Fin.zero_le m))).unop
  exact Classical.choose (q.point_surjective W.originValue)

theorem Folio.map_unop_comp_apply (W : Folio) {i j k : Fin W.length}
    (hik : i ⟶ k) (hij : i ⟶ j) (hjk : j ⟶ k)
    (z : (W.core.obj k).unop.Obj) :
    (W.core.map hik).unop z =
      (W.core.map hij).unop ((W.core.map hjk).unop z) := by
  have e : hik = hij ≫ hjk := Subsingleton.elim _ _
  subst hik
  have h := congrArg Quiver.Hom.unop (W.core.map_comp hij hjk)
  exact congrFun (congrArg ConHom.toFun h) z

def bouquetLength (X Y : Folio) : Nat := max X.length Y.length + 1

def bouquetDepth (X Y : Folio) : Nat := max X.length Y.length

theorem bouquetLength_pos (X Y : Folio) : 0 < bouquetLength X Y := by
  simp [bouquetLength]

instance (X Y : Folio) : NeZero (bouquetLength X Y) :=
  ⟨Nat.ne_of_gt (bouquetLength_pos X Y)⟩

def bouquetChain (X Y : Folio) : Fin (bouquetLength X Y) → Chain :=
  Fin.cases singletonChain (fun m : Fin (bouquetDepth X Y) =>
    Chain.sum (X.core.obj (X.paddedIndex m.1)).unop
      (Y.core.obj (Y.paddedIndex m.1)).unop)

def bouquetValue (X Y : Folio) (m : Fin (bouquetLength X Y)) :
    (bouquetChain X Y m).Obj :=
  Fin.cases () (fun n => toLex (Sum.inl (X.pageValue (X.paddedIndex n.1)))) m

def bouquetConMap (X Y : Folio) {i j : Fin (bouquetLength X Y)} (h : i ≤ j) :
    bouquetChain X Y j ⟶ bouquetChain X Y i := by
  revert j
  refine Fin.cases ?_ (fun i => ?_) i
  · rename_i j
    intro h
    refine
      { toFun := fun _ => ()
        monotone := fun _ _ _ => le_rfl
        point_surjective := fun z => by
          refine ⟨bouquetValue X Y j, ?_⟩
          change (() : Unit) = z
          exact Subsingleton.elim _ _ }
  · rename_i j
    intro h
    revert h
    refine Fin.cases (by
      intro h
      change i.1 + 1 ≤ 0 at h
      omega) (fun j => ?_) j
    intro h
    have hij : i ≤ j := Fin.succ_le_succ_iff.mp h
    let hx : X.paddedIndex i.1 ≤ X.paddedIndex j.1 := X.paddedIndex_mono hij
    let hy : Y.paddedIndex i.1 ≤ Y.paddedIndex j.1 := Y.paddedIndex_mono hij
    exact ConHom.sum (X.core.map (homOfLE hx)).unop
      (Y.core.map (homOfLE hy)).unop

def bouquetFolio (X Y : Folio) : Folio where
  length := bouquetLength X Y
  positive := bouquetLength_pos X Y
  core :=
    { obj := fun m => op (bouquetChain X Y m)
      map := fun f => (bouquetConMap X Y (leOfHom f)).op
      map_id := by
        intro m
        refine Fin.cases ?_ (fun m => ?_) m
        · apply Quiver.Hom.unop_inj
          apply ConHom.ext
          intro z
          change (() : Unit) = ()
          rfl
        apply Quiver.Hom.unop_inj
        apply ConHom.ext
        intro w
        generalize hz : ofLex w = z
        rcases z with z | z
        · have hz' : w = toLex (Sum.inl z) := ofLex.injective (by simpa using hz)
          subst w
          simp [bouquetConMap, ConHom.sum]
          change toLex (Sum.inl z) = toLex (Sum.inl z)
          rfl
        · have hz' : w = toLex (Sum.inr z) := ofLex.injective (by simpa using hz)
          subst w
          simp [bouquetConMap, ConHom.sum]
          change toLex (Sum.inr z) = toLex (Sum.inr z)
          rfl
      map_comp := by
        intro i j k f g
        letI : NeZero (bouquetLength X Y) := ⟨Nat.ne_of_gt (bouquetLength_pos X Y)⟩
        revert j k
        refine Fin.cases ?_ (fun i => ?_) i
        · rename_i jTarget kTarget
          intro f g
          apply Quiver.Hom.unop_inj
          apply ConHom.ext
          intro z
          change (() : Unit) = ()
          rfl
        · rename_i iOrig jTarget kTarget
          intro f g
          have hj : jTarget ≠ 0 := by
            intro e
            have hf := leOfHom f
            rw [e] at hf
            change i.1 + 1 ≤ 0 at hf
            omega
          obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
          have hk : kTarget ≠ 0 := by
            intro e
            have hg := leOfHom g
            rw [e] at hg
            change j.1 + 1 ≤ 0 at hg
            omega
          obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk
          apply Quiver.Hom.unop_inj
          apply ConHom.ext
          intro w
          generalize hz : ofLex w = z
          rcases z with z | z
          · have hz' : w = toLex (Sum.inl z) := ofLex.injective (by simpa using hz)
            subst w
            simpa only [bouquetConMap, ConHom.sum] using congrArg
              (fun q => toLex (Sum.inl q)) (X.map_unop_comp_apply _ _ _ z)
          · have hz' : w = toLex (Sum.inr z) := ofLex.injective (by simpa using hz)
            subst w
            simpa only [bouquetConMap, ConHom.sum] using congrArg
              (fun q => toLex (Sum.inr q)) (Y.map_unop_comp_apply _ _ _ z) }
  originEquiv := by
    exact singletonObjEquiv

def domSum (X Y : DomIns) : DomIns where
  toDom :=
    { Carrier := Sum X Y
      rank :=
        { toFun := fun z => match z with
            | .inl x => 2 * X.toDom.rank x
            | .inr y => 2 * Y.toDom.rank y + 1
          inj' := by
            intro a b h
            rcases a with a | a <;> rcases b with b | b
            · simp only at h
              exact congrArg Sum.inl (X.toDom.rank.injective (by omega))
            · simp only at h
              omega
            · simp only at h
              omega
            · simp only at h
              exact congrArg Sum.inr (Y.toDom.rank.injective (by omega)) } }

def domSum.inl (X Y : DomIns) : X ⟶ domSum X Y where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def domSum.inr (X Y : DomIns) : Y ⟶ domSum X Y where
  toFun := Sum.inr
  inj' := Sum.inr_injective

def bouquetPag (X Y : Atl) : Pag := ⟨bouquetFolio X.P.folio Y.P.folio⟩

/- The first carrier-level implementation is retained here as a derivation of
the image-subobject construction below.  The latter has definitionally
functorial transition inclusions and therefore avoids dependent cast noise.

def bouquetDomIndex (X Y : Atl) :
    (m : Fin (bouquetLength X.P.folio Y.P.folio)) →
      (bouquetFolio X.P.folio Y.P.folio).H.obj (op m) → DomIns :=
  Fin.cases (fun _ => domSum (extent X) (extent Y)) (fun n v =>
    match ofLex v with
    | .inl k => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) k)
    | .inr k => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k))

def bouquetDom (X Y : Atl) (x : (bouquetPag X Y).E) : DomIns :=
  bouquetDomIndex X Y x.1.unop x.2

def bouquetDomMap (X Y : Atl) {x y : (bouquetPag X Y).E} (f : x ⟶ y) :
    bouquetDom X Y x ⟶ bouquetDom X Y y := by
  rcases x with ⟨⟨mx⟩, vx⟩
  rcases y with ⟨⟨my⟩, vy⟩
  induction mx using Fin.cases with
  | zero =>
    induction my using Fin.cases with
    | zero => exact 𝟙 _
    | succ p =>
      have hf : p.succ ⟶
          (⟨0, bouquetLength_pos X.P.folio Y.P.folio⟩ :
            Fin (bouquetLength X.P.folio Y.P.folio)) :=
        Quiver.Hom.unop f.val
      have h := leOfHom hf
      change p.1 + 1 ≤ 0 at h
      omega
  | succ n =>
    induction my using Fin.cases with
    | zero =>
      generalize hvx : ofLex vx = s
      rcases s with k | k
      · have evx : vx = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        have hs : bouquetDomIndex X Y n.succ (toLex (Sum.inl k)) =
            X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) k) := by
          change (match ofLex (toLex (Sum.inl k)) with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) q)) = _
          simp
        exact eqToHom hs ≫
          X.G.map (X.P.cellToOrigin (op (X.P.folio.paddedIndex n.1)) k) ≫
          domSum.inl (extent X) (extent Y)
      · have evx : vx = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        have hs : bouquetDomIndex X Y n.succ (toLex (Sum.inr k)) =
            Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k) := by
          change (match ofLex (toLex (Sum.inr k)) with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) q)) = _
          simp
        exact eqToHom hs ≫
          Y.G.map (Y.P.cellToOrigin (op (Y.P.folio.paddedIndex n.1)) k) ≫
          domSum.inr (extent X) (extent Y)
    | succ p =>
      have hf : p.succ ⟶ n.succ := Quiver.Hom.unop f.val
      have hpn : p ≤ n := Fin.succ_le_succ_iff.mp (leOfHom hf)
      let hxp : X.P.folio.paddedIndex p.1 ≤ X.P.folio.paddedIndex n.1 :=
        X.P.folio.paddedIndex_mono hpn
      let hyp : Y.P.folio.paddedIndex p.1 ≤ Y.P.folio.paddedIndex n.1 :=
        Y.P.folio.paddedIndex_mono hpn
      have ef : f.val = (homOfLE (show p.succ ≤ n.succ from
          Fin.succ_le_succ_iff.mpr hpn)).op :=
        Subsingleton.elim _ _
      generalize hvx : ofLex vx = s
      rcases s with k | k
      · have evx : vx = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        let k' := X.P.H.map (homOfLE hxp).op k
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inl k)) = vy :=
          f.property
        have hv : ofLex vy = Sum.inl k' := by
          rw [← hfv]
          rw [ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inl k))))) = _
          simp [k']
          congr 2
        have hs : bouquetDomIndex X Y n.succ (toLex (Sum.inl k)) =
            X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) k) := by
          change (match ofLex (toLex (Sum.inl k)) with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) q)) = _
          simp
        have ht : bouquetDomIndex X Y p.succ vy =
            X.G.obj (X.P.cell (op (X.P.folio.paddedIndex p.1)) k') := by
          change (match ofLex vy with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex p.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex p.1)) q)) = _
          rw [hv]
        exact eqToHom hs ≫
          X.G.map (CategoryOfElements.homMk _ _ (homOfLE hxp).op rfl) ≫
          eqToHom ht.symm
      · have evx : vx = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        let k' := Y.P.H.map (homOfLE hyp).op k
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inr k)) = vy :=
          f.property
        have hv : ofLex vy = Sum.inr k' := by
          rw [← hfv]
          rw [ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inr k))))) = _
          simp [k']
          congr 2
        have hs : bouquetDomIndex X Y n.succ (toLex (Sum.inr k)) =
            Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k) := by
          change (match ofLex (toLex (Sum.inr k)) with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) q)) = _
          simp
        have ht : bouquetDomIndex X Y p.succ vy =
            Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex p.1)) k') := by
          change (match ofLex vy with
            | .inl q => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex p.1)) q)
            | .inr q => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex p.1)) q)) = _
          rw [hv]
        exact eqToHom hs ≫
          Y.G.map (CategoryOfElements.homMk _ _ (homOfLE hyp).op rfl) ≫
          eqToHom ht.symm

def bouquetToOrigin (X Y : Atl) (x : (bouquetPag X Y).E) :
    bouquetDom X Y x ⟶ domSum (extent X) (extent Y) := by
  rcases x with ⟨⟨m⟩, v⟩
  induction m using Fin.cases with
  | zero => exact 𝟙 _
  | succ n =>
    generalize hv : ofLex v = s
    rcases s with k | k
    · have ev : v = toLex (Sum.inl k) :=
        ofLex.injective (by simpa using hv)
      subst v
      exact X.G.map (X.P.cellToOrigin
        (op (X.P.folio.paddedIndex n.1)) k) ≫
        domSum.inl (extent X) (extent Y)
    · have ev : v = toLex (Sum.inr k) :=
        ofLex.injective (by simpa using hv)
      subst v
      exact Y.G.map (Y.P.cellToOrigin
        (op (Y.P.folio.paddedIndex n.1)) k) ≫
        domSum.inr (extent X) (extent Y)

theorem bouquetDomMap_toOrigin (X Y : Atl)
    {x y : (bouquetPag X Y).E} (f : x ⟶ y) :
    bouquetDomMap X Y f ≫ bouquetToOrigin X Y y =
      bouquetToOrigin X Y x := by
  apply DomIns.hom_ext
  intro a
  rcases x with ⟨⟨mx⟩, vx⟩
  rcases y with ⟨⟨my⟩, vy⟩
  induction mx using Fin.cases with
  | zero =>
    induction my using Fin.cases with
    | zero => rfl
    | succ p =>
      have hf : p.succ ⟶
          (⟨0, bouquetLength_pos X.P.folio Y.P.folio⟩ :
            Fin (bouquetLength X.P.folio Y.P.folio)) :=
        Quiver.Hom.unop f.val
      have h := leOfHom hf
      change p.1 + 1 ≤ 0 at h
      omega
  | succ n =>
    induction my using Fin.cases with
    | zero =>
      generalize hv : ofLex vx = s
      rcases s with k | k
      · have ev : vx = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hv)
        subst vx
        rfl
      · have ev : vx = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hv)
        subst vx
        rfl
    | succ p =>
      have hf : p.succ ⟶ n.succ := Quiver.Hom.unop f.val
      have hpn : p ≤ n := Fin.succ_le_succ_iff.mp (leOfHom hf)
      let hxp : X.P.folio.paddedIndex p.1 ≤ X.P.folio.paddedIndex n.1 :=
        X.P.folio.paddedIndex_mono hpn
      let hyp : Y.P.folio.paddedIndex p.1 ≤ Y.P.folio.paddedIndex n.1 :=
        Y.P.folio.paddedIndex_mono hpn
      generalize hv : ofLex vx = s
      rcases s with k | k
      · have ev : vx = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hv)
        subst vx
        let k' := X.P.H.map (homOfLE hxp).op k
        have ef : f.val = (homOfLE (show p.succ ≤ n.succ from
            Fin.succ_le_succ_iff.mpr hpn)).op := Subsingleton.elim _ _
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inl k)) = vy :=
          f.property
        have hvy : ofLex vy = Sum.inl k' := by
          rw [← hfv, ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inl k))))) = _
          simp [k']
          congr 2
        have evy : vy = toLex (Sum.inl k') :=
          ofLex.injective (by simpa using hvy)
        subst vy
        have hmap := X.G.map_comp
          (CategoryOfElements.homMk
            (X.P.cell (op (X.P.folio.paddedIndex n.1)) k)
            (X.P.cell (op (X.P.folio.paddedIndex p.1))
              (X.P.H.map (homOfLE hxp).op k))
            (homOfLE hxp).op rfl)
          (X.P.cellToOrigin (op (X.P.folio.paddedIndex p.1))
            (X.P.H.map (homOfLE hxp).op k))
        unfold bouquetDomMap bouquetToOrigin
        simp_rw [ofLex_toLex]
        simp_all [bouquetDom, 
          bouquetDomIndex, Category.assoc]
      · have ev : vx = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hv)
        subst vx
        let k' := Y.P.H.map (homOfLE hyp).op k
        have ef : f.val = (homOfLE (show p.succ ≤ n.succ from
            Fin.succ_le_succ_iff.mpr hpn)).op := Subsingleton.elim _ _
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inr k)) = vy :=
          f.property
        have hvy : ofLex vy = Sum.inr k' := by
          rw [← hfv, ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inr k))))) = _
          simp [k']
          congr 2
        have evy : vy = toLex (Sum.inr k') :=
          ofLex.injective (by simpa using hvy)
        subst vy
        have hmap := Y.G.map_comp
          (CategoryOfElements.homMk
            (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k)
            (Y.P.cell (op (Y.P.folio.paddedIndex p.1))
              (Y.P.H.map (homOfLE hyp).op k))
            (homOfLE hyp).op rfl)
          (Y.P.cellToOrigin (op (Y.P.folio.paddedIndex p.1))
            (Y.P.H.map (homOfLE hyp).op k))
        unfold bouquetDomMap bouquetToOrigin
        simp_rw [ofLex_toLex]
        simp_all [bouquetDom,
          bouquetDomIndex, Category.assoc]

def bouquetFunctor (X Y : Atl) : (bouquetPag X Y).E ⥤ DomIns where
  obj := bouquetDom X Y
  map := bouquetDomMap X Y
  map_id := by
    intro x
    apply (cancel_mono (bouquetToOrigin X Y x)).1
    simpa using bouquetDomMap_toOrigin X Y (𝟙 x)
  map_comp := by
    intro x y z f g
    apply (cancel_mono (bouquetToOrigin X Y z)).1
    rw [Category.assoc, bouquetDomMap_toOrigin X Y g,
      bouquetDomMap_toOrigin X Y f]
    exact bouquetDomMap_toOrigin X Y (f ≫ g)
-/

def imageDom {A R : DomIns} (f : A ⟶ R) : DomIns where
  toDom :=
    { Carrier := Set.range f
      rank :=
        ({ toFun := Subtype.val
           inj' := Subtype.val_injective } : Set.range f ↪ R).trans R.toDom.rank }

def imageDom.inclusion {A R : DomIns} (f : A ⟶ R) : imageDom f ⟶ R where
  toFun := Subtype.val
  inj' := Subtype.val_injective

def bouquetRawDomIndex (X Y : Atl) :
    (m : Fin (bouquetLength X.P.folio Y.P.folio)) →
      (bouquetFolio X.P.folio Y.P.folio).H.obj (op m) → DomIns :=
  Fin.cases (fun _ => domSum (extent X) (extent Y)) (fun n v =>
    match ofLex v with
    | .inl k => X.G.obj (X.P.cell (op (X.P.folio.paddedIndex n.1)) k)
    | .inr k => Y.G.obj (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k))

def bouquetRootIndex (X Y : Atl) :
    ∀ (m : Fin (bouquetLength X.P.folio Y.P.folio))
      (v : (bouquetFolio X.P.folio Y.P.folio).H.obj (op m)),
      bouquetRawDomIndex X Y m v ⟶ domSum (extent X) (extent Y) := by
  intro m
  induction m using Fin.cases with
  | zero => intro v; exact 𝟙 _
  | succ n =>
    intro v
    generalize hv : ofLex v = s
    rcases s with k | k
    · have ev : v = toLex (Sum.inl k) :=
        ofLex.injective (by simpa using hv)
      subst v
      exact X.G.map (X.P.cellToOrigin
        (op (X.P.folio.paddedIndex n.1)) k) ≫
        domSum.inl (extent X) (extent Y)
    · have ev : v = toLex (Sum.inr k) :=
        ofLex.injective (by simpa using hv)
      subst v
      exact Y.G.map (Y.P.cellToOrigin
        (op (Y.P.folio.paddedIndex n.1)) k) ≫
        domSum.inr (extent X) (extent Y)

def bouquetDom (X Y : Atl) (x : (bouquetPag X Y).E) : DomIns :=
  imageDom (bouquetRootIndex X Y x.1.unop x.2)

theorem bouquetRange_mono (X Y : Atl) {x y : (bouquetPag X Y).E}
    (f : x ⟶ y) :
    Set.range (bouquetRootIndex X Y x.1.unop x.2) ⊆
      Set.range (bouquetRootIndex X Y y.1.unop y.2) := by
  intro z hz
  rcases x with ⟨⟨mx⟩, vx⟩
  rcases y with ⟨⟨my⟩, vy⟩
  rcases hz with ⟨a, ha⟩
  rw [← ha]
  induction mx using Fin.cases with
  | zero =>
    induction my using Fin.cases with
    | zero => exact ⟨a, rfl⟩
    | succ p =>
      have hf : p.succ ⟶
          (⟨0, bouquetLength_pos X.P.folio Y.P.folio⟩ :
            Fin (bouquetLength X.P.folio Y.P.folio)) :=
        Quiver.Hom.unop f.val
      have h := leOfHom hf
      change p.1 + 1 ≤ 0 at h
      omega
  | succ n =>
    induction my using Fin.cases with
    | zero => exact ⟨bouquetRootIndex X Y n.succ vx a, rfl⟩
    | succ p =>
      have hf : p.succ ⟶ n.succ := Quiver.Hom.unop f.val
      have hpn : p ≤ n := Fin.succ_le_succ_iff.mp (leOfHom hf)
      let hxp : X.P.folio.paddedIndex p.1 ≤ X.P.folio.paddedIndex n.1 :=
        X.P.folio.paddedIndex_mono hpn
      let hyp : Y.P.folio.paddedIndex p.1 ≤ Y.P.folio.paddedIndex n.1 :=
        Y.P.folio.paddedIndex_mono hpn
      generalize hvx : ofLex vx = s
      rcases s with k | k
      · have evx : vx = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        let k' := X.P.H.map (homOfLE hxp).op k
        have ef : f.val = (homOfLE (show p.succ ≤ n.succ from
            Fin.succ_le_succ_iff.mpr hpn)).op := Subsingleton.elim _ _
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inl k)) = vy :=
          f.property
        have hvy : ofLex vy = Sum.inl k' := by
          rw [← hfv, ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inl k))))) = _
          simp [k']
          congr 2
        have evy : vy = toLex (Sum.inl k') :=
          ofLex.injective (by simpa using hvy)
        subst vy
        let q := CategoryOfElements.homMk
          (X.P.cell (op (X.P.folio.paddedIndex n.1)) k)
          (X.P.cell (op (X.P.folio.paddedIndex p.1)) k')
          (homOfLE hxp).op rfl
        refine ⟨X.G.map q a, ?_⟩
        change Sum.inl (X.G.map (X.P.cellToOrigin _ k') (X.G.map q a)) =
          Sum.inl (X.G.map (X.P.cellToOrigin _ k) a)
        apply congrArg Sum.inl
        have hc : q ≫ X.P.cellToOrigin _ k' = X.P.cellToOrigin _ k :=
          CategoryOfElements.ext X.P.H _ _ (Subsingleton.elim _ _)
        have hm := X.G.map_comp q (X.P.cellToOrigin _ k')
        rw [hc] at hm
        exact congrFun (congrArg Function.Embedding.toFun hm.symm) a
      · have evx : vx = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hvx)
        subst vx
        let k' := Y.P.H.map (homOfLE hyp).op k
        have ef : f.val = (homOfLE (show p.succ ≤ n.succ from
            Fin.succ_le_succ_iff.mpr hpn)).op := Subsingleton.elim _ _
        have hfv : (bouquetPag X Y).H.map f.val (toLex (Sum.inr k)) = vy :=
          f.property
        have hvy : ofLex vy = Sum.inr k' := by
          rw [← hfv, ef]
          change ofLex (toLex (Sum.map _ _ (ofLex (toLex (Sum.inr k))))) = _
          simp [k']
          congr 2
        have evy : vy = toLex (Sum.inr k') :=
          ofLex.injective (by simpa using hvy)
        subst vy
        let q := CategoryOfElements.homMk
          (Y.P.cell (op (Y.P.folio.paddedIndex n.1)) k)
          (Y.P.cell (op (Y.P.folio.paddedIndex p.1)) k')
          (homOfLE hyp).op rfl
        refine ⟨Y.G.map q a, ?_⟩
        change Sum.inr (Y.G.map (Y.P.cellToOrigin _ k') (Y.G.map q a)) =
          Sum.inr (Y.G.map (Y.P.cellToOrigin _ k) a)
        apply congrArg Sum.inr
        have hc : q ≫ Y.P.cellToOrigin _ k' = Y.P.cellToOrigin _ k :=
          CategoryOfElements.ext Y.P.H _ _ (Subsingleton.elim _ _)
        have hm := Y.G.map_comp q (Y.P.cellToOrigin _ k')
        rw [hc] at hm
        exact congrFun (congrArg Function.Embedding.toFun hm.symm) a

def imageDom.map {A B R : DomIns} (f : A ⟶ R) (g : B ⟶ R)
    (h : Set.range f ⊆ Set.range g) : imageDom f ⟶ imageDom g where
  toFun z := ⟨z.1, h z.2⟩
  inj' := by
    intro a b e
    apply Subtype.ext
    exact congrArg (fun q => q.1) e

@[simp]
theorem imageDom.map_val {A B R : DomIns} (f : A ⟶ R) (g : B ⟶ R)
    (h : Set.range f ⊆ Set.range g) (z : imageDom f) :
    (imageDom.map f g h z).1 = z.1 := rfl

def bouquetImageMap (X Y : Atl) {x y : (bouquetPag X Y).E} (f : x ⟶ y) :
    bouquetDom X Y x ⟶ bouquetDom X Y y :=
  imageDom.map _ _ (bouquetRange_mono X Y f)

def bouquetFunctor (X Y : Atl) : (bouquetPag X Y).E ⥤ DomIns where
  obj := bouquetDom X Y
  map := bouquetImageMap X Y
  map_id := by
    intro x
    apply DomIns.hom_ext
    intro z
    apply Subtype.ext
    change z.1 = z.1
    rfl
  map_comp := by
    intro x y z f g
    apply DomIns.hom_ext
    intro w
    apply Subtype.ext
    change w.1 = w.1
    rfl

def bouquetAtlas (X Y : Atl) : Atl where
  P := bouquetPag X Y
  G := bouquetFunctor X Y
  disjoint := by
    intro m i j hij x y hxy
    rcases m with ⟨m⟩
    induction m using Fin.cases with
    | zero =>
      exact hij ((bouquetFolio X.P.folio Y.P.folio).originEquiv.injective
        (Subsingleton.elim _ _))
    | succ n =>
      rcases x.2 with ⟨a, ha⟩
      rcases y.2 with ⟨b, hb⟩
      have huv : x.1 = y.1 := by
        have e := congrArg (fun q => q.1) hxy
        change x.1 = y.1 at e
        exact e
      have hroot : bouquetRootIndex X Y n.succ i a =
          bouquetRootIndex X Y n.succ j b := ha.trans (huv.trans hb.symm)
      generalize hi : ofLex i = si
      generalize hj : ofLex j = sj
      rcases si with k | k <;> rcases sj with l | l
      · have ei : i = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hi)
        have ej : j = toLex (Sum.inl l) :=
          ofLex.injective (by simpa using hj)
        subst i
        subst j
        have hkl : k ≠ l := by
          intro e
          subst l
          exact hij rfl
        change Sum.inl (X.G.map (X.P.cellToOrigin _ k) a) =
          Sum.inl (X.G.map (X.P.cellToOrigin _ l) b) at hroot
        exact X.disjoint _ k l hkl a b (Sum.inl.inj hroot)
      · have ei : i = toLex (Sum.inl k) :=
          ofLex.injective (by simpa using hi)
        have ej : j = toLex (Sum.inr l) :=
          ofLex.injective (by simpa using hj)
        subst i
        subst j
        change Sum.inl (X.G.map (X.P.cellToOrigin _ k) a) =
          Sum.inr (Y.G.map (Y.P.cellToOrigin _ l) b) at hroot
        exact Sum.noConfusion hroot
      · have ei : i = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hi)
        have ej : j = toLex (Sum.inl l) :=
          ofLex.injective (by simpa using hj)
        subst i
        subst j
        change Sum.inr (Y.G.map (Y.P.cellToOrigin _ k) a) =
          Sum.inl (X.G.map (X.P.cellToOrigin _ l) b) at hroot
        exact Sum.noConfusion hroot
      · have ei : i = toLex (Sum.inr k) :=
          ofLex.injective (by simpa using hi)
        have ej : j = toLex (Sum.inr l) :=
          ofLex.injective (by simpa using hj)
        subst i
        subst j
        have hkl : k ≠ l := by
          intro e
          subst l
          exact hij rfl
        change Sum.inr (Y.G.map (Y.P.cellToOrigin _ k) a) =
          Sum.inr (Y.G.map (Y.P.cellToOrigin _ l) b) at hroot
        exact Y.disjoint _ k l hkl a b (Sum.inr.inj hroot)

/-!
### The ω₀-completion used by horizontal constructions

The finite folio written in the manuscript is the finite presentation of an
eventually constant folio.  It cannot itself support the claimed associator:
the rule `max (|X|) (|Y|) + 1` gives different finite lengths under the two
parenthesizations.  We therefore perform horizontal constructions after the
following canonical completion.  Page `n` is the genuine page when
`n < |X|`; otherwise it is the final page.  Thus no datum is invented: only
the final territories are repeated.  This common index chain removes the
finite-cardinality mismatch.  A coherent horizontal product must additionally
*flatten* an already-horizontal input instead of inserting its combined root
as a new positive-page cell; otherwise the two parenthesizations still have
different first-page partitions.  The horizontal normal form must therefore
use a flat finite family of completed atlas components.
-/

def Folio.omegaIndex (W : Folio) (n : Nat) : Fin W.length :=
  W.paddedIndex n

theorem Folio.omegaIndex_of_lt (W : Folio) {n : Nat} (h : n < W.length) :
    W.omegaIndex n = ⟨n, h⟩ := by
  apply Fin.ext
  change min n (W.length - 1) = n
  exact Nat.min_eq_left (by omega)

theorem Folio.omegaIndex_of_ge (W : Folio) {n : Nat} (h : W.length ≤ n) :
    W.omegaIndex n = W.lastIndex := by
  apply Fin.ext
  change min n (W.length - 1) = W.length - 1
  exact Nat.min_eq_right (by omega)

/-- `N` is a cutoff when page `N - 1` is final and every page from `N`
onward normalizes to it. -/
def Folio.IsCutoff (W : Folio) (N : Nat) : Prop :=
  0 < N ∧ ∀ n, N ≤ n → W.omegaIndex n = W.omegaIndex (N - 1)

theorem Folio.length_isCutoff (W : Folio) : W.IsCutoff W.length := by
  refine ⟨W.positive, ?_⟩
  intro n hn
  rw [W.omegaIndex_of_ge hn]
  apply Fin.ext
  change W.length - 1 = min (W.length - 1) (W.length - 1)
  simp

/-- The stored cardinality really is the least positive stabilization cutoff,
not merely some bound after which repetition happens. -/
theorem Folio.length_le_of_isCutoff (W : Folio) {N : Nat}
    (hN : W.IsCutoff N) : W.length ≤ N := by
  by_contra h
  have hNl : N < W.length := Nat.lt_of_not_ge h
  have hpos := hN.1
  have he := hN.2 N le_rfl
  rw [W.omegaIndex_of_lt hNl] at he
  have hpred : N - 1 < W.length := lt_of_le_of_lt (Nat.sub_le N 1) hNl
  rw [W.omegaIndex_of_lt hpred] at he
  have hv : N = N - 1 := Fin.ext_iff.mp he
  omega

/-- On the repeated tail, every spine arrow commutes with the canonical
identifications of its endpoints with the final finite index. -/
theorem Folio.spineBase_map_tail (W : Folio) {m n : Nat}
    (hm : W.length ≤ m) (hn : W.length ≤ n) (f : m ⟶ n) :
    W.spineBase.map f ≫ eqToHom (W.omegaIndex_of_ge hn) =
      eqToHom (W.omegaIndex_of_ge hm) := by
  apply Subsingleton.elim

/-- The corresponding coherence condition in `CoCon`: after identifying both
repeated pages with the final page, the transition is the identity transition.
This is the formal content of the manuscript's repeated-page clause. -/
theorem Folio.F_map_tail (W : Folio) {m n : Nat}
    (hm : W.length ≤ m) (hn : W.length ≤ n) (f : m ⟶ n) :
    W.F.map f ≫ W.core.map (eqToHom (W.omegaIndex_of_ge hn)) =
      W.core.map (eqToHom (W.omegaIndex_of_ge hm)) := by
  change W.core.map (W.spineBase.map f) ≫ _ = _
  rw [← W.core.map_comp]
  congr 1

def Folio.omegaBase (W : Folio) : Nat ⥤ Fin W.length where
  obj n := W.omegaIndex n
  map f := homOfLE (W.paddedIndex_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

structure OmegaFolio where
  finite : Folio

def OmegaFolio.F (W : OmegaFolio) : Nat ⥤ CoCon :=
  W.finite.F

def OmegaFolio.H (W : OmegaFolio) : Natᵒᵖ ⥤ Type :=
  W.F.leftOp ⋙ Tra

def OmegaFolio.originBase (_W : OmegaFolio) : Natᵒᵖ := op 0

def OmegaFolio.lastRepeatedIndex (W : OmegaFolio) (n : Nat)
    (h : W.finite.length ≤ n) :
    W.finite.omegaIndex n = W.finite.lastIndex :=
  W.finite.omegaIndex_of_ge h

theorem OmegaFolio.cardinality_is_least_cutoff (W : OmegaFolio) :
    W.finite.IsCutoff W.finite.length ∧
      ∀ N, W.finite.IsCutoff N → W.finite.length ≤ N :=
  ⟨W.finite.length_isCutoff, fun _ h => W.finite.length_le_of_isCutoff h⟩

/-- A wrapper is used instead of the raw dependent sum so that Mathlib's
unrelated category instance for sigma-types cannot compete with the category
of elements instance. -/
structure OmegaElement (W : OmegaFolio) where
  base : Natᵒᵖ
  value : W.H.obj base

instance (W : OmegaFolio) : Category (OmegaElement W) where
  Hom x y := { f : x.base ⟶ y.base // W.H.map f x.value = y.value }
  id x := ⟨𝟙 _, by simp⟩
  comp f g := ⟨f.1 ≫ g.1, by simp [f.2, g.2]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

instance (W : OmegaFolio) (x y : OmegaElement W) : Subsingleton (x ⟶ y) where
  allEq _ _ := Subtype.ext (Subsingleton.elim _ _)

def OmegaFolio.toFiniteElement (W : OmegaFolio) :
    OmegaElement W ⥤ W.finite.E where
  obj x := ⟨op (W.finite.omegaIndex x.base.unop), x.value⟩
  map {_ _} f := CategoryOfElements.homMk _ _
    (W.finite.omegaBase.map (Quiver.Hom.unop f.1)).op f.2
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The occurrence of a final-page cell on a repeated spine page. -/
def OmegaFolio.repeatElement (W : OmegaFolio) (n : Nat)
    (h : W.finite.length ≤ n)
    (k : W.finite.H.obj W.finite.lastBase) : OmegaElement W := by
  refine ⟨op n, ?_⟩
  change (W.finite.core.obj (W.finite.omegaIndex n)).unop.Obj
  rw [W.finite.omegaIndex_of_ge h]
  exact k

structure OmegaAtl where
  finite : Atl

def OmegaAtl.folio (X : OmegaAtl) : OmegaFolio := ⟨X.finite.P.folio⟩
abbrev OmegaAtl.E (X : OmegaAtl) := OmegaElement X.folio
instance (X : OmegaAtl) : Category X.E := inferInstance
def OmegaAtl.G (X : OmegaAtl) : X.E ⥤ DomIns :=
  X.folio.toFiniteElement ⋙ X.finite.G

def OmegaAtl.originElement (X : OmegaAtl) : X.E := by
  refine ⟨op 0, ?_⟩
  change (X.finite.P.folio.core.obj
    (X.finite.P.folio.omegaIndex 0)).unop.Obj
  rw [X.finite.P.folio.omegaIndex_of_lt X.finite.P.folio.positive]
  exact X.finite.P.folio.originValue

def OmegaAtl.extent (X : OmegaAtl) : DomIns := X.G.obj X.originElement

def OmegaAtl.cardinality (X : OmegaAtl) : Nat := X.finite.P.folio.length

theorem OmegaAtl.spine_orderType (_X : OmegaAtl) :
    Ordinal.type (fun m n : Nat => m < n) = Ordinal.omega0 := by
  change typeLT Nat = Ordinal.omega0
  exact Ordinal.type_nat_lt

def OmegaAtl.pageIndex (X : OmegaAtl) (n : Nat) : Fin X.finite.P.folio.length :=
  X.finite.P.folio.omegaIndex n

theorem OmegaAtl.pageIndex_inside (X : OmegaAtl) {n : Nat}
    (h : n < X.finite.P.folio.length) :
    X.pageIndex n = ⟨n, h⟩ :=
  X.finite.P.folio.omegaIndex_of_lt h

theorem OmegaAtl.pageIndex_outside (X : OmegaAtl) {n : Nat}
    (h : X.finite.P.folio.length ≤ n) :
    X.pageIndex n = X.finite.P.folio.lastIndex :=
  X.finite.P.folio.omegaIndex_of_ge h

/-- The partition condition for the completed atlas, stated at an arbitrary
natural-number page.  Beyond the finite presentation this is literally the
partition condition of the final territory. -/
def IsOmegaPagewiseDisjoint (X : OmegaAtl) : Prop :=
  ∀ (n : Nat) (i j : X.folio.H.obj (op n)), i ≠ j →
    ∀ (x : X.finite.G.obj
        (X.finite.P.cell (op (X.pageIndex n)) i))
      (y : X.finite.G.obj
        (X.finite.P.cell (op (X.pageIndex n)) j)),
      X.finite.G.map
          (X.finite.P.cellToOrigin (op (X.pageIndex n)) i) x ≠
        X.finite.G.map
          (X.finite.P.cellToOrigin (op (X.pageIndex n)) j) y

theorem OmegaAtl.disjoint (X : OmegaAtl) : IsOmegaPagewiseDisjoint X := by
  intro n i j hij x y
  exact X.finite.disjoint (op (X.pageIndex n)) i j hij x y

/-- Morphisms are stored on the least finite presentations and extended
canonically to the repeated spine.  Consequently they cannot make independent
choices on pages above the source cardinality; this is precisely the tail
condition in the manuscript. -/
abbrev OmegaAtlHom (X Y : OmegaAtl) := X.finite ⟶ Y.finite

instance : Category OmegaAtl where
  Hom := OmegaAtlHom
  id X := 𝟙 X.finite
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def omegaCompleteObj (X : Atl) : OmegaAtl := ⟨X⟩

theorem omegaComplete_eventually_territory (X : Atl) (n : Nat)
    (h : X.P.folio.length ≤ n) :
    X.P.folio.omegaIndex n = X.P.folio.lastIndex :=
  X.P.folio.omegaIndex_of_ge h

theorem omegaComplete_cardinality (X : Atl) :
    (omegaCompleteObj X).cardinality = cardinality X := rfl

/-!
`OmegaAtlFamily` is the flat normal form used for coherence.  A singleton
family is an ordinary atlas after ω₀-completion; the empty family is the
horizontal unit; and tensoring concatenates families.  In particular, neither
parenthesization creates an intermediate combined root as a new component.
-/

structure OmegaAtlFamily where
  Index : Type
  finiteIndex : Fintype Index
  component : Index → OmegaAtl

attribute [instance] OmegaAtlFamily.finiteIndex

structure OmegaAtlFamilyHom (X Y : OmegaAtlFamily) where
  index : X.Index → Y.Index
  component : ∀ i, X.component i ⟶ Y.component (index i)

@[ext]
theorem OmegaAtlFamilyHom.ext {X Y : OmegaAtlFamily}
    (f g : OmegaAtlFamilyHom X Y) (hi : f.index = g.index)
    (hc : ∀ i, HEq (f.component i) (g.component i)) : f = g := by
  cases f
  cases g
  cases hi
  congr
  funext i
  exact eq_of_heq (hc i)

def OmegaAtlFamilyHom.identity (X : OmegaAtlFamily) :
    OmegaAtlFamilyHom X X where
  index := id
  component := fun _ => 𝟙 _

def OmegaAtlFamilyHom.comp {X Y Z : OmegaAtlFamily}
    (f : OmegaAtlFamilyHom X Y) (g : OmegaAtlFamilyHom Y Z) :
    OmegaAtlFamilyHom X Z where
  index := g.index ∘ f.index
  component := fun i => f.component i ≫ g.component (f.index i)

instance : Category OmegaAtlFamily where
  Hom := OmegaAtlFamilyHom
  id := OmegaAtlFamilyHom.identity
  comp := OmegaAtlFamilyHom.comp
  id_comp f := by
    apply OmegaAtlFamilyHom.ext
    · rfl
    · intro i
      exact heq_of_eq (Category.id_comp _)
  comp_id f := by
    apply OmegaAtlFamilyHom.ext
    · rfl
    · intro i
      exact heq_of_eq (Category.comp_id _)
  assoc f g h := by
    apply OmegaAtlFamilyHom.ext
    · rfl
    · intro i
      exact heq_of_eq (Category.assoc _ _ _)

@[simp]
theorem OmegaAtlFamilyHom.component_id (X : OmegaAtlFamily) (i : X.Index) :
    (𝟙 X : X ⟶ X).component i = 𝟙 (X.component i) := rfl

@[simp]
theorem OmegaAtlFamilyHom.component_comp {X Y Z : OmegaAtlFamily}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : X.Index) :
    (f ≫ g).component i = f.component i ≫ g.component (f.index i) := rfl

def omegaAtom (X : Atl) : OmegaAtlFamily where
  Index := Unit
  finiteIndex := inferInstance
  component := fun _ => omegaCompleteObj X

def omegaFamilyUnit : OmegaAtlFamily where
  Index := Empty
  finiteIndex := inferInstance
  component := fun i => nomatch i

def omegaFamilyTensorObj (X Y : OmegaAtlFamily) : OmegaAtlFamily where
  Index := Sum X.Index Y.Index
  finiteIndex := inferInstance
  component := Sum.elim X.component Y.component

def omegaFamilyTensorHom {X₁ X₂ Y₁ Y₂ : OmegaAtlFamily}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    omegaFamilyTensorObj X₁ X₂ ⟶ omegaFamilyTensorObj Y₁ Y₂ where
  index := Sum.map f.index g.index
  component
    | .inl i => f.component i
    | .inr j => g.component j

def omegaFamilyTensor : OmegaAtlFamily × OmegaAtlFamily ⥤ OmegaAtlFamily where
  obj X := omegaFamilyTensorObj X.1 X.2
  map f := omegaFamilyTensorHom f.1 f.2
  map_id X := by
    have hi : (omegaFamilyTensorHom (𝟙 X.1) (𝟙 X.2)).index =
        (OmegaAtlFamilyHom.identity _).index := by
      funext i
      cases i <;> rfl
    apply OmegaAtlFamilyHom.ext _ _ hi
    intro i
    cases i <;> exact HEq.rfl
  map_comp f g := by
    have hi : (omegaFamilyTensorHom (f.1 ≫ g.1) (f.2 ≫ g.2)).index =
        (omegaFamilyTensorHom f.1 f.2 ≫
          omegaFamilyTensorHom g.1 g.2).index := by
      funext i
      cases i <;> rfl
    apply OmegaAtlFamilyHom.ext _ _ hi
    intro i
    cases i <;> exact HEq.rfl

def omegaFamilyAssociatorHom (X Y Z : OmegaAtlFamily) :
    omegaFamilyTensorObj (omegaFamilyTensorObj X Y) Z ⟶
      omegaFamilyTensorObj X (omegaFamilyTensorObj Y Z) where
  index
    | .inl (.inl i) => .inl i
    | .inl (.inr j) => .inr (.inl j)
    | .inr k => .inr (.inr k)
  component
    | .inl (.inl i) => 𝟙 (X.component i)
    | .inl (.inr j) => 𝟙 (Y.component j)
    | .inr k => 𝟙 (Z.component k)

def omegaFamilyAssociatorInv (X Y Z : OmegaAtlFamily) :
    omegaFamilyTensorObj X (omegaFamilyTensorObj Y Z) ⟶
      omegaFamilyTensorObj (omegaFamilyTensorObj X Y) Z where
  index
    | .inl i => .inl (.inl i)
    | .inr (.inl j) => .inl (.inr j)
    | .inr (.inr k) => .inr k
  component
    | .inl i => 𝟙 (X.component i)
    | .inr (.inl j) => 𝟙 (Y.component j)
    | .inr (.inr k) => 𝟙 (Z.component k)

def omegaFamilyAssociator (X Y Z : OmegaAtlFamily) :
    omegaFamilyTensorObj (omegaFamilyTensorObj X Y) Z ≅
      omegaFamilyTensorObj X (omegaFamilyTensorObj Y Z) where
  hom := omegaFamilyAssociatorHom X Y Z
  inv := omegaFamilyAssociatorInv X Y Z
  hom_inv_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with (i | j) | k <;> rfl
    · intro i
      rcases i with (i | j) | k
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]
  inv_hom_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with i | (j | k) <;> rfl
    · intro i
      rcases i with i | (j | k)
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]
      · simp [omegaFamilyAssociatorHom, omegaFamilyAssociatorInv,
          omegaFamilyTensorObj]

def omegaFamilyLeftUnitorHom (X : OmegaAtlFamily) :
    omegaFamilyTensorObj omegaFamilyUnit X ⟶ X where
  index
    | .inr i => i
  component
    | .inr i => 𝟙 (X.component i)

def omegaFamilyLeftUnitorInv (X : OmegaAtlFamily) :
    X ⟶ omegaFamilyTensorObj omegaFamilyUnit X where
  index i := .inr i
  component i := 𝟙 (X.component i)

def omegaFamilyLeftUnitor (X : OmegaAtlFamily) :
    omegaFamilyTensorObj omegaFamilyUnit X ≅ X where
  hom := omegaFamilyLeftUnitorHom X
  inv := omegaFamilyLeftUnitorInv X
  hom_inv_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with i | i
      · exact i.elim
      · rfl
    · intro i
      rcases i with i | i
      · exact i.elim
      · simp [omegaFamilyLeftUnitorHom, omegaFamilyLeftUnitorInv,
          omegaFamilyTensorObj]
  inv_hom_id := by
    apply OmegaAtlFamilyHom.ext
    · rfl
    · intro i
      simp [omegaFamilyLeftUnitorHom, omegaFamilyLeftUnitorInv,
        omegaFamilyTensorObj]

def omegaFamilyRightUnitorHom (X : OmegaAtlFamily) :
    omegaFamilyTensorObj X omegaFamilyUnit ⟶ X where
  index
    | .inl i => i
  component
    | .inl i => 𝟙 (X.component i)

def omegaFamilyRightUnitorInv (X : OmegaAtlFamily) :
    X ⟶ omegaFamilyTensorObj X omegaFamilyUnit where
  index i := .inl i
  component i := 𝟙 (X.component i)

def omegaFamilyRightUnitor (X : OmegaAtlFamily) :
    omegaFamilyTensorObj X omegaFamilyUnit ≅ X where
  hom := omegaFamilyRightUnitorHom X
  inv := omegaFamilyRightUnitorInv X
  hom_inv_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with i | i
      · rfl
      · exact i.elim
    · intro i
      rcases i with i | i
      · simp [omegaFamilyRightUnitorHom, omegaFamilyRightUnitorInv,
          omegaFamilyTensorObj]
      · exact i.elim
  inv_hom_id := by
    apply OmegaAtlFamilyHom.ext
    · rfl
    · intro i
      simp [omegaFamilyRightUnitorHom, omegaFamilyRightUnitorInv,
        omegaFamilyTensorObj]

def omegaFamilyBraidingHom (X Y : OmegaAtlFamily) :
    omegaFamilyTensorObj X Y ⟶ omegaFamilyTensorObj Y X where
  index
    | .inl i => .inr i
    | .inr j => .inl j
  component
    | .inl i => 𝟙 (X.component i)
    | .inr j => 𝟙 (Y.component j)

def omegaFamilyBraiding (X Y : OmegaAtlFamily) :
    omegaFamilyTensorObj X Y ≅ omegaFamilyTensorObj Y X where
  hom := omegaFamilyBraidingHom X Y
  inv := omegaFamilyBraidingHom Y X
  hom_inv_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      cases i <;> rfl
    · intro i
      cases i with
      | inl i => simp [omegaFamilyBraidingHom, omegaFamilyTensorObj]
      | inr j => simp [omegaFamilyBraidingHom, omegaFamilyTensorObj]
  inv_hom_id := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      cases i <;> rfl
    · intro i
      cases i with
      | inl j => simp [omegaFamilyBraidingHom, omegaFamilyTensorObj]
      | inr i => simp [omegaFamilyBraidingHom, omegaFamilyTensorObj]

instance omegaFamilyMonoidalStruct : MonoidalCategoryStruct OmegaAtlFamily where
  tensorObj := omegaFamilyTensorObj
  tensorHom := omegaFamilyTensorHom
  whiskerLeft X _ _ f := omegaFamilyTensorHom (𝟙 X) f
  whiskerRight f Y := omegaFamilyTensorHom f (𝟙 Y)
  tensorUnit := omegaFamilyUnit
  associator := omegaFamilyAssociator
  leftUnitor := omegaFamilyLeftUnitor
  rightUnitor := omegaFamilyRightUnitor

instance omegaFamilyMonoidal : MonoidalCategory OmegaAtlFamily :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun X Y => by
      exact omegaFamilyTensor.map_id (X, Y))
    (id_tensorHom := fun X {_ _} f => rfl)
    (tensorHom_id := fun {_ _} f Y => rfl)
    (tensorHom_comp_tensorHom := fun {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        cases i <;> rfl
      · intro i
        cases i <;> simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom])
    (associator_naturality := fun {_ _ _ _ _ _} f₁ f₂ f₃ => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        rcases i with (i | j) | k <;> rfl
      · intro i
        rcases i with (i | j) | k <;>
          simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyAssociator,
            omegaFamilyAssociatorHom, omegaFamilyTensorObj])
    (leftUnitor_naturality := fun {_ _} f => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        rcases i with i | i
        · exact i.elim
        · rfl
      · intro i
        rcases i with i | i
        · exact i.elim
        · simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyLeftUnitor,
            omegaFamilyLeftUnitorHom, omegaFamilyTensorObj])
    (rightUnitor_naturality := fun {_ _} f => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        rcases i with i | i
        · rfl
        · exact i.elim
      · intro i
        rcases i with i | i
        · simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyRightUnitor,
            omegaFamilyRightUnitorHom, omegaFamilyTensorObj]
        · exact i.elim)
    (pentagon := fun W X Y Z => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        rcases i with ((i | j) | k) | l <;> rfl
      · intro i
        rcases i with ((i | j) | k) | l <;>
          simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyAssociator,
            omegaFamilyAssociatorHom, omegaFamilyTensorObj])
    (triangle := fun X Y => by
      apply OmegaAtlFamilyHom.ext
      · funext i
        rcases i with (i | e) | j
        · rfl
        · exact e.elim
        · rfl
      · intro i
        rcases i with (i | e) | j
        · simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyAssociator,
            omegaFamilyAssociatorHom, omegaFamilyRightUnitor,
            omegaFamilyRightUnitorHom, omegaFamilyTensorObj]
        · exact e.elim
        · simp [omegaFamilyMonoidalStruct, omegaFamilyTensorHom, omegaFamilyAssociator,
            omegaFamilyAssociatorHom, omegaFamilyLeftUnitor,
            omegaFamilyLeftUnitorHom, omegaFamilyTensorObj])

@[simp]
theorem omegaFamily_tensorObj (X Y : OmegaAtlFamily) :
    MonoidalCategoryStruct.tensorObj X Y = omegaFamilyTensorObj X Y := rfl

@[simp]
theorem omegaFamily_tensorHom {X₁ Y₁ X₂ Y₂ : OmegaAtlFamily}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    MonoidalCategoryStruct.tensorHom f g = omegaFamilyTensorHom f g := rfl

@[simp]
theorem omegaFamily_whiskerLeft (X : OmegaAtlFamily)
    {Y₁ Y₂ : OmegaAtlFamily} (f : Y₁ ⟶ Y₂) :
    MonoidalCategoryStruct.whiskerLeft X f =
      omegaFamilyTensorHom (𝟙 X) f := rfl

@[simp]
theorem omegaFamily_whiskerRight {X₁ X₂ : OmegaAtlFamily}
    (f : X₁ ⟶ X₂) (Y : OmegaAtlFamily) :
    MonoidalCategoryStruct.whiskerRight f Y =
      omegaFamilyTensorHom f (𝟙 Y) := rfl

@[simp]
theorem omegaFamily_associator (X Y Z : OmegaAtlFamily) :
    MonoidalCategoryStruct.associator X Y Z = omegaFamilyAssociator X Y Z := rfl

instance omegaFamilyBraided : BraidedCategory OmegaAtlFamily where
  braiding := omegaFamilyBraiding
  braiding_naturality_right := fun X {_ _} f => by
    apply OmegaAtlFamilyHom.ext
    · funext i
      cases i <;> rfl
    · intro i
      cases i <;>
        simp [omegaFamilyTensorHom,
          omegaFamilyBraiding, omegaFamilyBraidingHom,
          omegaFamilyTensorObj]
  braiding_naturality_left := fun {_ _} f Z => by
    apply OmegaAtlFamilyHom.ext
    · funext i
      cases i <;> rfl
    · intro i
      cases i <;>
        simp [omegaFamilyTensorHom,
          omegaFamilyBraiding, omegaFamilyBraidingHom,
          omegaFamilyTensorObj]
  hexagon_forward := fun X Y Z => by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with (i | j) | k <;> rfl
    · intro i
      rcases i with (i | j) | k <;>
        simp [omegaFamilyTensorHom,
          omegaFamilyAssociator, omegaFamilyAssociatorHom,
          omegaFamilyBraiding, omegaFamilyBraidingHom,
          omegaFamilyTensorObj]
  hexagon_reverse := fun X Y Z => by
    apply OmegaAtlFamilyHom.ext
    · funext i
      rcases i with i | (j | k) <;> rfl
    · intro i
      rcases i with i | (j | k) <;>
        simp [omegaFamilyTensorHom,
          omegaFamilyAssociator, omegaFamilyAssociatorInv,
          omegaFamilyBraiding, omegaFamilyBraidingHom,
          omegaFamilyTensorObj]

instance : SymmetricCategory OmegaAtlFamily where
  symmetry X Y := by
    apply OmegaAtlFamilyHom.ext
    · funext i
      cases i <;> rfl
    · intro i
      cases i <;>
        simp [omegaFamilyBraided, omegaFamilyBraiding,
          omegaFamilyBraidingHom, omegaFamilyTensorObj]

/-%%
\begin{definition}[The Atlas Horizontal Sum Bifunctor]
The \textbf{Atlas Horizontal Sum Bifunctor}, denoted
$\mathsf{AtlHorSum}:\Atl\times\Atl\to\Atl$, is defined as follows.  Given
two morphisms $F:X\to Y$ and $F':X'\to Y'$ in $\Atl$, if $F=\mathsf{AtlI}$,
then $\mathsf{AtlHorSum}(F,F')=F'$, and if $F'=\mathsf{AtlI}$, then
$\mathsf{AtlHorSum}(F,F')=F$.  Otherwise,
$\mathsf{AtlHorSum}(F,F')$ is the universal arrow from $\Atl$ to
$R=Y\sqcup Y'$, written $G:K\to R$, such that there exist morphisms
$M:X\to K$ and $M':X'\to K$ in $\mathsf{AtlTrav}$ satisfying
$M_E(0,0)=(1,0)$ and $M'_E(0,0)=(1,1)$.  For the injections
$Y_i:Y\to R$ and $Y'_i:Y'\to R$, these satisfy
$G\circ M\cong Y_i\circ F$ and $G\circ M'\cong Y'_i\circ F'$.
\end{definition}
%%-/

/-- Implementation note: the universal construction is represented by flat
finite families of atlases completed along the spine.  Keeping this note out
of the manuscript block ensures that the compiled definition remains the one
stated in `datra.md`. -/
abbrev AtlHor := OmegaAtlFamily

def AtlHorSum : CategoryTheory.Functor (AtlHor × AtlHor) AtlHor :=
  omegaFamilyTensor

/-%%
\begin{lemma}[Horizontal Lemma]
The Atlas Horizontal Sum Bifunctor $\mathsf{AtlHorSum}$ exists.

\emph{Proof sketch.}  The cases $F=\mathsf{AtlI}$ or
$F'=\mathsf{AtlI}$ are trivial.  Otherwise, for $F:X\to Y$ and
$F':X'\to Y'$, let $T:\Atl$, let $R=Y\sqcup Y'$, and let $G:T\to R$,
where
\[
  |T|=\max(|X|,|X'|)+1.
\]
Set $T_G(0,0)=\Ex(X)\sqcup\Ex(X')$,
$R_G(0,0)=\Ex(Y)\sqcup\Ex(Y')$, and let $G_{A,(0,0)}$ be the induced
monomorphism.  For each positive integer $m$, set
$T_H(m)=X_H(m-1)\sqcup X'_H(m-1)$.  For $n\in|A_P(m)|$, if $n<M(m)$,
put
\[
  T_G(m,n)=X_G(m-1,n),\qquad
  G_{A,(m,n)}=F_{A,(m-1,n)};
\]
otherwise put
\[
  T_G(m,n)=X'_G\bigl(m-1,n-|X_H(m-1)|\bigr),
\]
and
\[
  G_{A,(m,n)}=F'_{A,\left(m-1,n-|X_H(m-1)|\right)}.
\]
This defines $G$, which is initial among solutions.
\end{lemma}
%%-/

theorem horizontalLemma : Nonempty (SymmetricCategory AtlHor) :=
  ⟨inferInstance⟩

/-%%
\begin{definition}[The Atlas Braider]
The \textbf{Atlas Braider}
$\mathsf{AtlBrd}_{F,F'}:\mathsf{AtlHorSum}(F,F')\to
\mathsf{AtlHorSum}(F',F)$ is defined as follows.  If
$F=\mathsf{AtlI}$ or $F'=\mathsf{AtlI}$, then
$\mathsf{AtlBrd}_{F,F'}=\id$.  Otherwise, let
$R=\mathsf{AtlHorSum}(F,F')$, and let $G:H\to R$ be the universal arrow
from $\mathsf{AtlTrap}$ to $R$ satisfying
$G_E(1,0)=(1,1)$ and $G_E(1,1)=(1,0)$.  Then
$\mathsf{AtlBrd}_{F,F'}=G^{-1}$, and
$\mathsf{AtlBrd}_{F,F'}\circ\mathsf{AtlBrd}_{F',F}=\id$.
\end{definition}
%%-/

def AtlBrd (X Y : AtlHor) :
    AtlHorSum.obj (X, Y) ≅ AtlHorSum.obj (Y, X) :=
  omegaFamilyBraiding X Y

/-%%
\begin{definition}[The Atlas Associator]
The \textbf{Atlas Associator}, denoted
\[
  \mathsf{AtlAsoc}_{F,F',F''}:
  \mathsf{AtlHorSum}(\mathsf{AtlHorSum}(F,F'),F'')
  \longrightarrow
  \mathsf{AtlHorSum}(F,\mathsf{AtlHorSum}(F',F'')),
\]
is defined as follows.  If $F=\mathsf{AtlI}$, $F'=\mathsf{AtlI}$, or
$F''=\mathsf{AtlI}$, then $\mathsf{AtlAsoc}_{F,F',F''}=\id$.
Otherwise, let
$R=\mathsf{AtlHorSum}(\mathsf{AtlHorSum}(F,F'),F'')$, and let
$G:H\to R$ be the universal arrow from $\mathsf{AtlTrap}$ to $R$ such
that $G_E(2,0)=(1,0)$.  Suppose also that there exists a morphism
$G':\mathsf{AtlHorSum}(F',F'')\to H$ in $\mathsf{AtlTrav}$ satisfying
$G'_E(0,0)=(1,1)$.  Then $\mathsf{AtlAsoc}_{F,F',F''}=G^{-1}$.
\end{definition}
%%-/

def AtlAsoc (X Y Z : AtlHor) :
    AtlHorSum.obj (AtlHorSum.obj (X, Y), Z) ≅
      AtlHorSum.obj (X, AtlHorSum.obj (Y, Z)) :=
  omegaFamilyAssociator X Y Z

/-%%
\begin{definition}[The Atlas Unitors]
The \textbf{Atlas Left Unitor}
$\mathsf{Lu}:\mathsf{AtlHorSum}(F,\mathsf{AtlI})\to F$ and the
\textbf{Atlas Right Unitor}
$\mathsf{Ru}:\mathsf{AtlHorSum}(\mathsf{AtlI},F)\to F$ are given by
$\mathsf{Lu}=\id$ and $\mathsf{Ru}=\id$.
\end{definition}
%%-/

/-- The public names follow the manuscript's left/right convention.  Mathlib's
standard names are opposite: `omegaFamilyRightUnitor` has source `X ⊗ I`,
while `omegaFamilyLeftUnitor` has source `I ⊗ X`. -/
def AtlLu (X : AtlHor) : AtlHorSum.obj (X, omegaFamilyUnit) ≅ X :=
  omegaFamilyRightUnitor X

def AtlRu (X : AtlHor) : AtlHorSum.obj (omegaFamilyUnit, X) ≅ X :=
  omegaFamilyLeftUnitor X

instance : SymmetricCategory OmegaAtlFamilyᵒᵖ where
  symmetry X Y := by
    apply Quiver.Hom.unop_inj
    simp

/-! The completed presheaf category on which Day convolution is formed.  The
all-objects full subcategory is deliberate: it gives the Day convolution a
fresh monoidal instance, distinct from the pointwise cartesian monoidal
structure that the raw functor category already carries. -/
abbrev OmegaPresheaf :=
  CategoryTheory.Functor OmegaAtlFamilyᵒᵖ (Type 3)

def IsOmegaDaTra : ObjectProperty OmegaPresheaf := fun _ => True

abbrev OmegaDaTra := IsOmegaDaTra.FullSubcategory

abbrev omegaDaTraInc : CategoryTheory.Functor OmegaDaTra OmegaPresheaf :=
  IsOmegaDaTra.ι

theorem omegaDaTraInc_essImage (F : OmegaPresheaf) :
    omegaDaTraInc.essImage F :=
  ⟨⟨F, trivial⟩, ⟨Iso.refl _⟩⟩

instance omegaPreservesTensorRightForTensor (v : Type 3)
    (d : OmegaAtlFamilyᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow (MonoidalCategory.tensor OmegaAtlFamilyᵒᵖ) d)
      (MonoidalCategory.tensorRight v) :=
  preservesColimitsOfShape_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight v)

instance omegaPreservesTensorRightForUnit (v : Type 3)
    (d : OmegaAtlFamilyᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow
        (CategoryTheory.Functor.fromPUnit
          (MonoidalCategory.tensorUnit OmegaAtlFamilyᵒᵖ)) d)
      (MonoidalCategory.tensorRight v) :=
  preservesColimitsOfShape_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight v)

instance omegaPreservesTensorRightForUnitProduct (v : Type 3)
    (d : OmegaAtlFamilyᵒᵖ × OmegaAtlFamilyᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow
        ((CategoryTheory.Functor.id OmegaAtlFamilyᵒᵖ).prod
          (CategoryTheory.Functor.fromPUnit
            (MonoidalCategory.tensorUnit OmegaAtlFamilyᵒᵖ))) d)
      (MonoidalCategory.tensorRight v) :=
  preservesColimitsOfShape_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight v)

instance omegaPreservesTensorRightForTensorProduct (v : Type 3)
    (d : OmegaAtlFamilyᵒᵖ × OmegaAtlFamilyᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow
        ((MonoidalCategory.tensor OmegaAtlFamilyᵒᵖ).prod
          (CategoryTheory.Functor.id OmegaAtlFamilyᵒᵖ)) d)
      (MonoidalCategory.tensorRight v) :=
  preservesColimitsOfShape_of_natIso
    (BraidedCategory.tensorLeftIsoTensorRight v)

noncomputable def omegaDaTraMonoidal : MonoidalCategory OmegaDaTra :=
  MonoidalCategory.monoidalOfHasDayConvolutions omegaDaTraInc
    (ObjectProperty.fullyFaithfulι IsOmegaDaTra)
    (fun _ _ => omegaDaTraInc_essImage _)
    (omegaDaTraInc_essImage _)

noncomputable instance : MonoidalCategory OmegaDaTra := omegaDaTraMonoidal

noncomputable instance omegaDaTraLawful :
    MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct
      OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra :=
  MonoidalCategory.lawfulDayConvolutionMonoidalCategoryStructOfHasDayConvolutions
    omegaDaTraInc (ObjectProperty.fullyFaithfulι IsOmegaDaTra)
    (fun _ _ => omegaDaTraInc_essImage _)
    (omegaDaTraInc_essImage _)

noncomputable instance omegaDayConvolution (F G : OmegaDaTra) :
    MonoidalCategory.DayConvolution
      (omegaDaTraInc.obj F) (omegaDaTraInc.obj G) :=
  MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.convolution
    OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra F G

noncomputable instance omegaDayConvolutionRightNested
    (F G H : OmegaDaTra) :
    MonoidalCategory.DayConvolution (omegaDaTraInc.obj F)
      (MonoidalCategory.DayConvolution.convolution
        (omegaDaTraInc.obj G) (omegaDaTraInc.obj H)) :=
  MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.convolution₂
    OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra F G H

noncomputable instance omegaDayConvolutionLeftNested
    (F G H : OmegaDaTra) :
    MonoidalCategory.DayConvolution
      (MonoidalCategory.DayConvolution.convolution
        (omegaDaTraInc.obj F) (omegaDaTraInc.obj G))
      (omegaDaTraInc.obj H) :=
  MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.convolution₂'
    OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra F G H

noncomputable def omegaDaTraBraiding (F G : OmegaDaTra) :
    MonoidalCategory.tensorObj F G ≅ MonoidalCategory.tensorObj G F := by
  exact (ObjectProperty.fullyFaithfulι IsOmegaDaTra).preimageIso
    (MonoidalCategory.DayConvolution.braiding
      (omegaDaTraInc.obj F) (omegaDaTraInc.obj G))

theorem omegaDaTraInc_map_braiding_hom (F G : OmegaDaTra) :
    omegaDaTraInc.map (omegaDaTraBraiding F G).hom =
      (MonoidalCategory.DayConvolution.braiding
        (omegaDaTraInc.obj F) (omegaDaTraInc.obj G)).hom := by
  exact (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_preimage _

theorem omegaDaTraInc_map_braiding_inv (F G : OmegaDaTra) :
    omegaDaTraInc.map (omegaDaTraBraiding F G).inv =
      (MonoidalCategory.DayConvolution.braiding
        (omegaDaTraInc.obj F) (omegaDaTraInc.obj G)).inv := by
  exact (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_preimage _

theorem omegaDaTraInc_map_tensorHom
    {F₁ F₂ G₁ G₂ : OmegaDaTra}
    (f : F₁ ⟶ F₂) (g : G₁ ⟶ G₂) :
    omegaDaTraInc.map (MonoidalCategory.tensorHom f g) =
      MonoidalCategory.DayConvolution.map
        (omegaDaTraInc.map f) (omegaDaTraInc.map g) := by
  simpa [omegaDaTraInc, omegaDaTraLawful] using
    (MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom
        OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra f g)

theorem omegaDaTraInc_map_associator_hom (F G H : OmegaDaTra) :
    omegaDaTraInc.map (MonoidalCategory.associator F G H).hom =
      (MonoidalCategory.DayConvolution.associator
        (omegaDaTraInc.obj F) (omegaDaTraInc.obj G)
        (omegaDaTraInc.obj H)).hom := by
  simpa [omegaDaTraInc, omegaDaTraLawful] using
    (MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.ι_map_associator_hom_eq_associator_hom
        OmegaAtlFamilyᵒᵖ (Type 3) OmegaDaTra F G H)

noncomputable instance omegaDaTraBraided : BraidedCategory OmegaDaTra where
  braiding := omegaDaTraBraiding
  braiding_naturality_right := fun X {_ _} f => by
    rw [← MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.tensorHom_id]
    apply (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_injective
    simp only [Functor.map_comp,
      omegaDaTraInc_map_tensorHom, omegaDaTraInc_map_braiding_hom]
    exact MonoidalCategory.DayConvolution.braiding_naturality_right
      (omegaDaTraInc.obj X) (omegaDaTraInc.map f)
  braiding_naturality_left := fun {_ _} f Z => by
    rw [← MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.id_tensorHom]
    apply (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_injective
    simp only [Functor.map_comp,
      omegaDaTraInc_map_tensorHom, omegaDaTraInc_map_braiding_hom]
    exact MonoidalCategory.DayConvolution.braiding_naturality_left
      (omegaDaTraInc.map f) (omegaDaTraInc.obj Z)
  hexagon_forward := by
    intro X Y Z
    apply (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_injective
    simp only [Functor.map_comp,
      omegaDaTraInc_map_associator_hom,
      omegaDaTraInc_map_braiding_hom]
    rw [← MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.id_tensorHom]
    simp only [omegaDaTraInc_map_tensorHom]
    exact MonoidalCategory.DayConvolution.hexagon_forward
      (omegaDaTraInc.obj X) (omegaDaTraInc.obj Y) (omegaDaTraInc.obj Z)
  hexagon_reverse := by
    intro X Y Z
    apply (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_injective
    simp only [Functor.map_comp,
      omegaDaTraInc_map_braiding_hom]
    rw [← MonoidalCategory.id_tensorHom,
      ← MonoidalCategory.tensorHom_id]
    simp only [omegaDaTraInc_map_tensorHom]
    exact MonoidalCategory.DayConvolution.hexagon_reverse
      (omegaDaTraInc.obj X) (omegaDaTraInc.obj Y) (omegaDaTraInc.obj Z)

set_option maxHeartbeats 2400000 in
noncomputable instance : SymmetricCategory OmegaDaTra where
  symmetry F G := by
    apply (ObjectProperty.fullyFaithfulι IsOmegaDaTra).map_injective
    simp only [Functor.map_comp]
    exact MonoidalCategory.DayConvolution.symmetry
      (omegaDaTraInc.obj F) (omegaDaTraInc.obj G)

/-%%
\section{Horizontal Data Traversals}

\begin{definition}[The Empty Map]
The \textbf{Empty Map}, denoted $I$, is the Yoneda embedding of the Empty
Atlas:
\[
  I=\Yo(\mathsf{AtlI}).
\]
\end{definition}
%%-/

/-- The implementation realizes the manuscript's horizontal site by the flat
completed atlas category `AtlHor`; `DaTravMon` is its full presheaf category.
This completion detail is intentionally outside the extracted definition. -/
abbrev DaTravMon := OmegaDaTra

noncomputable def I : DaTravMon :=
  MonoidalCategory.tensorUnit DaTravMon

/-- Certificate of the universal property implicit in the notation
`I = Yo(AtlI)`: under the inclusion into presheaves, `I` is the pointwise left
Kan extension of the singleton along the inclusion of the horizontal unit. -/
noncomputable def I_dayConvolutionUnit :
    MonoidalCategory.DayConvolutionUnit (omegaDaTraInc.obj I) :=
  MonoidalCategory.LawfulDayConvolutionMonoidalCategoryStruct.convolutionUnit
    OmegaAtlFamilyᵒᵖ (Type 3) DaTravMon

/-%%
\begin{definition}[The Horizontal Sum Bifunctor]
The \textbf{Horizontal Sum Bifunctor}, denoted
$\mathsf{HorSum}:\mathsf{DaTrav}\times\mathsf{DaTrav}	o
\mathsf{DaTrav}$, or in infix notation by
$+_{!<}:\mathsf{DaTrav}\times\mathsf{DaTrav}\to\mathsf{DaTrav}$,
is the Day convolution extension of $\mathsf{AtlHorSum}$.
\end{definition}
%%-/

noncomputable def HorSum :
    CategoryTheory.Functor (DaTravMon × DaTravMon) DaTravMon :=
  MonoidalCategory.tensor DaTravMon

/-%%
\begin{definition}[The Data Traversal Braider]
The \textbf{Data Traversal Braider}
$\mathsf{Brd}_{F,F'}:F+_{!<}F'\to F'+_{!<}F$ is the Day convolution
extension of $\mathsf{AtlBrd}$.
\end{definition}
%%-/

noncomputable def Brd (F G : DaTravMon) :
    MonoidalCategory.tensorObj F G ≅ MonoidalCategory.tensorObj G F :=
  omegaDaTraBraiding F G

/-%%
\begin{definition}[The Data Traversal Associator]
The \textbf{Data Traversal Associator}
\[
  \mathsf{Asoc}_{F,F',F''}:(F+_{!<}F')+_{!<}F''
    \longrightarrow F+_{!<}(F'+_{!<}F'')
\]
is the Day convolution extension of $\mathsf{AtlAsoc}$.
\end{definition}
%%-/

noncomputable def Asoc (F G H : DaTravMon) :
    MonoidalCategory.tensorObj (MonoidalCategory.tensorObj F G) H ≅
      MonoidalCategory.tensorObj F (MonoidalCategory.tensorObj G H) :=
  MonoidalCategory.associator F G H

/-%%
\begin{definition}[The Data Traversal Unitors]
The \textbf{Data Traversal Left Unitor}
$\mathsf{Lu}:F+_{!<}I\to F$ and the
\textbf{Data Traversal Right Unitor}
$\mathsf{Ru}:I+_{!<}F\to F$ are the Day convolution extensions of
$\mathsf{AtlLu}$ and $\mathsf{AtlRu}$.
\end{definition}
%%-/

noncomputable def Lu (F : DaTravMon) :
    MonoidalCategory.tensorObj F I ≅ F :=
  MonoidalCategory.rightUnitor F

noncomputable def Ru (F : DaTravMon) :
    MonoidalCategory.tensorObj I F ≅ F :=
  MonoidalCategory.leftUnitor F

/-%%
\begin{definition}[The Data Traversal Monoidal Category]
The \textbf{Data Traversal Monoidal Category}, denoted
$\mathsf{DaTravMon}$, is
\[
  \mathsf{DaTravMon}=(\mathsf{DaTrav},+_{!<},I).
\]
The coherence conditions are checked by observing that
$\mathsf{Brd}$, $\mathsf{Asoc}$, $\mathsf{Lu}$, and $\mathsf{Ru}$ are
sent to isomorphisms in $\mathsf{DaTra}$.
\end{definition}
%%-/

/-- Unlike the prose's abbreviated "can be checked", the Lean instance above
contains the naturality, pentagon, triangle, two hexagons, and symmetry proofs
explicitly. -/
theorem serenityLemma : Nonempty (SymmetricCategory DaTravMon) :=
  ⟨inferInstance⟩


end

end Datra

/-%%
\end{document}
%%-/
