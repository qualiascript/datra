import Mathlib

/-%%
\documentclass[11pt]{article}
\usepackage[a4paper,margin=1in]{geometry}
\usepackage{microtype}
\usepackage{mathtools,amssymb,amsthm}
\usepackage{tikz-cd}
\usepackage[hidelinks]{hyperref}

\title{DaTra: Data Transformation Semantics As a Symmetrical Monoidal
Category on a Paginated Topos}
\author{\texttt{@qualiascript} \and ChatGPT}
\date{}

\theoremstyle{definition}
\newtheorem{definition}{Definition}[section]
\theoremstyle{plain}
\newtheorem{lemma}[definition]{Lemma}

\newcommand{\Set}{\mathsf{Set}}
\newcommand{\id}{\operatorname{Id}}
\newcommand{\Hom}{\operatorname{Hom}}
\newcommand{\PSh}{\operatorname{PSh}}

\begin{document}
\maketitle

\section{Dominions}

\begin{definition}[The Category of Dominions]
The \textbf{Category of Dominions}, denoted $\mathsf{Dom}$, has as its objects
sets whose cardinality is at most $\omega_0$ (i.e. the smallest infinite
ordinal), that is, its objects are sets that have an injection to $\omega_0$,
and as its morphisms set-theoretic functions (i.e. morphisms in $\Set$).
\end{definition}
%%-/

namespace Datra

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open Opposite

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

/-%%
\begin{definition}[The Domanial Embedding Functor]
The \textbf{Domanial Embedding Functor}, denoted
$\mathsf{Emb} : \mathsf{Dom} \to \Set$, sends each dominion to its
corresponding set.
\end{definition}
%%-/

def Emb : Functor Dom (Type 0) where
  obj X := X
  map f := f

/-%%
\section{Domanial Insertions}

\begin{definition}[The Category of Domanial Insertions]
The \textbf{Category of Domanial Insertions}, denoted $\mathsf{DomIns}$, is
the category whose objects are dominions, that is, objects of $\mathsf{Dom}$,
and whose morphisms are monomorphisms in $\mathsf{Dom}$.
\end{definition}
%%-/

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

/-%%
\begin{definition}[The Category of Codomanial Insertions]
The \textbf{Category of Codomanial Insertions}, denoted $\mathsf{CoDomIns}$,
is the opposite category of $\mathsf{DomIns}$, that is,
\[
  \mathsf{CoDomIns} = \mathsf{DomIns}^{\mathrm{op}}.
\]
\end{definition}
%%-/

abbrev CoDomIns := Opposite DomIns

/-%%
\section{Domanial Consolidations}

\begin{definition}[The Category of Domanial Consolidations]
The \textbf{Category of Domanial Consolidations}, denoted $\mathsf{DomCon}$,
is the category whose objects are dominions and morphisms are order-preserving
epimorphisms in $\mathsf{Dom}$. More specifically, a morphism
$F : A \to B$ in $\mathsf{DomCon}$ has the property that for any $x,y : A$,
if $\lvert x\rvert < \lvert y\rvert$, then
$\lvert F(x)\rvert \leq \lvert F(y)\rvert$.
\end{definition}
%%-/

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

/-%%
\begin{definition}[The Category of Codomanial Consolidations]
The \textbf{Category of Codomanial Consolidations}, denoted
$\mathsf{CoDomCon}$, is the opposite category of $\mathsf{DomCon}$, that is,
\[
  \mathsf{CoDomCon} = \mathsf{DomCon}^{\mathrm{op}}.
\]
\end{definition}
%%-/

abbrev CoDomCon := Opposite DomCon

/-%%
\section{Chains}

\begin{definition}[Chain]
A \textbf{Chain} is a totally ordered thin category, taken skeletally.
\end{definition}
%%-/

structure Chain where
  Carrier : Type 0
  order : LinearOrder Carrier

attribute [instance] Chain.order

/-%%
\begin{definition}[Short Chain]
A \textbf{Short Chain} is a chain that is finite, taken skeletally.
\end{definition}
%%-/

structure ShortChain extends Chain where
  finite : Fintype Carrier

attribute [instance] ShortChain.finite

/-%%
\section{Transportation and Folios}

\begin{definition}[The Transportation Functor]
The \textbf{Transportation Functor}, denoted $\mathsf{Tra}$, is of type
$\mathsf{Tra} : \mathsf{DomCon} \to \Set$, and sends each morphism in
$\mathsf{DomCon}$ to its underlying set-theoretic surjection.
\end{definition}
%%-/

def Tra : Functor DomCon (Type 0) where
  obj X := X
  map f := f.toFun

/-%%
\begin{definition}[Folio]
A \textbf{Folio} is a functor
$F : C \to (1 \downarrow \mathsf{CoDomCon})$, where
$1 \downarrow \mathsf{CoDomCon}$ is the coslice category, that preserves the
initial object.
\end{definition}
%%-/

structure Folio where
  length : Nat
  positive : 0 < length
  F : Functor (Fin length) CoDomCon
  originEquiv : Equiv ((F.obj (Fin.mk 0 positive)).unop.toDom.Carrier) PUnit.{0}

def Folio.H (W : Folio) : Functor (Opposite (Fin W.length)) (Type 0) :=
  Functor.comp W.F.leftOp Tra

def Folio.E (W : Folio) : Type 0 := W.H.Elements

instance (W : Folio) : Category.{0} W.E := CategoryTheory.categoryOfElements W.H

/-%%
\section{Paginations}

\begin{definition}[The Category of Paginations]
The \textbf{Category of Paginations}, denoted $\mathsf{Pag}$, is the category
whose objects are pairs $(H,E)$, where
$H = \mathsf{Tra} \circ F^{\mathrm{op}}$,
$F : C \to \mathsf{CoDomCon}$ is a folio,
and $E$ is the category of elements of functor $H$. For any
$W : \mathsf{Pag}$, we denote $W_H$ as the first inclusion and $W_E$ as the
second inclusion. Morphisms in $\mathsf{Pag}$, for $F : X \to Y$ and
$X,Y : \mathsf{Pag}$, are given by functors $T : X_E \to Y_E$, so that the
following diagram commutes:
\[
\begin{tikzcd}[column sep=large,row sep=large]
x=(m,i) \arrow[r,"f"] \arrow[d,"T"']
  & \bigl(n,(X_H(f))(i)\bigr) \arrow[d,"T"] \\
(m',i') \arrow[r,"T(f)"']
  & \bigl(n',(Y_H(T(f)))(i')\bigr).
\end{tikzcd}
\]
\end{definition}
%%-/

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

/-%%
\section{Atlases}

\begin{definition}[The Category of Atlases]
The \textbf{Category of Atlases}, denoted $\mathsf{Atl}$, is the category
whose objects are pairs $(P,G)$, where $P : \mathsf{Pag}$ and $G$ is a functor
$G : P_E \to \mathsf{DomIns}$, or alternatively a presheaf
$G : P_E^{\mathrm{op}} \to \mathsf{CoDomIns}$. For
$X : \mathsf{Atl}$, we denote
$X_P$ the first inclusion, $X_G$ the second inclusion, along with
$X_H = X_{P_H}$ and $X_E = X_{P_E}$. Morphisms in $\mathsf{Atl}$, for
$T : X \to Y$, are pairs $(T_P,T_A)$, where $T_P : X_P \to Y_P$ is a
morphism in $\mathsf{Pag}$ and
$T_A : X_G \Rightarrow Y_G \circ T_E$ is a natural transformation, that is,
the following diagram commutes for all morphisms $f : x \to y$ in $X_E$:
\[
\begin{tikzcd}[column sep=huge,row sep=large]
X_G(x) \arrow[r,"X_G(f)"] \arrow[d,"(T_A)_x"']
  & X_G(y) \arrow[d,"(T_A)_y"] \\
Y_G(T_E(x)) \arrow[r,"Y_G(T_E(f))"']
  & Y_G(T_E(y)).
\end{tikzcd}
\]
\end{definition}
%%-/

structure Atl where
  P : Pag
  G : Functor P.E DomIns

def Atl.H (X : Atl) : Functor (Opposite (Fin X.P.folio.length)) (Type 0) := X.P.H
def Atl.E (X : Atl) : Type 0 := X.P.E

instance (X : Atl) : Category.{0} X.E := CategoryTheory.categoryOfElements X.H

structure AtlHom (X Y : Atl) where
  P : Functor X.E Y.E
  A : NatTrans X.G (Functor.comp P Y.G)

def AtlHom.identity (X : Atl) : AtlHom X X where
  P := Functor.id X.E
  A := NatTrans.id X.G

def AtlHom.comp {X Y Z : Atl} (f : AtlHom X Y) (g : AtlHom Y Z) :
    AtlHom X Z where
  P := Functor.comp f.P g.P
  A := CategoryStruct.comp f.A (whiskerLeft f.P g.A)

@[ext]
theorem AtlHom.ext {X Y : Atl} (f g : AtlHom X Y)
    (hP : f.P = g.P) (hA : HEq f.A g.A) : f = g := by
  cases f
  cases g
  simp_all

instance : Category.{0} Atl where
  Hom := AtlHom
  id := AtlHom.identity
  comp := AtlHom.comp
  id_comp f := by
    apply AtlHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [AtlHom.comp, AtlHom.identity]
  comp_id f := by
    apply AtlHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [AtlHom.comp, AtlHom.identity]
  assoc f g h := by
    apply AtlHom.ext
    rfl
    apply heq_of_eq
    ext x
    simp [AtlHom.comp]

def Folio.originIndex (W : Folio) : Fin W.length := Fin.mk 0 W.positive

def Folio.originBase (W : Folio) : Opposite (Fin W.length) := op W.originIndex

def Folio.originValue (W : Folio) : W.H.obj W.originBase :=
  W.originEquiv.symm PUnit.unit

def Folio.originElement (W : Folio) : W.E := Sigma.mk W.originBase W.originValue

def Folio.lastIndex (W : Folio) : Fin W.length :=
  Fin.mk (W.length - 1) (Nat.sub_lt W.positive (by decide))

def Folio.lastBase (W : Folio) : Opposite (Fin W.length) := op W.lastIndex

/-%%
\begin{definition}[Cardinality of an Atlas]
The \textbf{Cardinality of an Atlas} $A : \mathsf{Atl}$ is the cardinality
of the origin of $A_H : C \to \Set$, that is, the number of objects of the
small chain $C$. It is denoted as $\lvert A\rvert$.
\end{definition}
%%-/

def cardinality (A : Atl) : Nat := A.P.folio.length

/-%%
\begin{definition}[Extent of an Atlas]
The \textbf{Extent of an Atlas} $A : \mathsf{Atl}$ is the value at
$A_G(0,0)$, that exists as folios preserve initial objects. It is denoted as
$\mathsf{Ex}(A)$. Since the objects of $\mathsf{DomIns}$ are dominions,
$\mathsf{Ex}(A) : \mathsf{Dom}$ for any $A : \mathsf{Atl}$.
\end{definition}
%%-/

def extent (A : Atl) : Dom :=
  (A.G.obj A.P.folio.originElement).toDom

/-%%
\begin{definition}[Territory of an Atlas]
The \textbf{Territory of an Atlas} $A : \mathsf{Atl}$ is the indexed
collection of dominions $\mathsf{Ter}(A) : M \to \mathsf{Dom}$, where
$M = A_H(\lvert A\rvert - 1)$, so that
$\mathsf{Ter}(A)(k) = A_G(\lvert A\rvert - 1,k)$.
\end{definition}
%%-/

/-- The type `M` is the last fiber of `A_H`; this is the only typing of the
displayed expression for which `k` indexes objects of the category of
elements. -/
def TerritoryIndex (A : Atl) : Type 0 := A.H.obj A.P.folio.lastBase

def territory (A : Atl) (k : TerritoryIndex A) : Dom :=
  (A.G.obj (Sigma.mk A.P.folio.lastBase k)).toDom

/-%%
\begin{definition}[$n$th Region of an Atlas]
The \textbf{$n$th Region of an Atlas} $A : \mathsf{Atl}$ is the
dominion $\mathsf{Ter}(A)(n)$ for $n : M$, noting that the indexing starts at
$0$.
\end{definition}
%%-/

def region (A : Atl) (n : TerritoryIndex A) : Dom := territory A n

/-%%
\section{Transposals and Traversals}

\begin{definition}[The Category of Atlas Transposals]
The \textbf{Category of Atlas Transposals}, denoted $\mathsf{AtlTrap}$, is the
wide subcategory of $\mathsf{Atl}$ whose morphisms $F : X \to Y$ have the
property that $F_E$ is a faithful functor.
\end{definition}
%%-/

def IsTransposal : MorphismProperty Atl := fun _ _ F => F.P.Faithful

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

abbrev AtlTrap := WideSubcategory IsTransposal

def AtlTrapInc : Functor AtlTrap Atl := wideSubcategoryInclusion IsTransposal

/-%%

\end{document}
%%-/

end Datra
