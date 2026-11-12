import Executable.Folio
import Executable.Trace

namespace Datra.Executable
open CategoryTheory

universe s t

/-- The cell index includes the genuine page, modeling Haskell's phantom object
identity as well as its existential payload. Distinct genuine pages can have
different data families even when their chain and value coincide. Padding
normalization preserves this index literally. -/
structure PageElementCell where
  Carrier : Type
  chain : Chain Carrier
  value : Carrier
  genuinePage : Nat

/-- The owner is a value index; arrows cannot connect different owners.
Validity against a folio is an additional invariant of the public constructors. -/
structure PageElement {Scope : Type s} (owner : Scope) where
  page : Nat
  position : Ordinal
  trace : List Ordinal
  cell : PageElementCell

namespace PageElement
variable {Scope : Type s} {owner : Scope}

/-- Look up the transported position in the stored descending page trace. -/
def positionAtPage (page : Nat) (occurrence : PageElement owner) : Option Ordinal :=
  (occurrence.trace.drop (occurrence.page - page)).head?

/-- The strict comparison reads both traces at the common earliest page. -/
def elementLT (left right : PageElement owner) : Bool :=
  let commonPage := min left.page right.page
  match positionAtPage commonPage left, positionAtPage commonPage right with
  | some a, some b => Ordinal.ordinalLT a b
  | _, _ => false

def precedes (source target : PageElement owner) : Prop := target.page ≤ source.page

def transported (source target : PageElement owner) : Prop :=
  Trace.traceSuffix source.trace target.trace = true

structure Arrow (source target : PageElement owner) : Type where
  precedes : precedes source target
  transported : transported source target

instance (source target : PageElement owner) : Subsingleton (Arrow source target) :=
  ⟨by intro a b; cases a; cases b; rfl⟩

def identityArrow (x : PageElement owner) : Arrow x x :=
  ⟨le_rfl, (Trace.traceSuffix_iff _ _).2 List.suffix_rfl⟩

def composeArrows {x y z : PageElement owner} (first : Arrow x y) (second : Arrow y z) :
    Arrow x z :=
  ⟨second.precedes.trans first.precedes,
    (Trace.traceSuffix_iff _ _).2
      (((Trace.traceSuffix_iff _ _).1 second.transported).trans
        ((Trace.traceSuffix_iff _ _).1 first.transported))⟩

instance : Category (PageElement owner) where
  Hom := Arrow
  id := identityArrow
  comp := composeArrows
  id_comp := fun _ => Subsingleton.elim _ _
  comp_id := fun _ => Subsingleton.elim _ _
  assoc := fun _ _ _ => Subsingleton.elim _ _

/-- The two independent parameters match normalizePageElementAt, including
its behavior on malformed raw traces and negative trace limits. -/
def normalize (finalPage : Nat) (traceLimit : Int) (value : PageElement owner) : PageElement owner :=
  { value with page := min value.page finalPage, trace := Trace.trimTrace traceLimit value.trace }

-- ALIGN: PE-NORMALIZE-IDEMPOTENT.
theorem normalize_idempotent (finalPage : Nat) (traceLimit : Int) (value : PageElement owner) :
    normalize finalPage traceLimit (normalize finalPage traceLimit value) =
      normalize finalPage traceLimit value := by
  simp [normalize, Trace.trimTraceIdempotent]

-- ALIGN: PE-NORMALIZE-ARROW.
def normalizeArrow (finalPage : Nat) (traceLimit : Int) {x y : PageElement owner}
    (arrow : Arrow x y) : Arrow (normalize finalPage traceLimit x) (normalize finalPage traceLimit y) :=
  ⟨min_le_min_right _ arrow.precedes,
    Trace.trimTracePreservesSuffix _ _ _ arrow.transported⟩

/-- Every raw occurrence reaches its normalized representative. -/
def toNormalized (finalPage : Nat) (traceLimit : Int) (x : PageElement owner) :
    Arrow x (normalize finalPage traceLimit x) :=
  ⟨min_le_left _ _, Trace.trimTraceIsSuffix _ _⟩

def normalization (finalPage : Nat) (traceLimit : Int) : PageElement owner ⥤ PageElement owner where
  obj := normalize finalPage traceLimit
  map := normalizeArrow finalPage traceLimit

end PageElement

end Datra.Executable

namespace Datra.Executable.FolioData
variable {origin final : Page}

def paddedIndex (pages : FolioData origin final) (n : Nat) : Fin pages.depth :=
  ⟨min n (pages.depth - 1), by have := pages.depth_positive; omega⟩

def pageAt (pages : FolioData origin final) (n : Nat) : Page :=
  pages.page (pages.indexEquivFin.symm (pages.paddedIndex n))

@[simp] theorem paddedIndex_fin (pages : FolioData origin final) (i : Fin pages.depth) :
    pages.paddedIndex i.val = i := by
  apply Fin.ext
  exact Nat.min_eq_left (by have := i.isLt; omega)

@[simp] theorem pageAt_fin (pages : FolioData origin final) (i : Fin pages.depth) :
    pages.pageAt i.val = pages.page (pages.indexEquivFin.symm i) := by
  simp only [pageAt, paddedIndex_fin]

def transport (pages : FolioData origin final) (source target : Nat) (h : target ≤ source) :
    Consolidation (pages.pageAt source).chain (pages.pageAt target).chain :=
  pages.interval (pages.indexEquivFin.symm (pages.paddedIndex source))
    (pages.indexEquivFin.symm (pages.paddedIndex target))
    (by simpa [paddedIndex] using min_le_min_right (pages.depth - 1) h)

@[simp] theorem transport_identity (pages : FolioData origin final) (n : Nat) :
    pages.transport n n le_rfl = Consolidation.identity (pages.pageAt n).chain :=
  pages.interval_identity _

theorem transport_comp (pages : FolioData origin final) (source middle target : Nat)
    (h₁ : middle ≤ source) (h₂ : target ≤ middle) :
    Consolidation.comp (pages.transport source middle h₁) (pages.transport middle target h₂) =
      pages.transport source target (h₂.trans h₁) :=
  pages.interval_comp _ _ _ _ _

/-- All and only valid full-spine cells. The complete trace is computed below
from this dependent pair, so an arbitrary raw trace cannot enter Atlas laws. -/
structure Occurrence (pages : FolioData origin final) where
  page : Nat
  value : (pages.pageAt page).Carrier

@[ext] theorem Occurrence.ext {pages : FolioData origin final} {x y : pages.Occurrence}
    (hp : x.page = y.page) (hv : HEq x.value y.value) : x = y := by
  cases x
  cases y
  cases hp
  cases hv
  rfl

def traceAt (pages : FolioData origin final) : (n : Nat) → (pages.pageAt n).Carrier → List Ordinal
  | 0, x => [(pages.pageAt 0).chain.position x]
  | n + 1, x => (pages.pageAt (n + 1)).chain.position x ::
      pages.traceAt n ((pages.transport (n + 1) n (Nat.le_succ n)).map x)

@[simp] theorem traceAt_length (pages : FolioData origin final) (n : Nat)
    (x : (pages.pageAt n).Carrier) : (pages.traceAt n x).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [traceAt, List.length_cons, ih]

@[simp] theorem traceAt_head (pages : FolioData origin final) (n : Nat)
    (x : (pages.pageAt n).Carrier) :
    (pages.traceAt n x).head? = some ((pages.pageAt n).chain.position x) := by
  cases n <;> rfl

def Occurrence.toRaw {pages : FolioData origin final} (x : pages.Occurrence) : PageElement pages where
  page := x.page
  position := (pages.pageAt x.page).chain.position x.value
  trace := pages.traceAt x.page x.value
  cell := ⟨(pages.pageAt x.page).Carrier, (pages.pageAt x.page).chain, x.value,
    min x.page (pages.depth - 1)⟩

-- ALIGN: PE-TRACE-TRANSPORT.
theorem traceAt_drop (pages : FolioData origin final) (source target : Nat) (h : target ≤ source)
    (x : (pages.pageAt source).Carrier) :
    (pages.traceAt source x).drop (source - target) =
      pages.traceAt target ((pages.transport source target h).map x) := by
  induction source generalizing target with
  | zero =>
      have : target = 0 := by omega
      subst target
      simp [transport_identity, Consolidation.identity]
  | succ source ih =>
      by_cases he : target = source + 1
      · subst target
        simp [transport_identity, Consolidation.identity]
      · have ht : target ≤ source := by omega
        have hn : source + 1 - target = (source - target) + 1 := by omega
        rw [traceAt, hn, List.drop_succ_cons, ih target ht]
        have hc := congrArg Consolidation.map
          (pages.transport_comp (source + 1) source target (Nat.le_succ source) ht)
        exact congrArg (pages.traceAt target) (congrFun hc x)

end Datra.Executable.FolioData

namespace Datra.Executable.FolioData
open CategoryTheory Opposite
variable {origin final : Page}

-- ALIGN: PE-ARROW-REPRESENTATION.
theorem traceAt_suffix_iff (pages : FolioData origin final) (source target : Nat) (h : target ≤ source)
    (x : (pages.pageAt source).Carrier) (y : (pages.pageAt target).Carrier) :
    Trace.traceSuffix (pages.traceAt source x) (pages.traceAt target y) = true ↔
      (pages.transport source target h).map x = y := by
  rw [Trace.traceSuffix_iff, List.suffix_iff_eq_drop]
  simp only [traceAt_length, Nat.add_sub_add_right]
  rw [pages.traceAt_drop source target h x]
  constructor
  · intro he
    have hh := congrArg List.head? he
    simp only [traceAt_head, Option.some.injEq] at hh
    exact ((pages.pageAt target).chain.positionInjective hh).symm
  · intro he
    rw [he]

namespace Occurrence
variable {pages : FolioData origin final}

instance : Category pages.Occurrence where
  Hom x y := PageElement.Arrow x.toRaw y.toRaw
  id x := PageElement.identityArrow x.toRaw
  comp f g := PageElement.composeArrows f g
  id_comp := fun _ => Subsingleton.elim _ _
  comp_id := fun _ => Subsingleton.elim _ _
  assoc := fun _ _ _ => Subsingleton.elim _ _

instance (x y : pages.Occurrence) : Subsingleton (x ⟶ y) :=
  inferInstanceAs (Subsingleton (PageElement.Arrow x.toRaw y.toRaw))

/-- On valid occurrences the trace-suffix test is precisely the element-category
transport equation. This functor does not replace traces by arbitrary arrows. -/
noncomputable def toSemantics (pages : FolioData origin final) :
    pages.Occurrence ⥤ pages.toSemantics.TallEl where
  obj x := ⟨op x.page, x.value⟩
  map {x y} f := CategoryOfElements.homMk _ _ (homOfLE f.precedes).op
    ((pages.traceAt_suffix_iff x.page y.page f.precedes x.value y.value).1 f.transported)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

noncomputable def fromSemantics (pages : FolioData origin final) :
    pages.toSemantics.TallEl ⥤ pages.Occurrence where
  obj x := ⟨x.1.unop, x.2⟩
  map {x y} f :=
    ⟨leOfHom f.val.unop,
      (pages.traceAt_suffix_iff x.1.unop y.1.unop (leOfHom f.val.unop) x.2 y.2).2 f.property⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

-- ALIGN: PE-ELEMENTS-EQUIVALENCE.
noncomputable def elementsEquivalence (pages : FolioData origin final) :
    pages.Occurrence ≌ pages.toSemantics.TallEl where
  functor := toSemantics pages
  inverse := fromSemantics pages
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end Occurrence
end Datra.Executable.FolioData

namespace Datra.Executable.FolioData
variable {origin final : Page}

@[simp] theorem paddedIndex_clamp (pages : FolioData origin final) (n : Nat) :
    pages.paddedIndex (min n (pages.depth - 1)) = pages.paddedIndex n := by
  apply Fin.ext
  simp [paddedIndex]

private theorem interval_cell_eq (pages : FolioData origin final) (source target : pages.Index)
    (h : pages.indexNumber target ≤ pages.indexNumber source) (e : source = target)
    (x : (pages.page source).Carrier) :
    (⟨(pages.page target).Carrier, (pages.page target).chain,
      (pages.interval source target h).map x, pages.indexNumber target⟩ : PageElementCell) =
      ⟨(pages.page source).Carrier, (pages.page source).chain, x, pages.indexNumber source⟩ := by
  subst target
  simp [interval_identity, Consolidation.identity]

private theorem interval_position_eq (pages : FolioData origin final) (source target : pages.Index)
    (h : pages.indexNumber target ≤ pages.indexNumber source) (e : source = target)
    (x : (pages.page source).Carrier) :
    (pages.page target).chain.position ((pages.interval source target h).map x) =
      (pages.page source).chain.position x := by
  subst target
  simp [interval_identity, Consolidation.identity]

namespace Occurrence
variable {pages : FolioData origin final}

def normalize (x : pages.Occurrence) : pages.Occurrence :=
  ⟨min x.page (pages.depth - 1),
    (pages.transport x.page (min x.page (pages.depth - 1)) (min_le_left _ _)).map x.value⟩

-- ALIGN: PE-NORMALIZE-REPRESENTATION.
theorem normalize_toRaw (x : pages.Occurrence) :
    x.normalize.toRaw = PageElement.normalize (pages.depth - 1) pages.depth x.toRaw := by
  have hi : pages.indexEquivFin.symm (pages.paddedIndex x.page) =
      pages.indexEquivFin.symm (pages.paddedIndex (min x.page (pages.depth - 1))) := by simp
  have hp := pages.interval_position_eq _ _
    (show pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex (min x.page (pages.depth - 1)))) ≤
      pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex x.page)) by simp) hi x.value
  have hc := pages.interval_cell_eq _ _
    (show pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex (min x.page (pages.depth - 1)))) ≤
      pages.indexNumber (pages.indexEquivFin.symm (pages.paddedIndex x.page)) by simp) hi x.value
  have ht : pages.traceAt (min x.page (pages.depth - 1))
      ((pages.transport x.page (min x.page (pages.depth - 1)) (min_le_left _ _)).map x.value) =
      Trace.trimTrace pages.depth (pages.traceAt x.page x.value) := by
    rw [Trace.trimTrace_eq_drop, traceAt_length]
    simp only [Int.toNat_natCast]
    have hn : x.page + 1 - pages.depth =
        x.page - min x.page (pages.depth - 1) := by
      have := pages.depth_positive
      omega
    rw [hn, traceAt_drop]
  simp only [normalize, toRaw, PageElement.normalize, PageElement.mk.injEq]
  exact ⟨True.intro, hp, ht, by
    simpa only [indexEquivFin_symm_number, paddedIndex] using hc⟩

theorem toRaw_injective : Function.Injective (toRaw (pages := pages)) := by
  intro x y he
  have hp := congrArg PageElement.page he
  cases x with
  | mk n x =>
      cases y with
      | mk m y =>
          change n = m at hp
          subst m
          have hv := congrArg PageElement.position he
          change (pages.pageAt n).chain.position x = (pages.pageAt n).chain.position y at hv
          have := (pages.pageAt n).chain.positionInjective hv
          subst y
          rfl

theorem normalize_idempotent (x : pages.Occurrence) : x.normalize.normalize = x.normalize := by
  apply toRaw_injective
  rw [normalize_toRaw, normalize_toRaw, PageElement.normalize_idempotent]

end Occurrence
end Datra.Executable.FolioData

namespace Datra.Executable.FolioData
open CategoryTheory
variable {origin final : Page}

/-- Public page elements are exactly those produced by the owning folio.
Keeping the raw record exposes the literal preservation of its cell payload. -/
def ValidElement (pages : FolioData origin final) :=
  { x : PageElement pages // ∃ occurrence : pages.Occurrence, occurrence.toRaw = x }

namespace ValidElement
variable {pages : FolioData origin final}

def ofOccurrence (x : pages.Occurrence) : pages.ValidElement := ⟨x.toRaw, x, rfl⟩

/-- Recover the page value through the same checked position lookup used by
page-element construction. Validity proves that the decoder succeeds. -/
def occurrence (x : pages.ValidElement) : pages.Occurrence :=
  ⟨x.val.page, (((pages.pageAt x.val.page).chain.chainIndex x.val.position).get (by
    obtain ⟨source, same⟩ := x.property
    rw [← same]
    simp only [Occurrence.toRaw, Chain.chainIndex_position, Option.isSome_some])).object⟩

@[simp] theorem occurrence_toRaw (x : pages.ValidElement) : x.occurrence.toRaw = x.val :=
  by
    obtain ⟨raw, valid⟩ := x
    obtain ⟨source, rfl⟩ := valid
    simp only [occurrence, Occurrence.toRaw, Chain.chainIndex_position, Option.get_some,
      Chain.chainIndexOf]

@[simp] theorem occurrence_ofOccurrence (x : pages.Occurrence) : (ofOccurrence x).occurrence = x :=
  Occurrence.toRaw_injective (occurrence_toRaw _)

@[simp] theorem ofOccurrence_occurrence (x : pages.ValidElement) : ofOccurrence x.occurrence = x :=
  Subtype.ext (occurrence_toRaw x)

instance : Category pages.ValidElement where
  Hom x y := PageElement.Arrow x.val y.val
  id x := PageElement.identityArrow x.val
  comp f g := PageElement.composeArrows f g
  id_comp := fun _ => Subsingleton.elim _ _
  comp_id := fun _ => Subsingleton.elim _ _
  assoc := fun _ _ _ => Subsingleton.elim _ _

instance (x y : pages.ValidElement) : Subsingleton (x ⟶ y) :=
  inferInstanceAs (Subsingleton (PageElement.Arrow x.val y.val))

def normalize (x : pages.ValidElement) : pages.ValidElement :=
  ⟨PageElement.normalize (pages.depth - 1) pages.depth x.val, by
    obtain ⟨y, hy⟩ := x.property
    exact ⟨y.normalize, by rw [Occurrence.normalize_toRaw, hy]⟩⟩

@[simp] theorem normalize_cell (x : pages.ValidElement) : x.normalize.val.cell = x.val.cell := rfl

theorem normalize_idempotent (x : pages.ValidElement) : x.normalize.normalize = x.normalize :=
  Subtype.ext (PageElement.normalize_idempotent _ _ _)

def normalizeArrow {x y : pages.ValidElement} (f : x ⟶ y) : x.normalize ⟶ y.normalize :=
  PageElement.normalizeArrow _ _ f

def toNormalized (x : pages.ValidElement) : x ⟶ x.normalize := PageElement.toNormalized _ _ _

def normalization : pages.ValidElement ⥤ pages.ValidElement where
  obj := normalize
  map := normalizeArrow

noncomputable def occurrenceEquivalence (pages : FolioData origin final) :
    pages.ValidElement ≌ pages.Occurrence where
  functor :=
    { obj := occurrence
      map := fun {x y} f => by
        change PageElement.Arrow x.occurrence.toRaw y.occurrence.toRaw
        simpa only [occurrence_toRaw] using f
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  inverse :=
    { obj := ofOccurrence
      map := fun f => f }
  unitIso := NatIso.ofComponents (fun x => eqToIso (ofOccurrence_occurrence x).symm)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun x => eqToIso (occurrence_ofOccurrence x))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp := fun _ => Subsingleton.elim _ _

noncomputable def elementsEquivalence (pages : FolioData origin final) :
    pages.ValidElement ≌ pages.toSemantics.TallEl :=
  (occurrenceEquivalence pages).trans (Occurrence.elementsEquivalence pages)

end ValidElement
end Datra.Executable.FolioData

namespace Datra.Executable.FolioData.ValidElement
open CategoryTheory
variable {origin final : Page} {pages : FolioData origin final}

theorem eq_of_page_position {x y : pages.ValidElement}
    (hp : x.val.page = y.val.page) (hv : x.val.position = y.val.position) : x = y := by
  rcases x with ⟨_, ⟨⟨n, x⟩, rfl⟩⟩
  rcases y with ⟨_, ⟨⟨m, y⟩, rfl⟩⟩
  change n = m at hp
  subst m
  change (pages.pageAt n).chain.position x = (pages.pageAt n).chain.position y at hv
  have := (pages.pageAt n).chain.positionInjective hv
  subst y
  rfl

@[simp] theorem cell_genuinePage (x : pages.ValidElement) :
    x.val.cell.genuinePage = x.normalize.val.page := by
  rcases x with ⟨_, ⟨occurrence, rfl⟩⟩
  rfl

@[simp] theorem cell_position (x : pages.ValidElement) :
    x.val.cell.chain.position x.val.cell.value = x.val.position := by
  rcases x with ⟨_, ⟨occurrence, rfl⟩⟩
  rfl

/-- The data-family index identifies exactly a genuine cell. Padded copies
share that index; distinct genuine pages do not, even with equal payloads. -/
theorem cell_eq_iff_normalize_eq (x y : pages.ValidElement) :
    x.val.cell = y.val.cell ↔ x.normalize = y.normalize := by
  constructor
  · intro h
    apply eq_of_page_position
    · simpa only [cell_genuinePage] using congrArg PageElementCell.genuinePage h
    · have positions := congrArg (fun cell : PageElementCell => cell.chain.position cell.value) h
      simpa only [cell_position] using positions
  · intro h
    have cells := congrArg (fun value : pages.ValidElement => value.val.cell) h
    exact cells

theorem cell_ne_of_genuine_pages_ne {x y : pages.ValidElement}
    (hx : x.normalize = x) (hy : y.normalize = y) (different : x.val.page ≠ y.val.page) :
    x.val.cell ≠ y.val.cell := by
  intro equal
  have same := (cell_eq_iff_normalize_eq x y).mp equal
  rw [hx, hy] at same
  exact different (congrArg (fun value : pages.ValidElement => value.val.page) same)

@[simp] theorem trace_length (x : pages.ValidElement) : x.val.trace.length = x.val.page + 1 := by
  rcases x with ⟨_, ⟨occurrence, rfl⟩⟩
  exact pages.traceAt_length occurrence.page occurrence.value

@[simp] theorem trace_head (x : pages.ValidElement) : x.val.trace.head? = some x.val.position := by
  rcases x with ⟨_, ⟨occurrence, rfl⟩⟩
  exact pages.traceAt_head occurrence.page occurrence.value

-- ALIGN: ATLAS-ORDER-TRACE-LOOKUP.
theorem positionAtPage_arrow {x y : pages.ValidElement} (f : x ⟶ y) :
    PageElement.positionAtPage y.val.page x.val = some y.val.position := by
  have hs := (Trace.traceSuffix_iff _ _).mp f.transported
  have hd := (List.suffix_iff_eq_drop).mp hs
  rw [trace_length, trace_length, Nat.add_sub_add_right] at hd
  rw [PageElement.positionAtPage, ← hd]
  exact trace_head y

noncomputable def fromFinite (pages : FolioData origin final) :
    pages.toSemantics.El ⥤ pages.ValidElement :=
  pages.toSemantics.includeElements ⋙ (elementsEquivalence pages).inverse

@[simp] theorem fromFinite_page (x : pages.toSemantics.El) :
    ((fromFinite pages).obj x).val.page = x.1.unop.val := rfl

theorem fromFinite_injective (pages : FolioData origin final) :
    Function.Injective (fromFinite pages).obj := by
  intro x y h
  have ho := congrArg occurrence h
  change (ofOccurrence ⟨_, _⟩).occurrence = (ofOccurrence ⟨_, _⟩).occurrence at ho
  simp only [occurrence_ofOccurrence] at ho
  have hs := congrArg (Occurrence.toSemantics pages).obj ho
  change pages.toSemantics.includeElements.obj x = pages.toSemantics.includeElements.obj y at hs
  have hc := congrArg pages.toSemantics.collapseElements.obj hs
  simpa using hc

@[simp] theorem normalize_ofOccurrence (x : pages.Occurrence) :
    (ofOccurrence x).normalize = ofOccurrence x.normalize :=
  Subtype.ext x.normalize_toRaw.symm

/-- Executable clamping corresponds to collapse followed by inclusion on the
semantic padded diagram, including the dependent cell transport. -/
theorem normalize_toSemantics (x : pages.ValidElement) :
    (elementsEquivalence pages).functor.obj x.normalize =
      pages.toSemantics.includeElements.obj (pages.toSemantics.collapseElements.obj
        ((elementsEquivalence pages).functor.obj x)) := by
  obtain ⟨value, hv⟩ := x.property
  have hx : x = ofOccurrence value := Subtype.ext hv.symm
  subst x
  rw [normalize_ofOccurrence]
  change (Occurrence.toSemantics pages).obj (ofOccurrence value.normalize).occurrence =
    pages.toSemantics.includeElements.obj (pages.toSemantics.collapseElements.obj
      ((Occurrence.toSemantics pages).obj (ofOccurrence value).occurrence))
  rw [occurrence_ofOccurrence, occurrence_ofOccurrence]
  rfl

@[simp] theorem inverse_functor_obj (x : pages.ValidElement) :
    (elementsEquivalence pages).inverse.obj ((elementsEquivalence pages).functor.obj x) = x :=
  ofOccurrence_occurrence x

@[simp] theorem functor_inverse_obj (x : pages.toSemantics.TallEl) :
    (elementsEquivalence pages).functor.obj ((elementsEquivalence pages).inverse.obj x) = x := by
  change (Occurrence.toSemantics pages).obj (ofOccurrence _).occurrence = x
  rw [occurrence_ofOccurrence]
  rfl

theorem fromFinite_collapse (x : pages.ValidElement) :
    (fromFinite pages).obj (pages.toSemantics.collapseElements.obj
      ((elementsEquivalence pages).functor.obj x)) = x.normalize := by
  have h := congrArg (elementsEquivalence pages).inverse.obj (normalize_toSemantics x)
  rw [inverse_functor_obj] at h
  exact h.symm

@[simp] theorem normalize_fromFinite (pages : FolioData origin final)
    (x : pages.toSemantics.El) :
    ((fromFinite pages).obj x).normalize = (fromFinite pages).obj x := by
  have h := fromFinite_collapse ((fromFinite pages).obj x)
  simpa only [fromFinite, Functor.comp_obj, functor_inverse_obj,
    Datra.Semantics.Folio.collapse_include_obj] using h.symm

/-- Construct a genuine finite occurrence directly from its certified page.
Only equality transport is needed; the executable constructor uses no choice. -/
def ofFinite (pages : FolioData origin final) (i : Fin pages.depth)
    (value : (pages.page (pages.indexEquivFin.symm i)).Carrier) : pages.ValidElement :=
  ofOccurrence ⟨i.val, cast (congrArg Page.Carrier (pages.pageAt_fin i).symm) value⟩

theorem ofFinite_interpretation (pages : FolioData origin final) (i : Fin pages.depth)
    (value : (pages.page (pages.indexEquivFin.symm i)).Carrier) :
    ofFinite pages i value = (fromFinite pages).obj ⟨Opposite.op i, value⟩ := by
  apply congrArg ofOccurrence
  apply Occurrence.ext
  · rfl
  · change HEq (cast (congrArg Page.Carrier (pages.pageAt_fin i).symm) value)
      (pages.toSemantics.cellDiagram.map
        (eqToHom (congrArg Opposite.op (pages.toSemantics.paddedIndex_fin i).symm)) value)
    have map_heq {a b : (Fin pages.depth)ᵒᵖ} (h : a = b)
        (v : pages.toSemantics.cellDiagram.obj a) :
        HEq (pages.toSemantics.cellDiagram.map (eqToHom h) v) v := by
      cases h
      simp
    exact (cast_heq _ value).trans (map_heq _ value).symm

@[simp] theorem fromFinite_position (pages : FolioData origin final) (i : Fin pages.depth)
    (value : (pages.page (pages.indexEquivFin.symm i)).Carrier) :
    ((fromFinite pages).obj ⟨Opposite.op i, value⟩).val.position =
      (pages.page (pages.indexEquivFin.symm i)).chain.position value := by
  rw [← ofFinite_interpretation]
  have position_cast {A B : Page} (h : A = B) (v : B.Carrier) :
      A.chain.position (cast (congrArg Page.Carrier h.symm) v) = B.chain.position v := by
    cases h
    rfl
  exact position_cast (pages.pageAt_fin i) value

def originFiniteValue (pages : FolioData origin final) :
    (pages.page (pages.indexEquivFin.symm ⟨0, pages.depth_positive⟩)).Carrier :=
  cast (congrArg Page.Carrier
    ((congrArg pages.page pages.zero_index).trans pages.firstIndex_page).symm) pages.originValue

def originElement (pages : FolioData origin final) : pages.ValidElement :=
  ofFinite pages ⟨0, pages.depth_positive⟩ (originFiniteValue pages)

-- ALIGN: PE-ORIGIN-INTERPRETATION.
theorem originElement_interpretation (pages : FolioData origin final) :
    originElement pages = (fromFinite pages).obj pages.toSemantics.originElement := by
  rw [originElement, ofFinite_interpretation]
  have h := pages.toSemantics.origin_unique (originFiniteValue pages)
  rw [h]
  rfl

def finalIndex (pages : FolioData origin final) : Fin pages.depth :=
  ⟨pages.depth - 1, by have := pages.depth_positive; omega⟩

theorem finalIndex_page (pages : FolioData origin final) :
    pages.page (pages.indexEquivFin.symm (finalIndex pages)) = final := by
  have h : pages.indexEquivFin.symm (finalIndex pages) = pages.lastIndex := by
    apply pages.indexEquivFin.injective
    apply Fin.ext
    rw [Equiv.apply_symm_apply, indexEquivFin_val]
    cases pages <;> simp [finalIndex, depth, lastIndex, indexNumber]
  rw [h, page_lastIndex]

def finalFiniteValue (pages : FolioData origin final) (value : final.Carrier) :
    (pages.page (pages.indexEquivFin.symm (finalIndex pages))).Carrier :=
  cast (congrArg Page.Carrier (finalIndex_page pages).symm) value

def lastElement (pages : FolioData origin final) (index : ChainIndex final.chain) :
    pages.ValidElement := ofFinite pages (finalIndex pages) (finalFiniteValue pages index.object)

-- ALIGN: PE-LAST-INTERPRETATION.
theorem lastElement_interpretation (pages : FolioData origin final) (index : ChainIndex final.chain) :
    lastElement pages index = (fromFinite pages).obj
      ⟨pages.toSemantics.lastBase, finalFiniteValue pages index.object⟩ :=
  ofFinite_interpretation pages (finalIndex pages) (finalFiniteValue pages index.object)

/-- Every valid occurrence on the final genuine page is a territory cell. -/
theorem lastElement_surjective (pages : FolioData origin final) (x : pages.ValidElement)
    (h : x.val.page = pages.depth - 1) :
    ∃ index : ChainIndex final.chain, lastElement pages index = x := by
  rcases x with ⟨_, ⟨⟨n, value⟩, rfl⟩⟩
  change n = pages.depth - 1 at h
  subst n
  let hf : pages.pageAt (pages.depth - 1) = final :=
    (pages.pageAt_fin (finalIndex pages)).trans (finalIndex_page pages)
  let v : final.Carrier := cast (congrArg Page.Carrier hf) value
  refine ⟨final.chain.chainIndexOf v, ?_⟩
  change ofOccurrence _ = ofOccurrence _
  apply congrArg ofOccurrence
  apply Occurrence.ext
  · rfl
  · exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

private theorem origin_subsingleton (pages : FolioData origin final) :
    Subsingleton (pages.pageAt 0).Carrier := by
  have h : pages.pageAt 0 = origin := by
    rw [pages.pageAt_fin ⟨0, pages.depth_positive⟩, zero_index, firstIndex_page]
  rw [h]
  exact ⟨fun x y => (pages.originUnique x).trans (pages.originUnique y).symm⟩

/-- Every valid full-spine occurrence reaches its unique origin cell. -/
def toOrigin (x : pages.ValidElement) : x ⟶ originElement pages := by
  refine ⟨Nat.zero_le _, ?_⟩
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := (originElement pages).property
  have hp : b.page = 0 := congrArg PageElement.page hb
  change Trace.traceSuffix x.val.trace (originElement pages).val.trace = true
  rw [← ha, ← hb]
  apply (pages.traceAt_suffix_iff a.page b.page (by omega) a.value b.value).2
  have hs : Subsingleton (pages.pageAt b.page).Carrier := by
    rw [hp]
    exact origin_subsingleton pages
  exact hs.elim _ _

end Datra.Executable.FolioData.ValidElement
