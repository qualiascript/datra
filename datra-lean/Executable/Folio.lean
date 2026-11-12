import Executable.Consolidation
import Executable.Trace

namespace Datra.Executable

structure Page where
  Carrier : Type
  chain : Chain Carrier

/-- The cached counts and the existential previous page mirror FolioData.
Only the smart constructors below establish the cache invariant. -/
inductive FolioData : Page → Page → Type 1
  | origin (page : Page) (count : Nat) (selected : page.Carrier)
      (unique : ∀ x : page.Carrier, x = selected) : FolioData page page
  | snoc {origin previous : Page} (count : Nat) (pages : FolioData origin previous)
      (next : Page) (transition : Consolidation next.chain previous.chain) : FolioData origin next

namespace FolioData
variable {origin final : Page}

def length {origin final : Page} : FolioData origin final → Nat
  | .origin _ count _ _ => count
  | .snoc count _ _ _ => count

def depth {origin final : Page} : FolioData origin final → Nat
  | .origin .. => 1
  | .snoc _ previous _ _ => previous.depth + 1

def Valid {origin final : Page} : FolioData origin final → Prop
  | .origin _ count _ _ => count = 1
  | .snoc count previous _ _ => previous.Valid ∧ count = previous.length + 1

def singleton (page : Page) (selected : page.Carrier) (unique : ∀ x, x = selected) :
    FolioData page page := .origin page 1 selected unique

def append (pages : FolioData origin final) (next : Page)
    (transition : Consolidation next.chain final.chain) : FolioData origin next :=
  .snoc (pages.length + 1) pages next transition

theorem singleton_valid (page : Page) (selected : page.Carrier) (unique : ∀ x, x = selected) :
    (singleton page selected unique).Valid := rfl

theorem append_valid (pages : FolioData origin final) (h : pages.Valid) (next : Page)
    (transition : Consolidation next.chain final.chain) : (pages.append next transition).Valid :=
  ⟨h, rfl⟩

theorem length_eq_depth (pages : FolioData origin final) (h : pages.Valid) :
    pages.length = pages.depth := by
  induction pages with
  | origin => exact h
  | snoc count previous next transition ih =>
      exact h.2.trans (congrArg (· + 1) (ih h.1))

theorem depth_positive (pages : FolioData origin final) : 0 < pages.depth := by
  cases pages <;> simp [depth]

def originValue {origin final : Page} : FolioData origin final → origin.Carrier
  | .origin _ _ selected _ => selected
  | .snoc _ previous _ _ => previous.originValue

-- ALIGN: FOLIO-ORIGIN-UNIQUE.
theorem originUnique (pages : FolioData origin final) (x : origin.Carrier) :
    x = pages.originValue := by
  induction pages with
  | origin _ _ unique => exact unique x
  | snoc _ _ _ _ ih => exact ih

/-- A structural finite index, with none denoting the new final page. -/
def Index {origin final : Page} : FolioData origin final → Type
  | .origin .. => Unit
  | .snoc _ previous _ _ => Option previous.Index

def indexNumber {origin final : Page} : (pages : FolioData origin final) → pages.Index → Nat
  | .origin .. => fun _ => 0
  | .snoc _ previous _ _ => fun
      | none => previous.depth
      | some index => previous.indexNumber index

def page {origin final : Page} : (pages : FolioData origin final) → pages.Index → Page
  | .origin _ _ _ _ => fun _ => origin
  | .snoc _ previous next _ => fun
      | none => next
      | some index => previous.page index

def lastIndex {origin final : Page} : (pages : FolioData origin final) → pages.Index
  | .origin .. => ()
  | .snoc .. => none

@[simp] theorem page_lastIndex (pages : FolioData origin final) :
    pages.page pages.lastIndex = final := by cases pages <;> rfl

theorem indexNumber_lt (pages : FolioData origin final) (index : pages.Index) :
    pages.indexNumber index < pages.depth := by
  induction pages with
  | origin => exact Nat.zero_lt_one
  | snoc _ previous _ _ ih =>
      cases index with
      | none => exact Nat.lt_succ_self _
      | some i => exact (ih i).trans (Nat.lt_succ_self _)

/-- Full genuine trace, obtained by applying each adjacent transport.
This is never synthesized from page numbers alone. -/
def genuineTrace {origin final : Page} : (pages : FolioData origin final) → final.Carrier → List Ordinal
  | .origin _ _ _ _ => fun value => [origin.chain.position value]
  | .snoc _ previous next transition => fun value =>
      next.chain.position value :: previous.genuineTrace (transition.map value)

-- ALIGN: FOLIO-TRACE-LENGTH.
theorem genuineTrace_length (pages : FolioData origin final) (value : final.Carrier) :
    (pages.genuineTrace value).length = pages.depth := by
  induction pages with
  | origin => rfl
  | snoc _ previous _ _ ih => simp only [genuineTrace, List.length_cons, ih, depth]

/-- Occurrences after the stored spine repeat the final position in front of
the genuine transport trace, exactly as prependCopies does in Haskell. -/
def paddedTrace (pages : FolioData origin final) (padding : Nat) (value : final.Carrier) : List Ordinal :=
  List.replicate padding (final.chain.position value) ++ pages.genuineTrace value

-- ALIGN: FOLIO-PADDED-TRACE-NORMALIZE.
theorem paddedTrace_normalize (pages : FolioData origin final) (padding : Nat) (value : final.Carrier) :
    Trace.trimTrace pages.depth (pages.paddedTrace padding value) = pages.genuineTrace value := by
  rw [Trace.trimTrace_eq_drop]
  simp [paddedTrace, genuineTrace_length]

end FolioData

/-- Public folios have consistent cached counts; raw constructors are modeled
separately so the invariant is visible rather than silently assumed. -/
structure Folio (origin final : Page) where
  data : FolioData origin final
  valid : data.Valid

end Datra.Executable

namespace Datra.Executable.FolioData
variable {origin final : Page}

/-- Transport from the last genuine page follows the snoc generators. -/
def lastInterval {origin final : Page} : (pages : FolioData origin final) →
    (target : pages.Index) → Consolidation final.chain (pages.page target).chain
  | .origin _ _ _ _ => fun _ => Consolidation.identity origin.chain
  | .snoc _ previous next transition => fun
      | none => Consolidation.identity next.chain
      | some index => Consolidation.comp transition (previous.lastInterval index)

/-- Interval transport is defined before, and independently of, functor laws. -/
def interval {origin final : Page} : (pages : FolioData origin final) →
    (source target : pages.Index) → pages.indexNumber target ≤ pages.indexNumber source →
    Consolidation (pages.page source).chain (pages.page target).chain
  | .origin _ _ _ _ => fun _ _ _ => Consolidation.identity origin.chain
  | .snoc _ previous next transition => fun
      | none, none, _ => Consolidation.identity next.chain
      | none, some index, _ => Consolidation.comp transition (previous.lastInterval index)
      | some _, none, h => False.elim (Nat.not_le_of_lt (previous.indexNumber_lt _) h)
      | some source, some target, h => previous.interval source target h

-- ALIGN: FOLIO-INTERVAL-IDENTITY.
theorem interval_identity (pages : FolioData origin final) (index : pages.Index) :
    pages.interval index index le_rfl = Consolidation.identity (pages.page index).chain := by
  induction pages with
  | origin => rfl
  | snoc _ previous _ _ ih => cases index with
    | none => rfl
    | some index => exact ih index

theorem lastInterval_comp (pages : FolioData origin final) (middle target : pages.Index)
    (h : pages.indexNumber target ≤ pages.indexNumber middle) :
    Consolidation.comp (pages.lastInterval middle) (pages.interval middle target h) =
      pages.lastInterval target := by
  induction pages with
  | origin => exact Consolidation.identity_comp _
  | snoc _ previous _ _ ih =>
      cases middle with
      | none => cases target <;> exact Consolidation.identity_comp _
      | some middle =>
          cases target with
          | none => exact False.elim (Nat.not_le_of_lt (previous.indexNumber_lt middle) h)
          | some target =>
              change Consolidation.comp (Consolidation.comp _ _) _ = Consolidation.comp _ _
              simp only [interval]
              rw [Consolidation.comp_assoc, ih middle target h]

-- ALIGN: FOLIO-INTERVAL-COMPOSITION.
theorem interval_comp (pages : FolioData origin final) (source middle target : pages.Index)
    (h₁ : pages.indexNumber middle ≤ pages.indexNumber source)
    (h₂ : pages.indexNumber target ≤ pages.indexNumber middle) :
    Consolidation.comp (pages.interval source middle h₁) (pages.interval middle target h₂) =
      pages.interval source target (h₂.trans h₁) := by
  induction pages with
  | origin => exact Consolidation.identity_comp _
  | snoc _ previous _ _ ih =>
      cases source with
      | none =>
          cases middle with
          | none => cases target <;> exact Consolidation.identity_comp _
          | some middle =>
              cases target with
              | none => exact False.elim (Nat.not_le_of_lt (previous.indexNumber_lt middle) h₂)
              | some target =>
                  change Consolidation.comp (Consolidation.comp _ _) _ = Consolidation.comp _ _
                  simp only [interval]
                  rw [Consolidation.comp_assoc, previous.lastInterval_comp middle target h₂]
      | some source =>
          cases middle with
          | none => exact False.elim (Nat.not_le_of_lt (previous.indexNumber_lt source) h₁)
          | some middle =>
              cases target with
              | none => exact False.elim (Nat.not_le_of_lt (previous.indexNumber_lt middle) h₂)
              | some target => exact ih source middle target h₁ h₂

end Datra.Executable.FolioData

namespace Datra.Executable.FolioData
open CategoryTheory Opposite
variable {origin final : Page}

def indexEquivFin {origin final : Page} : (pages : FolioData origin final) → pages.Index ≃ Fin pages.depth
  | .origin .. =>
      ⟨fun _ => ⟨0, Nat.zero_lt_one⟩, fun _ => (), fun _ => rfl, fun i => Fin.ext (by change 0 = i.val; have h := i.isLt; change i.val < 1 at h; omega)⟩
  | .snoc _ previous _ _ =>
      (Equiv.optionCongr previous.indexEquivFin).trans finSuccEquivLast.symm

@[simp] theorem indexEquivFin_val (pages : FolioData origin final) (index : pages.Index) :
    (pages.indexEquivFin index).val = pages.indexNumber index := by
  induction pages with
  | origin => rfl
  | snoc _ previous _ _ ih =>
      cases index with
      | none =>
          change (finSuccEquivLast.symm (none : Option (Fin previous.depth))).val = previous.depth
          exact congrArg Fin.val finSuccEquivLast_symm_none
      | some index =>
          change (finSuccEquivLast.symm (some (previous.indexEquivFin index))).val = _
          rw [finSuccEquivLast_symm_some]
          exact ih index

@[simp] theorem indexEquivFin_symm_number (pages : FolioData origin final) (n : Fin pages.depth) :
    pages.indexNumber (pages.indexEquivFin.symm n) = n.val := by
  rw [← indexEquivFin_val, Equiv.apply_symm_apply]

def firstIndex {origin final : Page} : (pages : FolioData origin final) → pages.Index
  | .origin .. => ()
  | .snoc _ previous _ _ => some previous.firstIndex

@[simp] theorem firstIndex_number (pages : FolioData origin final) :
    pages.indexNumber pages.firstIndex = 0 := by
  induction pages with
  | origin => rfl
  | snoc _ _ _ _ ih => exact ih

@[simp] theorem firstIndex_page (pages : FolioData origin final) :
    pages.page pages.firstIndex = origin := by
  induction pages with
  | origin => rfl
  | snoc _ _ _ _ ih => exact ih

theorem zero_index (pages : FolioData origin final) :
    pages.indexEquivFin.symm ⟨0, pages.depth_positive⟩ = pages.firstIndex := by
  apply pages.indexEquivFin.injective
  apply Fin.ext
  simp

/-- The finite categorical diagram is generated by the stored adjacent maps. -/
noncomputable def core (pages : FolioData origin final) : Fin pages.depth ⥤ Datra.Semantics.CoCon where
  obj n := op (pages.page (pages.indexEquivFin.symm n)).chain.toSemantics
  map {i j} f := Quiver.Hom.op
    (pages.interval (pages.indexEquivFin.symm j) (pages.indexEquivFin.symm i)
      (by simpa using leOfHom f)).toSemantics
  map_id i := by
    apply Quiver.Hom.unop_inj
    change (pages.interval (pages.indexEquivFin.symm i) (pages.indexEquivFin.symm i) _).toSemantics = _
    rw [interval_identity]
    rfl
  map_comp {i j k} f g := by
    have h := pages.interval_comp (pages.indexEquivFin.symm k)
      (pages.indexEquivFin.symm j) (pages.indexEquivFin.symm i)
      (by simpa using leOfHom g) (by simpa using leOfHom f)
    apply Quiver.Hom.unop_inj
    change (pages.interval _ _ _).toSemantics = _
    rw [← h]
    rfl

noncomputable def toSemantics (pages : FolioData origin final) : Datra.Semantics.Folio where
  length := pages.depth
  positive := pages.depth_positive
  core := pages.core
  originEquiv := by
    change (pages.page (pages.indexEquivFin.symm ⟨0, pages.depth_positive⟩)).Carrier ≃ Unit
    rw [zero_index, firstIndex_page]
    exact ⟨fun _ => (), fun _ => pages.originValue,
      fun x => (pages.originUnique x).symm, fun _ => Subsingleton.elim _ _⟩

-- ALIGN: FOLIO-SEMANTIC-LENGTH.
theorem toSemantics_length (pages : FolioData origin final) (valid : pages.Valid) :
    pages.toSemantics.length = pages.length := (pages.length_eq_depth valid).symm

-- ALIGN: FOLIO-SEMANTIC-INTERVAL.
theorem core_interval (pages : FolioData origin final) {i j : Fin pages.depth} (h : i ≤ j) :
    (pages.core.map (homOfLE h)).unop =
      (pages.interval (pages.indexEquivFin.symm j) (pages.indexEquivFin.symm i)
        (by simpa using h)).toSemantics := rfl

end Datra.Executable.FolioData
