import Executable.Folio.Prefix

namespace Datra.Executable
open CategoryTheory

/-- A checked full-spine interval induces the corresponding traced arrow. -/
def FolioData.transportArrow {origin final : Page} (pages : FolioData origin final)
    (source target : Nat) (precedes : target ≤ source) (value : (pages.pageAt source).Carrier) :
    (FolioData.ValidElement.ofOccurrence (⟨source, value⟩ : pages.Occurrence)) ⟶
      FolioData.ValidElement.ofOccurrence
        (⟨target, (pages.transport source target precedes).map value⟩ : pages.Occurrence) :=
  ⟨precedes, (pages.traceAt_suffix_iff source target precedes value _).mpr rfl⟩

namespace Folio.PrefixResolution

universe u

variable (origin : Page) (selected : origin.Carrier) (unique : ∀ x, x = selected)
    (pages : Nat → Page) (collapse : Consolidation (pages 0).chain origin.chain)
    (step : ∀ n, Consolidation (pages (n + 1)).chain (pages n).chain)
    {Label : Type u} (root : Label) (resolve : ∀ n, (pages n).Carrier → Label)

/-- Resolve a stored prefix index by the same recursion that builds its folio. -/
def atIndex : (n : Nat) →
    (index : (buildPrefix origin selected unique pages collapse step n).data.Index) →
    ((buildPrefix origin selected unique pages collapse step n).data.page index).Carrier → Label
  | 0, none, value => resolve 0 value
  | 0, some _, _ => root
  | n + 1, none, value => resolve (n + 1) value
  | n + 1, some index, value => atIndex n index value

theorem atIndex_first (n : Nat)
    (value : ((buildPrefix origin selected unique pages collapse step n).data.page (buildPrefix origin selected unique pages collapse step n).data.firstIndex).Carrier) :
    atIndex origin selected unique pages collapse step root resolve n (buildPrefix origin selected unique pages collapse step n).data.firstIndex value = root := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih value

theorem atIndex_heq (n : Nat)
    {i j : (buildPrefix origin selected unique pages collapse step n).data.Index} (same : i = j)
    {a : ((buildPrefix origin selected unique pages collapse step n).data.page i).Carrier}
    {b : ((buildPrefix origin selected unique pages collapse step n).data.page j).Carrier} (values : HEq a b) :
    atIndex origin selected unique pages collapse step root resolve n i a = atIndex origin selected unique pages collapse step root resolve n j b := by
  subst j
  cases values
  rfl

theorem atIndex_component (n : Nat) (k : Fin (n + 1))
    (value : (pages k.val).Carrier) :
    atIndex origin selected unique pages collapse step root resolve n (prefixIndex origin selected unique pages collapse step n k)
      (cast (congrArg Page.Carrier (prefixIndex_page origin selected unique pages collapse step n k).symm) value) =
      resolve k.val value := by
  induction n with
  | zero =>
    have hk : k = ⟨0, by omega⟩ := Fin.ext (by have := k.isLt; omega)
    subst k
    rfl
  | succ n ih =>
    by_cases last : k.val = n + 1
    · obtain ⟨k, hk⟩ := k
      dsimp only at last
      subst k
      have index : prefixIndex origin selected unique pages collapse step (n + 1) ⟨n + 1, hk⟩ = none := by simp [prefixIndex]
      exact atIndex_heq origin selected unique pages collapse step root resolve (n + 1) index (cast_heq _ value)
    · let previous : Fin (n + 1) := ⟨k.val, by have := k.isLt; omega⟩
      have index : prefixIndex origin selected unique pages collapse step (n + 1) k = some (prefixIndex origin selected unique pages collapse step n previous) := by
        simp [prefixIndex, last, previous]
      exact (atIndex_heq origin selected unique pages collapse step root resolve (n + 1) index
        ((cast_heq _ value).trans (cast_heq (congrArg Page.Carrier
          (prefixIndex_page origin selected unique pages collapse step n previous).symm) value).symm)).trans (ih previous value)

/-- Pagewise separation survives the shared finite-prefix construction. -/
theorem atIndex_separates (accepts : Label → Prop)
    (separates : ∀ n (a b : (pages n).Carrier), accepts (resolve n a) → accepts (resolve n b) → a = b)
    (n : Nat) (index : (buildPrefix origin selected unique pages collapse step n).data.Index)
    (a b : ((buildPrefix origin selected unique pages collapse step n).data.page index).Carrier)
    (inA : accepts (atIndex origin selected unique pages collapse step root resolve n index a))
    (inB : accepts (atIndex origin selected unique pages collapse step root resolve n index b)) : a = b := by
  induction n with
  | zero =>
    cases index with
    | none => exact separates 0 a b inA inB
    | some index => exact (unique a).trans (unique b).symm
  | succ n ih =>
    cases index with
    | none => exact separates (n + 1) a b inA inB
    | some index => exact ih index a b inA inB

variable (Rel : Label → Label → Prop)
    (identity : ∀ x, Rel x x)
    (compose : ∀ {a b c}, Rel a b → Rel b c → Rel a c)
    (toRoot : ∀ n value, Rel (resolve n value) root)
    (adjacent : ∀ n value, Rel (resolve (n + 1) value) (resolve n ((step n).map value)))

include identity compose toRoot adjacent

theorem lastInterval (n : Nat)
    (target : (buildPrefix origin selected unique pages collapse step n).data.Index)
    (value : (pages n).Carrier) :
    Rel (resolve n value)
      (atIndex origin selected unique pages collapse step root resolve n target
        ((buildPrefix origin selected unique pages collapse step n).data.lastInterval target |>.map value)) := by
  induction n with
  | zero =>
    cases target with
    | none => exact identity _
    | some target => exact toRoot 0 value
  | succ n ih =>
    cases target with
    | none => exact identity _
    | some target => exact compose (adjacent n value) (ih target ((step n).map value))

/-- Adjacent resolution laws extend to every generated finite interval. -/
theorem interval (n : Nat)
    (source target : (buildPrefix origin selected unique pages collapse step n).data.Index)
    (precedes : (buildPrefix origin selected unique pages collapse step n).data.indexNumber target ≤
      (buildPrefix origin selected unique pages collapse step n).data.indexNumber source)
    (value : ((buildPrefix origin selected unique pages collapse step n).data.page source).Carrier) :
    Rel (atIndex origin selected unique pages collapse step root resolve n source value)
      (atIndex origin selected unique pages collapse step root resolve n target
        ((buildPrefix origin selected unique pages collapse step n).data.interval source target precedes |>.map value)) := by
  induction n with
  | zero =>
    cases source with
    | none =>
      cases target with
      | none => exact identity _
      | some target => exact toRoot 0 value
    | some source =>
      cases target with
      | none => have : 1 ≤ 0 := precedes; omega
      | some target => exact identity root
  | succ n ih =>
    cases source with
    | none =>
      cases target with
      | none => exact identity _
      | some target =>
        exact compose (adjacent n value)
          (lastInterval origin selected unique pages collapse step root resolve Rel identity compose toRoot adjacent
            n target ((step n).map value))
    | some source =>
      cases target with
      | none =>
        exact False.elim (Nat.not_le_of_lt
          ((buildPrefix origin selected unique pages collapse step n).data.indexNumber_lt source) precedes)
      | some target => exact ih source target precedes value

end Folio.PrefixResolution
end Datra.Executable
