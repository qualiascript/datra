import Executable.Atlas.Sequence.Transition
import Executable.Folio.Assembly

namespace Datra.Executable.AtlasSequence

-- ALIGN: SEQUENCE-NATIVE-DEPTH.
def nativeDepth : List Member → Nat
  | [] => 0
  | member :: rest => max member.length (nativeDepth rest)

theorem nativeDepth_foldl (members : List Member) (initial : Nat) :
    (members.map Member.length).foldl max initial = max initial (nativeDepth members) := by
  induction members generalizing initial with
  | nil => simp [nativeDepth]
  | cons member rest ih => simp [nativeDepth, ih, Nat.max_assoc]

-- ALIGN: SEQUENCE-NATIVE-DEPTH-INTERPRETATION.
theorem nativeDepth_interpretation {count : Nat} (members : Fin count → Atlas) :
    nativeDepth (nativeMembers members) = sequenceDepth members := by
  have same : (nativeMembers members).map Member.length =
      List.ofFn (fun index => (members index).pages.length) := by
    simp [nativeMembers, Member.length, Function.comp_def]
  unfold sequenceDepth
  rw [← same, nativeDepth_foldl]
  simp

/-- Retain both native functions while expressing their orders on the interpreted pages. -/
def nativeConsolidation {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    Consolidation (pageChain members (page + 1)) (pageChain members page) where
  map := (nativePageTransition members page).map.map
  preimage := (nativePageTransition members page).map.preimage
  monotone first second ordered := by
    have sourceOrdered :
        (((nativePageTransition members page).source).position first).toSemantics ≤
          (((nativePageTransition members page).source).position second).toSemantics := by
      simpa only [nativePageTransition_source] using ordered
    simpa only [nativePageTransition_target] using
      (nativePageTransition members page).map.monotone first second sourceOrdered
  rightInverse := (nativePageTransition members page).map.rightInverse

theorem nativeConsolidation_eq {count : Nat} (members : Fin count → Atlas) (page : Nat) :
    nativeConsolidation members page = pageTransition members page := by
  apply Consolidation.ext
  · funext cell; exact nativePageTransition_map members page cell
  · funext cell; exact nativePageTransition_preimage members page cell

-- ALIGN: SEQUENCE-CONSTRUCTED-PREFIX.
def nativePrefixFolio {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) (page : Nat) :
    Folio DomanialInclusion.singletonPage (sequencePage members page) :=
  Folio.buildPrefix DomanialInclusion.singletonPage () (fun value => by cases value; rfl)
    (sequencePage members)
    (Folio.collapseToOrigin (pageChain members 0) Chain.singletonChain (firstPageCell positive members)).map
    (nativeConsolidation members) page

theorem nativePrefixFolio_length {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) (page : Nat) :
    (nativePrefixFolio positive members page).data.length = page + 2 :=
  Folio.buildPrefix_length _ _ _ _ _ _ _

-- ALIGN: SEQUENCE-CONSTRUCTED-PREFIX-LOOKUP.
theorem nativePrefixFolio_lookup_prefix {count : Nat} (inhabited : 0 < count) (members : Fin count → Atlas)
    (middle depth : Nat) (positive : 0 < middle) (bound : middle ≤ depth)
    (page : Nat) (earlier : page ≤ middle) (position : Ordinal) :
    (nativePrefixFolio inhabited members (depth - 1)).data.traceLookup page position =
      (nativePrefixFolio inhabited members (middle - 1)).data.traceLookup page position :=
  Folio.buildPrefix_lookup_prefix _ _ _ _ _ _ _ _ (by omega) _ (by omega) _

theorem nativePrefixFolio_eq {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) (page : Nat) :
    nativePrefixFolio positive members page = prefixFolio positive members page := by
  have steps : nativeConsolidation members = pageTransition members := funext (nativeConsolidation_eq members)
  simp only [nativePrefixFolio, prefixFolio, steps]
  rfl

-- ALIGN: SEQUENCE-FOLIO-PREFIX.
def nativeExtendPrefix {count : Nat} (members : Fin count → Atlas) (start remaining : Nat)
    (initial : Folio DomanialInclusion.singletonPage (sequencePage members start)) :
    Folio DomanialInclusion.singletonPage (sequencePage members (start + remaining)) :=
  Folio.extendPrefix (sequencePage members) (nativeConsolidation members) start remaining initial

-- ALIGN: SEQUENCE-PREFIX-LOOKUP-PRESERVED.
theorem nativeExtendPrefix_lookup {count : Nat} (members : Fin count → Atlas) (start remaining : Nat)
    (initial : Folio DomanialInclusion.singletonPage (sequencePage members start))
    (page : Nat) (earlier : page < initial.data.length) (position : Ordinal) :
    (nativeExtendPrefix members start remaining initial).data.traceLookup page position =
      initial.data.traceLookup page position :=
  Folio.extendPrefix_lookup _ _ _ _ _ _ earlier _

-- ALIGN: SEQUENCE-NATIVE-FOLIO-PREFIX.
theorem nativeExtendPrefix_eq {count : Nat} (positive : 0 < count) (members : Fin count → Atlas)
    (start remaining : Nat) :
    nativeExtendPrefix members start remaining (nativePrefixFolio positive members start) =
      nativePrefixFolio positive members (start + remaining) :=
  Folio.extendPrefix_buildPrefix _ _ _ _ _ _ _ _

-- ALIGN: SEQUENCE-NATIVE-FOLIO.
def nativeFolio {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) :
    Folio DomanialInclusion.singletonPage (sequencePage members (sequenceDepth members - 1)) :=
  nativePrefixFolio positive members (sequenceDepth members - 1)

-- ALIGN: SEQUENCE-GENUINE-PAGE-LOOKUP.
theorem nativeFolio_pageLookup_prefix {count : Nat} (inhabited : 0 < count) (members : Fin count → Atlas)
    (page : Nat) (positive : 0 < page) (bound : page ≤ sequenceDepth members) (position : Ordinal) :
    (nativeFolio inhabited members).data.traceLookup page position =
      (nativePrefixFolio inhabited members (page - 1)).data.traceLookup page position :=
  nativePrefixFolio_lookup_prefix inhabited members page (sequenceDepth members) positive bound page le_rfl position

-- ALIGN: SEQUENCE-GENUINE-CELL-LOOKUP.
theorem nativeFolio_cellLookup_prefix {count : Nat} (inhabited : 0 < count) (members : Fin count → Atlas)
    (page : Nat) (positive : 0 < page) (bound : page ≤ sequenceDepth members)
    (cell : ValidPageCell members (page - 1)) :
    (nativeFolio inhabited members).data.traceLookup page (pagePosition members (page - 1) cell.val) =
      some ((nativePrefixFolio inhabited members (page - 1)).data.genuineTrace cell) := by
  rw [nativeFolio_pageLookup_prefix inhabited members page positive bound]
  have found := (nativePrefixFolio inhabited members (page - 1)).data.traceLookup_last_value
    (nativePrefixFolio inhabited members (page - 1)).valid cell
  have last : (nativePrefixFolio inhabited members (page - 1)).data.length - 1 = page := by
    rw [nativePrefixFolio_length]
    omega
  rw [last] at found
  simpa only [sequencePage, pageChain_position] using found

-- ALIGN: SEQUENCE-NATIVE-FOLIO-INTERPRETATION.
theorem nativeFolio_eq {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) :
    nativeFolio positive members = folio positive members :=
  nativePrefixFolio_eq positive members (sequenceDepth members - 1)

theorem nativeFolio_length {count : Nat} (positive : 0 < count) (members : Fin count → Atlas) :
    (nativeFolio positive members).data.length = nativeDepth (nativeMembers members) + 1 := by
  rw [nativeFolio_eq, folio_length, nativeDepth_interpretation]

end Datra.Executable.AtlasSequence
