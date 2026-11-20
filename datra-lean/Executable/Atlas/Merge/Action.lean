import Executable.Atlas.Merge.Transport

namespace Datra.Executable.AtlasMerge

universe u
open CategoryTheory

-- ALIGN: MERGE-RAW-DATA-INSERTION.
def rawDataMap {Scope : Type u} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (sourceCell targetCell : PageElementCell) :
    DomanialInsertion
      (AcceptedDatum (resolvedContains X Y source : Datum sourceCell → Bool))
      (AcceptedDatum (resolvedContains X Y target : Datum targetCell → Bool)) :=
  acceptedInsertion (resolvedContains X Y source) (resolvedContains X Y target)
    (fun datum accepted => resolvedContains_preserved X Y arrow sourceValid targetValid datum accepted)

-- ALIGN: MERGE-RAW-DATA-APPLY.
theorem rawDataMap_apply {Scope : Type u} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (sourceCell targetCell : PageElementCell)
    (datum : AcceptedDatum (resolvedContains X Y source : Datum sourceCell → Bool)) :
    ((rawDataMap X Y arrow sourceValid targetValid sourceCell targetCell).map datum).val =
      retag datum.val := rfl

-- ALIGN: MERGE-RAW-DATA-PREIMAGE.
theorem rawDataMap_preimage {Scope : Type u} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (sourceCell targetCell : PageElementCell)
    (datum : AcceptedDatum (resolvedContains X Y target : Datum targetCell → Bool)) :
    ((rawDataMap X Y arrow sourceValid targetValid sourceCell targetCell).preimage datum).map Subtype.val =
      preimageDatum (resolvedContains X Y source) datum.val :=
  acceptedInsertion_preimage _ _ _ datum

-- ALIGN: MERGE-RAW-DOMINION.
def rawDominion {Scope : Type u} {owner : Scope} (X Y : Atlas) (occurrence : PageElement owner) :
    Dominion (AcceptedDatum (resolvedContains X Y occurrence : Datum occurrence.cell → Bool)) :=
  lookupDominion (resolvedContains X Y occurrence)

-- ALIGN: MERGE-RAW-ACTION.
def rawAction (X Y : Atlas) : AtlasMembershipAction (folio X Y).data Datum :=
  AtlasMembershipAction.packagePredicate
    (PageElementDomain.ofFolio (folio X Y).data (folio X Y))
    (fun occurrence => resolvedContains X Y occurrence)
    (fun occurrence _ => rawDominion X Y occurrence)
    (fun sourceValid targetValid arrow => rawDataMap X Y arrow
      (by simpa only [PageElementDomain.contains, PageElementDomain.ofFolio, FolioData.traceValid, decide_eq_true_eq] using sourceValid)
      (by simpa only [PageElementDomain.contains, PageElementDomain.ofFolio, FolioData.traceValid, decide_eq_true_eq] using targetValid) _ _)

instance rawAction_folioOwner (X Y : Atlas) : AtlasMembershipAction.FolioOwner (rawAction X Y) :=
  ⟨(folio X Y).valid, rfl⟩

-- ALIGN: MERGE-RAW-ACTION-IDENTITY.
theorem rawAction_identity (X Y : Atlas) (source : (folio X Y).data.ValidElement)
    (datum : (rawAction X Y).membership.Carrier source.normalize.val) :
    (((rawAction X Y).normalizedMap (𝟙 source)).map datum).val = datum.val :=
  retag_self datum.val

-- ALIGN: MERGE-RAW-ACTION-COMPOSITION.
theorem rawAction_composition (X Y : Atlas) {source middle target : (folio X Y).data.ValidElement}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (datum : (rawAction X Y).membership.Carrier source.normalize.val) :
    (((rawAction X Y).normalizedMap (first ≫ second)).map datum).val =
      (((rawAction X Y).normalizedMap second).map
        (((rawAction X Y).normalizedMap first).map datum)).val :=
  (retag_retag datum.val).symm

-- ALIGN: MERGE-RAW-ACTION-COHERENCE.
theorem rawAction_coherence (X Y : Atlas) (source : (folio X Y).data.ValidElement)
    (datum : (rawAction X Y).membership.Carrier source.normalize.val) :
    (((rawAction X Y).normalizedMap source.toNormalized).map datum).val = datum.val :=
  retag_self datum.val

-- ALIGN: MERGE-RAW-ACTION-DISJOINT.
theorem rawAction_disjoint (X Y : Atlas)
    {first second origin : (folio X Y).data.ValidElement}
    (samePage : second.val.page = first.val.page)
    (different : second.val.position ≠ first.val.position)
    (genuine : first.val.page ≤ (folio X Y).data.depth - 1)
    (atOrigin : origin.val.page = 0)
    (firstArrow : first ⟶ origin) (secondArrow : second ⟶ origin)
    (firstDatum : (rawAction X Y).membership.Carrier first.normalize.val)
    (secondDatum : (rawAction X Y).membership.Carrier second.normalize.val) :
    (((rawAction X Y).normalizedMap firstArrow).map firstDatum).val ≠
      (((rawAction X Y).normalizedMap secondArrow).map secondDatum).val := by
  by_cases atZero : first.val.page = 0
  · have firstPosition := FolioData.ValidElement.positionAtPage_arrow firstArrow
    have secondPosition := FolioData.ValidElement.positionAtPage_arrow secondArrow
    simp only [PageElement.positionAtPage, atOrigin, atZero, samePage, Nat.sub_self,
      List.drop_zero, first.trace_head, second.trace_head, Option.some.injEq] at firstPosition secondPosition
    exact (different (secondPosition.trans firstPosition.symm)).elim
  · intro same
    change retag (target := origin.normalize.val.cell) firstDatum.val = retag secondDatum.val at same
    have excluded := resolvedContains_disjoint X Y first.normalize.val second.normalize.val
      (by change 0 < min first.val.page ((folio X Y).data.depth - 1)
          rw [Nat.min_eq_left genuine]
          omega)
      (congrArg (fun n => min n ((folio X Y).data.depth - 1)) samePage)
      different firstDatum.val firstDatum.property
    have accepted : resolvedContains X Y second.normalize.val
        (retag (target := origin.normalize.val.cell) secondDatum.val) = true := by
      rw [resolvedContains_retag]
      exact secondDatum.property
    rw [← same, resolvedContains_retag, excluded] at accepted
    contradiction

theorem rawAction_laws (X Y : Atlas) : (rawAction X Y).Laws where
  identity := rawAction_identity X Y
  composition := rawAction_composition X Y
  coherence := rawAction_coherence X Y
  disjoint samePage different genuine atOrigin firstArrow secondArrow firstDatum secondDatum :=
    rawAction_disjoint X Y samePage.symm (Ne.symm different) genuine atOrigin
      firstArrow secondArrow firstDatum secondDatum

/-- The runtime merge's checked membership action and four laws assemble into
an Atlas through the shared normalization interpretation. -/
-- ALIGN: MERGE-RAW-ATLAS-CONSTRUCTION.
def rawAtlas (X Y : Atlas) : Atlas :=
  AtlasMembershipAction.toCanonicalAtlas (pagination X Y) (rawAction X Y) (rawAction_laws X Y)

end Datra.Executable.AtlasMerge
