import Executable.Atlas.ChainedDominionAction
import Executable.Atlas.Presentation
import Executable.Folio.Assembly

namespace Datra.Executable.ChainedDominionAtlas
open CategoryTheory

variable {A : Type} {Scope : Type*} {scope : Scope} {origin final : Page}

-- ALIGN: CHAINED-FOLIO-MEMBERSHIP.
def acceptsValue (_owner : Chain A) (_value : A) : Bool := true

-- ALIGN: CHAINED-TWO-PAGE-REGION.
theorem twoPageRegionPosition (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (occurrence : PageElement scope)
    (positive : 0 < occurrence.page) :
    (occurrence.normalize (pages.depth - 1) pages.depth).page = 1 := by
  have depth : pages.depth = 2 := (pages.length_eq_depth valid).symm.trans twoPages
  simp only [PageElement.normalize, depth]
  omega

/-- In a two-page presentation, an arrow between non-origin occurrences
retains the selected final-page position, including through padding. -/
theorem twoPageArrowPosition (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2)
    {source target : PageElement scope} (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true)
    (targetValid : pages.traceValid target = true)
    (sourcePositive : 0 < source.page) (targetPositive : 0 < target.page) :
    source.position = target.position := by
  have sourcePage := twoPageRegionPosition pages valid twoPages source sourcePositive
  have targetPage := twoPageRegionPosition pages valid twoPages target targetPositive
  exact (PageElement.normalizeArrow (pages.depth - 1) pages.depth arrow).samePagePosition
    (pages.traceValid_shape valid _ (pages.traceValid_normalize valid source sourceValid))
    (pages.traceValid_shape valid _ (pages.traceValid_normalize valid target targetValid))
    (sourcePage.trans targetPage.symm)

-- ALIGN: CHAINED-ARROW-COMPATIBLE.
theorem chainedArrowCompatible (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A)
    {source target : PageElement scope} (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true)
    (targetValid : pages.traceValid target = true) :
    cellPrecedes owner (chainedDominionCell first owner source)
      (chainedDominionCell first owner target) = true := by
  by_cases sourceOrigin : source.page = 0
  · have targetOrigin : target.page = 0 := by
      have order := arrow.precedes
      simp only [PageElement.precedes, sourceOrigin] at order
      omega
    simp [chainedDominionCell, sourceOrigin, targetOrigin, cellPrecedes]
  by_cases targetOrigin : target.page = 0
  · simp [chainedDominionCell, sourceOrigin, targetOrigin, cellPrecedes]
  have samePosition := twoPageArrowPosition pages valid twoPages arrow sourceValid targetValid (by omega) (by omega)
  simp [chainedDominionCell, sourceOrigin, targetOrigin, cellPrecedes,
    chainValueAt, samePosition]

-- ALIGN: CHAINED-REGION-POSITION.
theorem chainedRegionPosition (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : final.Carrier)
    (owner : Chain final.Carrier) (sameChain : owner = final.chain)
    (occurrence : PageElement scope) (accepted : pages.traceValid occurrence = true)
    (positive : 0 < occurrence.page) :
    owner.position (chainValueAt first owner occurrence) = occurrence.position := by
  subst owner
  have depth : pages.depth = 2 := (pages.length_eq_depth valid).symm.trans twoPages
  have lower : pages.depth - 1 ≤ occurrence.page := by omega
  have lookup := of_decide_eq_true accepted
  change pages.traceLookup occurrence.page occurrence.position = some occurrence.trace at lookup
  rw [pages.traceLookup_final valid _ _ lower] at lookup
  obtain ⟨index, found, _⟩ := Option.map_eq_some_iff.mp lookup
  simpa [chainValueAt, found] using
    index.position_eq.trans (final.chain.chainIndex_requested occurrence.position index found)

-- ALIGN: CHAINED-PRESENTATION-MEMBERSHIP.
def chainedDominionAccepts {Object : Type} (first : A) (owner : Chain A)
    (occurrence : PageElement scope) (datum : ChainedDominionCellData A Object) : Bool :=
  cellAccepts owner (chainedDominionCell first owner occurrence) datum

-- ALIGN: CHAINED-PRESENTATION-DOMINION.
def chainedDominionAt {Object : Type} (first : A) (owner : Chain A)
    (valueDominion : Dominion A) (occurrence : PageElement scope) :
    Dominion (CellCarrier owner (chainedDominionCell first owner occurrence) Object) :=
  match chainedDominionCell first owner occurrence with
  | .extent => extentDominion valueDominion
  | .region selected => regionDominion owner selected

-- ALIGN: CHAINED-PRESENTATION-INSERTION.
def chainedDominionDataMap {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (first : A) (owner : Chain A) {source target : PageElement scope}
    (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true) :
    DomanialInsertion (CellCarrier owner (chainedDominionCell first owner source) Source)
      (CellCarrier owner (chainedDominionCell first owner target) Target) :=
  cellInsertion owner _ _ (chainedArrowCompatible pages valid twoPages first owner arrow sourceValid targetValid)

-- ALIGN: CHAINED-PRESENTATION-FORWARD.
theorem chainedDominionDataMap_map {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (first : A) (owner : Chain A) {source target : PageElement scope}
    (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true)
    (datum : CellCarrier owner (chainedDominionCell first owner source) Source) :
    ((chainedDominionDataMap (Target := Target) pages valid twoPages first owner arrow sourceValid targetValid).map datum).val =
      cellMap owner (chainedDominionCell first owner source) (chainedDominionCell first owner target) datum.val := rfl

-- ALIGN: CHAINED-PRESENTATION-INVERSE.
theorem chainedDominionDataMap_preimage {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (first : A) (owner : Chain A) {source target : PageElement scope}
    (arrow : PageElement.Arrow source target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true)
    (datum : CellCarrier owner (chainedDominionCell first owner target) Target) :
    ((chainedDominionDataMap (Source := Source) pages valid twoPages first owner arrow sourceValid targetValid).preimage datum).map
      (fun value => value.val) =
      cellPreimage owner (chainedDominionCell first owner source) (chainedDominionCell first owner target) datum.val :=
  cellInsertion_preimage owner _ _ _ datum

-- ALIGN: CHAINED-ARROW-NORMALIZATION.
def normalizedArrow (pages : FolioData origin final) (valid : pages.Valid)
    {source target : PageElement scope} (arrow : source.Arrow target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true) :
    {result : (source.normalize (pages.depth - 1) pages.depth).Arrow
        (target.normalize (pages.depth - 1) pages.depth) //
      result = PageElement.normalizeArrow (pages.depth - 1) pages.depth arrow ∧
      pages.traceValid (source.normalize (pages.depth - 1) pages.depth) = true ∧
      pages.traceValid (target.normalize (pages.depth - 1) pages.depth) = true} :=
  ⟨PageElement.normalizeArrow (pages.depth - 1) pages.depth arrow, rfl,
    pages.traceValid_normalize valid source sourceValid,
    pages.traceValid_normalize valid target targetValid⟩

-- ALIGN: CHAINED-OWNED-NORMALIZATION.
theorem ownedCellNormalization (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (occurrence : PageElement scope) :
    chainedDominionCell first owner (occurrence.normalize (pages.depth - 1) pages.depth) =
      chainedDominionCell first owner occurrence := by
  have depth : pages.depth = 2 := (pages.length_eq_depth valid).symm.trans twoPages
  simpa only [depth, Nat.reduceSub, Nat.cast_ofNat] using cellNormalization first owner occurrence

-- ALIGN: CHAINED-PRESENTATION-ACTION.
def chainedDominionAction (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (D : Dominion A) :
    AtlasMembershipAction pages (fun cell => ChainedDominionCellData A cell.Carrier) :=
  AtlasMembershipAction.packagePredicate (PageElementDomain.ofFolio pages ⟨pages, valid⟩)
    (fun occurrence datum => chainedDominionAccepts first owner occurrence datum)
    (fun occurrence _ => chainedDominionAt first owner D occurrence)
    (fun sourceValid targetValid arrow =>
      chainedDominionDataMap pages valid twoPages first owner arrow sourceValid targetValid)

instance chainedDominionAction_owner (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (D : Dominion A) :
    (chainedDominionAction pages valid twoPages first owner D).FolioOwner := ⟨valid, rfl⟩

-- ALIGN: CHAINED-PRESENTATION-IDENTITY.
theorem chainedIdentity (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (D : Dominion A)
    (source : pages.ValidElement)
    (datum : (chainedDominionAction pages valid twoPages first owner D).membership.Carrier source.normalize.val) :
    (((chainedDominionAction pages valid twoPages first owner D).normalizedMap (𝟙 source)).map datum).val = datum.val := by
  exact (cellIdentity owner (chainedDominionCell first owner source.normalize.val) datum.val).1

-- ALIGN: CHAINED-PRESENTATION-COMPOSITION.
theorem chainedComposition (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (D : Dominion A)
    {source middle target : pages.ValidElement} (before : source ⟶ middle) (after : middle ⟶ target)
    (datum : (chainedDominionAction pages valid twoPages first owner D).membership.Carrier source.normalize.val) :
    (((chainedDominionAction pages valid twoPages first owner D).normalizedMap (before ≫ after)).map datum).val =
      (((chainedDominionAction pages valid twoPages first owner D).normalizedMap after).map
        (((chainedDominionAction pages valid twoPages first owner D).normalizedMap before).map datum)).val := by
  exact (cellComposition owner _ _ _
    (chainedArrowCompatible pages valid twoPages first owner (FolioData.ValidElement.normalizeArrow before)
      (source.normalize.traceValid valid) (middle.normalize.traceValid valid))
    (chainedArrowCompatible pages valid twoPages first owner (FolioData.ValidElement.normalizeArrow after)
      (middle.normalize.traceValid valid) (target.normalize.traceValid valid)) datum.val).symm

-- ALIGN: CHAINED-PRESENTATION-COHERENCE.
theorem chainedCoherence (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : A) (owner : Chain A) (D : Dominion A)
    (source : pages.ValidElement)
    (datum : (chainedDominionAction pages valid twoPages first owner D).membership.Carrier source.normalize.val) :
    (((chainedDominionAction pages valid twoPages first owner D).normalizedMap source.toNormalized).map datum).val = datum.val := by
  change cellMap owner (chainedDominionCell first owner source.normalize.val)
    (chainedDominionCell first owner source.normalize.normalize.val) datum.val = datum.val
  rw [FolioData.ValidElement.normalize_idempotent]
  exact (cellIdentity owner _ datum.val).1

-- ALIGN: CHAINED-PRESENTATION-DISJOINT.
theorem chainedDisjoint (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : final.Carrier) (owner : Chain final.Carrier)
    (sameChain : owner = final.chain) (D : Dominion final.Carrier)
    {left right root : pages.ValidElement} (samePage : left.val.page = right.val.page)
    (distinct : left.val.position ≠ right.val.position) (_bounded : left.val.page ≤ pages.depth - 1)
    (atOrigin : root.val.page = 0) (leftArrow : left ⟶ root) (rightArrow : right ⟶ root)
    (leftDatum : (chainedDominionAction pages valid twoPages first owner D).membership.Carrier left.normalize.val)
    (rightDatum : (chainedDominionAction pages valid twoPages first owner D).membership.Carrier right.normalize.val) :
    (((chainedDominionAction pages valid twoPages first owner D).normalizedMap leftArrow).map leftDatum).val ≠
      (((chainedDominionAction pages valid twoPages first owner D).normalizedMap rightArrow).map rightDatum).val := by
  intro same
  by_cases leftOrigin : left.val.page = 0
  · have l := leftArrow.samePagePosition (left.traceValid valid |> pages.traceValid_shape valid left.val)
      (root.traceValid valid |> pages.traceValid_shape valid root.val) (leftOrigin.trans atOrigin.symm)
    have r := rightArrow.samePagePosition (right.traceValid valid |> pages.traceValid_shape valid right.val)
      (root.traceValid valid |> pages.traceValid_shape valid root.val) (samePage.symm.trans (leftOrigin.trans atOrigin.symm))
    exact distinct (l.trans r.symm)
  have rightOrigin : right.val.page ≠ 0 := by omega
  have leftAccepted : cellAccepts owner (chainedDominionCell first owner left.val) leftDatum.val = true := by
    simpa only [chainedDominionAction, AtlasMembershipAction.packagePredicate, AtlasMembershipAction.package,
      AtlasMembership.accepts, chainedDominionAccepts, FolioData.ValidElement.normalize,
      ownedCellNormalization pages valid twoPages] using leftDatum.property
  have rightAccepted : cellAccepts owner (chainedDominionCell first owner right.val) rightDatum.val = true := by
    simpa only [chainedDominionAction, AtlasMembershipAction.packagePredicate, AtlasMembershipAction.package,
      AtlasMembership.accepts, chainedDominionAccepts, FolioData.ValidElement.normalize,
      ownedCellNormalization pages valid twoPages] using rightDatum.property
  change cellMap owner (chainedDominionCell first owner left.normalize.val)
    (chainedDominionCell first owner root.normalize.val) leftDatum.val =
      cellMap owner (chainedDominionCell first owner right.normalize.val)
        (chainedDominionCell first owner root.normalize.val) rightDatum.val at same
  simp only [FolioData.ValidElement.normalize, ownedCellNormalization pages valid twoPages] at same
  simp only [chainedDominionCell, leftOrigin, rightOrigin, atOrigin, if_false, if_true] at same leftAccepted rightAccepted
  have positions := cellDisjoint owner _ _ leftDatum.val rightDatum.val leftAccepted rightAccepted same
  rw [chainedRegionPosition pages valid twoPages first owner sameChain left.val (left.traceValid valid) (by omega),
    chainedRegionPosition pages valid twoPages first owner sameChain right.val (right.traceValid valid) (by omega)] at positions
  exact distinct positions

def chainedDominionLaws (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (first : final.Carrier) (owner : Chain final.Carrier)
    (sameChain : owner = final.chain) (D : Dominion final.Carrier) :
    (chainedDominionAction pages valid twoPages first owner D).Laws where
  identity := chainedIdentity pages valid twoPages first owner D
  composition := chainedComposition pages valid twoPages first owner D
  coherence := chainedCoherence pages valid twoPages first owner D
  disjoint := chainedDisjoint pages valid twoPages first owner sameChain D

-- ALIGN: CHAINED-OWNED-PRESENTATION.
def chainedDominionPresentation (pagination : Pagination) (twoPages : pagination.pages.length = 2)
    (first : pagination.final.Carrier) (owner : Chain pagination.final.Carrier)
    (sameChain : owner = pagination.final.chain) (D : Dominion pagination.final.Carrier) : AtlasPresentation :=
  AtlasPresentation.ofAction pagination
    (chainedDominionAction pagination.pages pagination.folio.valid twoPages first owner D)
    (chainedDominionLaws pagination.pages pagination.folio.valid twoPages first owner sameChain D)

-- ALIGN: CHAINED-TWO-PAGE-FOLIO.
def chainedDominionFolio (first : A) (owner : Chain A) :
    Folio ⟨Unit, Chain.singletonChain⟩ ⟨A, owner⟩ := (Folio.extendOrigin owner first).pages

theorem chainedDominionFolio_length (first : A) (owner : Chain A) :
    (chainedDominionFolio first owner).data.length = 2 := (Folio.extendOrigin owner first).length

end Datra.Executable.ChainedDominionAtlas
