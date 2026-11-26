import Executable.Atlas.RankedDominion
import Executable.Atlas.ChainedDominionPresentation

namespace Datra.Executable.RankedDominionAtlas
open CategoryTheory
universe u
variable {A : Type} {Scope : Type*} {scope : Scope} {origin final : Page}

-- ALIGN: RANKED-ARROW-COMPATIBLE.
theorem arrowCompatible (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) {source target : PageElement scope}
    (arrow : source.Arrow target) (sourceValid : pages.traceValid source = true)
    (targetValid : pages.traceValid target = true) : cellPrecedes (cellAt source) (cellAt target) = true := by
  by_cases sourceOrigin : source.page = 0
  · have targetOrigin : target.page = 0 := by
      have order := arrow.precedes
      simp only [PageElement.precedes, sourceOrigin] at order
      omega
    simp [cellAt, sourceOrigin, targetOrigin, cellPrecedes]
  by_cases targetOrigin : target.page = 0
  · simp [cellAt, sourceOrigin, targetOrigin, cellPrecedes]
  have same := ChainedDominionAtlas.twoPageArrowPosition pages valid twoPages arrow
    sourceValid targetValid (by omega) (by omega)
  simp [cellAt, sourceOrigin, targetOrigin, cellPrecedes, same]

-- ALIGN: RANKED-REGION-POSITION.
theorem regionPosition (pages : FolioData origin ⟨Nat, Chain.spine⟩) (valid : pages.Valid)
    (twoPages : pages.length = 2) (occurrence : PageElement scope)
    (accepted : pages.traceValid occurrence = true) (positive : 0 < occurrence.page) :
    Ordinal.finiteOrdinal (spineRank occurrence.position) = occurrence.position := by
  have finite := ChainedDominionAtlas.chainedRegionPosition pages valid twoPages 0 Chain.spine rfl
    occurrence accepted positive
  change Ordinal.finiteOrdinal _ = occurrence.position at finite
  have index := congrArg spineRank finite
  rw [spineRank_finite] at index
  rw [← index]
  exact finite

-- ALIGN: RANKED-OWNED-NORMALIZATION.
theorem ownedCellNormalization (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (occurrence : PageElement scope) :
    cellAt (occurrence.normalize (pages.depth - 1) pages.depth) = cellAt occurrence := by
  have depth : pages.depth = 2 := (pages.length_eq_depth valid).symm.trans twoPages
  simpa only [depth, Nat.reduceSub] using cellAt_normalize occurrence

-- ALIGN: RANKED-PRESENTATION-DOMINION.
def rankedDominionAt (owner : Dominion A) (occurrence : PageElement scope) :
    Dominion (CellCarrier owner (cellAt occurrence) occurrence.cell.Carrier) :=
  cellDominion owner (cellAt occurrence)

-- ALIGN: RANKED-PRESENTATION-INSERTION.
def rankedDominionDataMap {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (owner : Dominion A) {source target : PageElement scope} (arrow : source.Arrow target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true) :
    DomanialInsertion (CellCarrier owner (cellAt source) Source) (CellCarrier owner (cellAt target) Target) :=
  cellInsertion owner _ _ (arrowCompatible pages valid twoPages arrow sourceValid targetValid)

-- ALIGN: RANKED-PRESENTATION-FORWARD.
theorem rankedDominionDataMap_map {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (owner : Dominion A) {source target : PageElement scope} (arrow : source.Arrow target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true)
    (datum : CellCarrier owner (cellAt source) Source) :
    ((rankedDominionDataMap (Target := Target) pages valid twoPages owner arrow sourceValid targetValid).map datum).val =
      cellMap (cellAt source) (cellAt target) datum.val := rfl

-- ALIGN: RANKED-PRESENTATION-INVERSE.
theorem rankedDominionDataMap_preimage {Source Target : Type}
    (pages : FolioData origin final) (valid : pages.Valid) (twoPages : pages.length = 2)
    (owner : Dominion A) {source target : PageElement scope} (arrow : source.Arrow target)
    (sourceValid : pages.traceValid source = true) (targetValid : pages.traceValid target = true)
    (datum : CellCarrier owner (cellAt target) Target) :
    ((rankedDominionDataMap (Source := Source) pages valid twoPages owner arrow sourceValid targetValid).preimage datum).map
      (fun value => value.val) = cellPreimage owner (cellAt source) (cellAt target) datum.val :=
  cellInsertion_preimage owner _ _ _ datum

-- ALIGN: RANKED-PRESENTATION-ACTION.
def rankedDominionAction (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A) :
    AtlasMembershipAction pages (fun cell => RankedDominionCellData A cell.Carrier) :=
  AtlasMembershipAction.packagePredicate (PageElementDomain.ofFolio pages ⟨pages, valid⟩)
    (fun occurrence datum => rankedDominionAccepts owner occurrence datum)
    (fun occurrence _ => rankedDominionAt owner occurrence)
    (fun sourceValid targetValid arrow =>
      rankedDominionDataMap pages valid twoPages owner arrow sourceValid targetValid)

instance rankedDominionAction_owner (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A) :
    (rankedDominionAction pages valid twoPages owner).FolioOwner := ⟨valid, rfl⟩

theorem rankedAction_map (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A)
    {source target : pages.ValidElement} (arrow : source ⟶ target)
    (datum : (rankedDominionAction pages valid twoPages owner).membership.Carrier source.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap arrow).map datum).val =
      cellMap (cellAt source.val) (cellAt target.val) datum.val := by
  change cellMap (cellAt source.normalize.val) (cellAt target.normalize.val) datum.val = _
  simp only [FolioData.ValidElement.normalize, ownedCellNormalization pages valid twoPages]

theorem rankedAction_preimage (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A)
    {source target : pages.ValidElement} (arrow : source ⟶ target)
    (datum : (rankedDominionAction pages valid twoPages owner).membership.Carrier target.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap arrow).preimage datum).map
        (fun value => value.val) = cellPreimage owner (cellAt source.val) (cellAt target.val) datum.val := by
  have exactInverse := cellInsertion_preimage (Source := source.val.cell.Carrier) owner
    (cellAt source.normalize.val) (cellAt target.normalize.val)
    (arrowCompatible pages valid twoPages (FolioData.ValidElement.normalizeArrow arrow)
      (source.normalize.traceValid valid) (target.normalize.traceValid valid)) datum
  simpa only [FolioData.ValidElement.normalize, ownedCellNormalization pages valid twoPages] using exactInverse

-- ALIGN: RANKED-PRESENTATION-IDENTITY.
theorem rankedIdentity (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A) (source : pages.ValidElement)
    (datum : (rankedDominionAction pages valid twoPages owner).membership.Carrier source.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap (𝟙 source)).map datum).val = datum.val :=
  cellIdentity _ datum.val

-- ALIGN: RANKED-PRESENTATION-COMPOSITION.
theorem rankedComposition (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A)
    {source middle target : pages.ValidElement} (before : source ⟶ middle) (after : middle ⟶ target)
    (datum : (rankedDominionAction pages valid twoPages owner).membership.Carrier source.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap (before ≫ after)).map datum).val =
      (((rankedDominionAction pages valid twoPages owner).normalizedMap after).map
        (((rankedDominionAction pages valid twoPages owner).normalizedMap before).map datum)).val :=
  (cellComposition _ _ _
    (arrowCompatible pages valid twoPages (FolioData.ValidElement.normalizeArrow before)
      (source.normalize.traceValid valid) (middle.normalize.traceValid valid))
    (arrowCompatible pages valid twoPages (FolioData.ValidElement.normalizeArrow after)
      (middle.normalize.traceValid valid) (target.normalize.traceValid valid)) datum.val).symm

-- ALIGN: RANKED-PRESENTATION-COHERENCE.
theorem rankedCoherence (pages : FolioData origin final) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A) (source : pages.ValidElement)
    (datum : (rankedDominionAction pages valid twoPages owner).membership.Carrier source.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap source.toNormalized).map datum).val = datum.val := by
  change cellMap (cellAt source.normalize.val) (cellAt source.normalize.normalize.val) datum.val = datum.val
  rw [FolioData.ValidElement.normalize_idempotent]
  exact cellIdentity _ datum.val

-- ALIGN: RANKED-PRESENTATION-DISJOINT.
theorem rankedDisjoint (pages : FolioData origin ⟨Nat, Chain.spine⟩) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A)
    {left right root : pages.ValidElement} (samePage : left.val.page = right.val.page)
    (distinct : left.val.position ≠ right.val.position) (_bounded : left.val.page ≤ pages.depth - 1)
    (atOrigin : root.val.page = 0) (leftArrow : left ⟶ root) (rightArrow : right ⟶ root)
    (leftDatum : (rankedDominionAction pages valid twoPages owner).membership.Carrier left.normalize.val)
    (rightDatum : (rankedDominionAction pages valid twoPages owner).membership.Carrier right.normalize.val) :
    (((rankedDominionAction pages valid twoPages owner).normalizedMap leftArrow).map leftDatum).val ≠
      (((rankedDominionAction pages valid twoPages owner).normalizedMap rightArrow).map rightDatum).val := by
  intro same
  by_cases leftOrigin : left.val.page = 0
  · have l := leftArrow.samePagePosition (left.traceValid valid |> pages.traceValid_shape valid left.val)
      (root.traceValid valid |> pages.traceValid_shape valid root.val) (leftOrigin.trans atOrigin.symm)
    have r := rightArrow.samePagePosition (right.traceValid valid |> pages.traceValid_shape valid right.val)
      (root.traceValid valid |> pages.traceValid_shape valid root.val) (samePage.symm.trans (leftOrigin.trans atOrigin.symm))
    exact distinct (l.trans r.symm)
  have rightOrigin : right.val.page ≠ 0 := by omega
  have leftAccepted : cellAccepts owner (cellAt left.val) leftDatum.val = true := by
    simpa only [rankedDominionAction, AtlasMembershipAction.packagePredicate, AtlasMembershipAction.package,
      AtlasMembership.accepts, rankedDominionAccepts, FolioData.ValidElement.normalize,
      ownedCellNormalization pages valid twoPages] using leftDatum.property
  have rightAccepted : cellAccepts owner (cellAt right.val) rightDatum.val = true := by
    simpa only [rankedDominionAction, AtlasMembershipAction.packagePredicate, AtlasMembershipAction.package,
      AtlasMembership.accepts, rankedDominionAccepts, FolioData.ValidElement.normalize,
      ownedCellNormalization pages valid twoPages] using rightDatum.property
  change cellMap (cellAt left.normalize.val) (cellAt root.normalize.val) leftDatum.val =
    cellMap (cellAt right.normalize.val) (cellAt root.normalize.val) rightDatum.val at same
  simp only [FolioData.ValidElement.normalize, ownedCellNormalization pages valid twoPages] at same
  simp only [cellAt, leftOrigin, rightOrigin, atOrigin, if_false, if_true] at same leftAccepted rightAccepted
  have ranks := cellDisjoint owner _ _ leftDatum.val rightDatum.val leftAccepted rightAccepted same
  apply distinct
  rw [← regionPosition pages valid twoPages left.val (left.traceValid valid) (by omega),
    ← regionPosition pages valid twoPages right.val (right.traceValid valid) (by omega), ranks]

def rankedDominionLaws (pages : FolioData origin ⟨Nat, Chain.spine⟩) (valid : pages.Valid)
    (twoPages : pages.length = 2) (owner : Dominion A) :
    (rankedDominionAction pages valid twoPages owner).Laws where
  identity := rankedIdentity pages valid twoPages owner
  composition := rankedComposition pages valid twoPages owner
  coherence := rankedCoherence pages valid twoPages owner
  disjoint := rankedDisjoint pages valid twoPages owner

-- ALIGN: RANKED-TWO-PAGE-FOLIO.
def rankedDominionFolio : Folio ⟨Unit, Chain.singletonChain⟩ ⟨Nat, Chain.spine⟩ :=
  (Folio.extendOrigin Chain.spine 0).pages

theorem rankedDominionFolio_length : rankedDominionFolio.data.length = 2 :=
  (Folio.extendOrigin Chain.spine 0).length

-- ALIGN: RANKED-PAGINATION.
def rankedDominionPagination : Pagination := Pagination.fromPageElements rankedDominionFolio

-- ALIGN: RANKED-OWNED-PRESENTATION.
def rankedPresentationForPages (pagination : Pagination) (twoPages : pagination.pages.length = 2)
    (finalSpine : pagination.final = ⟨Nat, Chain.spine⟩) (owner : Dominion A) : AtlasPresentation := by
  rcases pagination with ⟨origin, final, folio⟩
  dsimp at finalSpine twoPages
  subst final
  exact AtlasPresentation.ofAction ⟨origin, ⟨Nat, Chain.spine⟩, folio⟩
    (rankedDominionAction folio.data folio.valid twoPages owner)
    (owner := rankedDominionAction_owner folio.data folio.valid twoPages owner)
    (rankedDominionLaws folio.data folio.valid twoPages owner)

-- ALIGN: RANKED-FIXED-PRESENTATION.
def rankedDominionPresentation (owner : Dominion A) : AtlasPresentation :=
  rankedPresentationForPages rankedDominionPagination rankedDominionFolio_length rfl owner

/-- The allocated executable Atlas uses exactly the accepted cell action of
the ranked presentation. The general Atlas bridge interprets it into the
written finite Atlas category. -/
def rankedDominionInterpretation (owner : Dominion A) :
    let presentation := rankedDominionPresentation owner
    letI := presentation.ownership
    presentation.allocate.data.toFunctor ≅ presentation.action.acceptedFunctor presentation.laws :=
  (rankedDominionPresentation owner).allocateFunctorIso

structure RetainedAtlas (Owner A : Type) where
  storedDominion : Dominion A
  storedAtlas : AtlasAllocation Owner
  owned : storedAtlas.atlasDescription = rankedDominionPresentation storedDominion

-- ALIGN: RANKED-OWNER-DOMINION.
def rankedDominionValueDominion {Owner : Type} (owner : RetainedAtlas Owner A) : Dominion A :=
  owner.storedDominion

-- ALIGN: RANKED-OWNER-RETAIN.
def retainRankedDominionAtlas {Owner : Type} (dominion : Dominion A) (allocation : AtlasAllocation Owner)
    (owned : allocation.atlasDescription = rankedDominionPresentation dominion) : RetainedAtlas Owner A :=
  ⟨dominion, allocation, owned⟩

-- ALIGN: RANKED-OWNER-ATLAS.
def rankedDominionAtlas {Owner : Type} (owner : RetainedAtlas Owner A) : AtlasAllocation Owner :=
  owner.storedAtlas

-- ALIGN: RANKED-OWNER-CONTRACT.
theorem rankedDominionAtlas_description {Owner : Type} (owner : RetainedAtlas Owner A) :
    (rankedDominionAtlas owner).atlasDescription = rankedDominionPresentation owner.storedDominion :=
  owner.owned

theorem rankedDominionAtlas_length {Owner : Type} (owner : RetainedAtlas Owner A) :
    (rankedDominionAtlas owner).atlasDescription.pagination.pages.length = 2 := by
  rw [rankedDominionAtlas_description]
  exact rankedDominionFolio_length

theorem rankedDominionAtlas_final {Owner : Type} (owner : RetainedAtlas Owner A) :
    (rankedDominionAtlas owner).atlasDescription.pagination.final = ⟨Nat, Chain.spine⟩ := by
  rw [rankedDominionAtlas_description]
  rfl

theorem rankedDominionAtlas_cellData {Owner : Type} (owner : RetainedAtlas Owner A) :
    (rankedDominionAtlas owner).atlasDescription.cellData =
      (fun cell => RankedDominionCellData A cell.Carrier) := by
  rw [rankedDominionAtlas_description]
  rfl

-- ALIGN: RANKED-OWNER-MEMBERSHIP.
theorem rankedDominionMembership {Owner : Type} (owner : RetainedAtlas Owner A)
    (occurrence : PageElement (rankedDominionAtlas owner).atlasDescription.pagination.pages)
    (datum : (rankedDominionAtlas owner).atlasDescription.cellData occurrence.cell) :
    (rankedDominionAtlas owner).acceptsDatum occurrence datum =
      rankedDominionAccepts owner.storedDominion occurrence
        (cast (congrFun (rankedDominionAtlas_cellData owner) occurrence.cell) datum) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  change cellAccepts dominion (cellAt (occurrence.normalize
    (rankedDominionFolio.data.depth - 1) rankedDominionFolio.data.depth)) datum =
      cellAccepts dominion (cellAt occurrence) datum
  rw [ownedCellNormalization rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length]

-- ALIGN: RANKED-OWNER-LOOKUP-RANK.
theorem rankedDominionDataAt_rank {Owner : Type} (owner : RetainedAtlas Owner A) :
    let allocation := rankedDominionAtlas owner
    letI := allocation.atlasDescription.ownership
    ∀ (occurrence : allocation.atlasDescription.pagination.pages.ValidElement)
      (datum : allocation.atlasDescription.action.membership.Carrier occurrence.normalize.val),
      (allocation.atlasDescription.action.dataAtValid occurrence.normalize).rank datum =
        cellRank owner.storedDominion (cellAt occurrence.val)
          (cast (congrFun (rankedDominionAtlas_cellData owner) occurrence.val.cell) datum.val) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  dsimp only
  intro occurrence datum
  change cellRank dominion (cellAt occurrence.normalize.val) datum.val = _
  exact congrArg (fun cell => cellRank dominion cell datum.val)
    (ownedCellNormalization rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length occurrence.val)

-- ALIGN: RANKED-OWNER-LOOKUP-DECODE.
theorem rankedDominionDataAt_unrank {Owner : Type} (owner : RetainedAtlas Owner A) :
    let allocation := rankedDominionAtlas owner
    letI := allocation.atlasDescription.ownership
    ∀ (occurrence : allocation.atlasDescription.pagination.pages.ValidElement) (index : Nat),
      ((allocation.atlasDescription.action.dataAtValid occurrence.normalize).unrank index).map
          (fun datum => cast (congrFun (rankedDominionAtlas_cellData owner) occurrence.val.cell) datum.val) =
        cellUnrank owner.storedDominion (cellAt occurrence.val) index := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  dsimp only
  intro occurrence index
  change ((cellDominion dominion (cellAt occurrence.normalize.val)).unrank index).map Subtype.val =
    (cellUnrank dominion (cellAt occurrence.val) index : Option (RankedDominionCellData A occurrence.val.cell.Carrier))
  rw [cellDominion_unrank]
  exact congrArg (fun cell => cellUnrank dominion cell index)
    (ownedCellNormalization rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length occurrence.val)

-- ALIGN: RANKED-OWNER-TRANSPORT.
theorem rankedDominionTransport {Owner : Type} (owner : RetainedAtlas Owner A) :
    let allocation := rankedDominionAtlas owner
    letI := allocation.atlasDescription.ownership
    ∀ {source target : allocation.atlasDescription.pagination.pages.ValidElement}
      (arrow : source ⟶ target)
      (datum : allocation.atlasDescription.action.membership.Carrier source.normalize.val),
      cast (congrFun (rankedDominionAtlas_cellData owner) target.val.cell)
        ((allocation.atlasDescription.action.normalizedMap arrow).map datum).val =
      cellMap (cellAt source.val) (cellAt target.val)
        (cast (congrFun (rankedDominionAtlas_cellData owner) source.val.cell) datum.val) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  dsimp only
  intro source target arrow datum
  exact rankedAction_map rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length
    dominion arrow datum

-- ALIGN: RANKED-OWNER-INVERSE-TRANSPORT.
theorem rankedDominionInverseTransport {Owner : Type} (owner : RetainedAtlas Owner A) :
    let allocation := rankedDominionAtlas owner
    letI := allocation.atlasDescription.ownership
    ∀ {source target : allocation.atlasDescription.pagination.pages.ValidElement}
      (arrow : source ⟶ target)
      (datum : allocation.atlasDescription.action.membership.Carrier target.normalize.val),
      ((allocation.atlasDescription.action.normalizedMap arrow).preimage datum).map
          (fun result => cast (congrFun (rankedDominionAtlas_cellData owner) source.val.cell) result.val) =
        cellPreimage owner.storedDominion (cellAt source.val) (cellAt target.val)
          (cast (congrFun (rankedDominionAtlas_cellData owner) target.val.cell) datum.val) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  dsimp only
  intro source target arrow datum
  exact rankedAction_preimage rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length
    dominion arrow datum

-- ALIGN: RANKED-OWNER-RETAIN-PRESENTATION.
def retainRankedPresentation {Owner : Type} (dominion : Dominion A) (presentation : AtlasPresentation)
    (canonical : presentation = rankedDominionPresentation dominion) (allocation : AtlasAllocation Owner)
    (owned : allocation.atlasDescription = presentation) : RetainedAtlas Owner A :=
  retainRankedDominionAtlas dominion allocation (owned.trans canonical)

-- ALIGN: RANKED-OWNER-ALLOCATION.
def withRankedDominionAtlas {Result : Type u} (owner : Dominion A)
    (useOwner : ∀ Owner : Type, RetainedAtlas Owner A → Result) : Result :=
  useOwner Unit (retainRankedPresentation owner (rankedDominionPresentation owner) rfl
    (rankedDominionPresentation owner).allocateStored rfl)

theorem withRankedDominionAtlas_dominion (owner : Dominion A) :
    withRankedDominionAtlas owner (fun _ retained => retained.storedDominion) = owner := rfl

end Datra.Executable.RankedDominionAtlas
