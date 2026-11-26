import Executable.Atlas.RankedDominionPresentation
import Executable.Atlas.Map

namespace Datra.Executable.RankedDominionAtlas
open CategoryTheory
variable {A Owner : Type}

/-- Read the tagged runtime datum from the allocated accepted carrier. -/
def rawDatum (owner : RetainedAtlas Owner A)
    {source : (rankedDominionAtlas owner).toAtlas.Element}
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    RankedDominionCellData A source.val.cell.Carrier :=
  cast (congrFun (rankedDominionAtlas_cellData owner) source.val.cell)
    (((rankedDominionAtlas owner).acceptedCarrierEquiv source) datum).val

theorem rawDatum_accepts (owner : RetainedAtlas Owner A)
    {source : (rankedDominionAtlas owner).toAtlas.Element}
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    rankedDominionAccepts owner.storedDominion
      source.val (rawDatum owner datum) = true := by
  exact (rankedDominionMembership owner source.val
    (((rankedDominionAtlas owner).acceptedCarrierEquiv source) datum).val).symm.trans
      (((rankedDominionAtlas owner).acceptedCarrierEquiv source) datum).property

/-- Repackage a checked tagged datum without changing its value. -/
def acceptedDatum (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : RankedDominionCellData A source.val.cell.Carrier)
    (accepted : rankedDominionAccepts owner.storedDominion
      source.val datum = true) : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell :=
  ((rankedDominionAtlas owner).acceptedCarrierEquiv source).symm
    ⟨cast (congrFun (rankedDominionAtlas_cellData owner) source.val.cell).symm datum, by
      rw [rankedDominionMembership]
      simpa using accepted⟩

@[simp] theorem rawDatum_acceptedDatum (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : RankedDominionCellData A source.val.cell.Carrier) (accepted) :
    rawDatum owner (acceptedDatum owner source datum accepted) = datum := by
  simp [rawDatum, acceptedDatum]

/-- Select the actual allocated final page at the datum's Dominion rank. -/
def coverageRegion (owner : RetainedAtlas Owner A) (value : A) :
    (rankedDominionAtlas owner).toAtlas.Element :=
  FolioData.ValidElement.lastElement (rankedDominionAtlas owner).toAtlas.pages
    ((rankedDominionAtlas owner).toAtlas.pagination.final.chain.chainIndexOf
      (cast (congrArg Page.Carrier (rankedDominionAtlas_final owner)).symm (owner.storedDominion.rank value)))

theorem coverageRegion_page (owner : RetainedAtlas Owner A) (value : A) :
    (coverageRegion owner value).val.page = 1 := by
  have length := rankedDominionAtlas_length owner
  have depth := (rankedDominionAtlas owner).atlasDescription.pagination.pages.length_eq_depth
    (rankedDominionAtlas owner).atlasDescription.pagination.folio.valid
  change (rankedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1 = 1
  omega

theorem coverageRegion_position (owner : RetainedAtlas Owner A) (value : A) :
    (coverageRegion owner value).val.position = Ordinal.finiteOrdinal (owner.storedDominion.rank value) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  exact FolioData.ValidElement.lastElement_position rankedDominionFolio.data
    (Chain.spine.chainIndexOf (dominion.rank value))

theorem rawDatum_injective (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element) :
    Function.Injective (rawDatum owner (source := source)) := by
  intro left right same
  apply ((rankedDominionAtlas owner).acceptedCarrierEquiv source).injective
  apply Subtype.ext
  exact (Equiv.cast (congrFun (rankedDominionAtlas_cellData owner) source.val.cell)).injective same

theorem rawDatum_rank (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    ((rankedDominionAtlas owner).toAtlas.dataAt source).rank datum =
      cellRank owner.storedDominion (cellAt source.val) (rawDatum owner datum) := by
  rcases owner with ⟨dominion, ⟨presentation⟩, same⟩
  change presentation = _ at same
  subst presentation
  letI := (rankedDominionPresentation dominion).ownership
  have preserved := AtlasMembershipAction.canonical_rank
    (rankedDominionPresentation dominion).pagination
    (rankedDominionPresentation dominion).action
    (rankedDominionPresentation dominion).laws source datum
  change _ = cellRank dominion (cellAt source.val) datum.val
  refine preserved.trans ?_
  change cellRank dominion (cellAt source.normalize.val) datum.val = _
  exact congrArg (fun cell => cellRank dominion cell datum.val)
    (ownedCellNormalization rankedDominionFolio.data rankedDominionFolio.valid rankedDominionFolio_length source.val)

theorem rawDatum_map (owner : RetainedAtlas Owner A)
    {source target : (rankedDominionAtlas owner).toAtlas.Element} (arrow : source ⟶ target)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    rawDatum owner (((rankedDominionAtlas owner).toAtlas.data.action.normalizedMap arrow).map datum) =
      cellMap (cellAt source.val) (cellAt target.val)
        (rawDatum owner datum) := by
  let allocation := rankedDominionAtlas owner
  letI := allocation.atlasDescription.ownership
  have mapped := AtlasMembershipAction.canonical_map allocation.atlasDescription.pagination
    allocation.atlasDescription.action allocation.atlasDescription.laws arrow datum
  exact (congrArg (cast (congrFun (rankedDominionAtlas_cellData owner) target.val.cell)) mapped).trans
    (rankedDominionTransport owner arrow (allocation.atlasDescription.action.canonicalCarrierEquiv source datum))

theorem rankedOriginImage (owner : RetainedAtlas Owner A)
    {source target : (rankedDominionAtlas owner).toAtlas.Element} (arrow : source ⟶ target)
    (atOrigin : target.val.page = 0)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    rawDatum owner (((rankedDominionAtlas owner).toAtlas.data.action.normalizedMap arrow).map datum) =
      .extent (cellValue (rawDatum owner datum)) := by
  rw [rawDatum_map]
  have accepted := rawDatum_accepts owner datum
  change cellAccepts _ _ _ = true at accepted
  have targetCell : cellAt target.val = .extent := by simp [cellAt, atOrigin]
  rw [targetCell]
  cases selected : cellAt source.val <;>
    cases value : rawDatum owner datum <;>
    simp_all [cellMap, cellAccepts, ChainedDominionAtlas.extentAccepts, ChainedDominionAtlas.retagCell, cellValue, ChainedDominionAtlas.cellValue]

theorem rankedOriginImageRank (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (rankedDominionAtlas owner).toAtlas.originImageRank source datum =
      owner.storedDominion.rank (cellValue (rawDatum owner datum)) := by
  rw [Atlas.originImageRank, rawDatum_rank]
  change cellRank owner.storedDominion .extent
    (rawDatum owner ((rankedDominionAtlas owner).toAtlas.originImage source datum)) = _
  rw [Atlas.originImage, rankedOriginImage owner source.toOrigin rfl]
  rfl

theorem finalRegion_normalized (owner : RetainedAtlas Owner A)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1) :
    region.normalize.val.page = (rankedDominionAtlas owner).toAtlas.coverageFinalPage := by
  have length := rankedDominionAtlas_length owner
  have depth := (rankedDominionAtlas owner).atlasDescription.pagination.pages.length_eq_depth
    (rankedDominionAtlas owner).atlasDescription.pagination.folio.valid
  change min region.val.page ((rankedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1) =
    (rankedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1
  omega

def rankedRegionCoverage (owner : RetainedAtlas Owner A)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData region.val.cell) :
    (rankedDominionAtlas owner).toAtlas.CoverageWitness :=
  (rankedDominionAtlas owner).toAtlas.atlasCoverageWitness region region datum datum
    ⟨finalRegion_normalized owner region atFinal, rfl⟩

theorem rankedRegionCoverage_spec (owner : RetainedAtlas Owner A)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData region.val.cell) :
    (rankedDominionAtlas owner).toAtlas.coverageWitnessCovers region datum
      (rankedRegionCoverage owner region atFinal datum) = true := by
  have normalized := ((rankedDominionAtlas owner).toAtlas.atlasCoverageWitness_spec region region datum datum
    ⟨finalRegion_normalized owner region atFinal, rfl⟩).2
  apply Atlas.coverageWitnessAlongArrow region.toNormalized datum
  simpa only [(rankedDominionAtlas owner).toAtlas.data.coherence] using normalized

theorem regionAt_accepts (owner : RetainedAtlas Owner A)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (value : A)
    (atFinal : region.val.page = 1)
    (position : region.val.position = Ordinal.finiteOrdinal (owner.storedDominion.rank value)) :
    rankedDominionAccepts (Object := region.val.cell.Carrier) owner.storedDominion region.val (.region value) = true := by
  simp [rankedDominionAccepts, cellAt, atFinal, position, spineRank_finite, cellAccepts]

def rankedCoverageAt (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (position : region.val.position = Ordinal.finiteOrdinal (owner.storedDominion.rank (cellValue (rawDatum owner datum)))) :
    (rankedDominionAtlas owner).toAtlas.CoverageWitness :=
  rankedRegionCoverage owner region atFinal
    (acceptedDatum owner region (.region (cellValue (rawDatum owner datum)))
      (regionAt_accepts owner region _ atFinal position))

theorem rankedCoverageAt_spec (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell)
    (region : (rankedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (position : region.val.position = Ordinal.finiteOrdinal (owner.storedDominion.rank (cellValue (rawDatum owner datum)))) :
    (rankedDominionAtlas owner).toAtlas.coverageWitnessCovers source datum
      (rankedCoverageAt owner source datum region atFinal position) = true := by
  let regionDatum := acceptedDatum owner region (.region (cellValue (rawDatum owner datum)))
    (regionAt_accepts owner region _ atFinal position)
  have same : (rankedDominionAtlas owner).toAtlas.originImage source datum =
      (rankedDominionAtlas owner).toAtlas.originImage region regionDatum := by
    apply rawDatum_injective owner
    have sourceImage := rankedOriginImage owner source.toOrigin rfl datum
    have regionImage := rankedOriginImage owner region.toOrigin rfl regionDatum
    exact sourceImage.trans (by simpa [regionDatum, cellValue] using regionImage.symm)
  have covered := rankedRegionCoverage_spec owner region atFinal regionDatum
  simpa only [Atlas.coverageWitnessCovers, Atlas.originImageRank, same] using covered

-- ALIGN: RANKED-OWNER-COVERAGE.
def rankedDominionCoverage (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (rankedDominionAtlas owner).toAtlas.CoverageWitness :=
  rankedCoverageAt owner source datum (coverageRegion owner (cellValue (rawDatum owner datum)))
    (coverageRegion_page owner _) (coverageRegion_position owner _)

theorem rankedDominionCoverage_spec (owner : RetainedAtlas Owner A)
    (source : (rankedDominionAtlas owner).toAtlas.Element)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (rankedDominionAtlas owner).toAtlas.coverageWitnessCovers source datum
      (rankedDominionCoverage owner source datum) = true :=
  rankedCoverageAt_spec owner source datum _ _ _

-- ALIGN: RANKED-OWNER-COVERAGE-MAP.
def rankedDominionAtlasMap (owner : RetainedAtlas Owner A) :
    AtlasMap (rankedDominionAtlas owner).toAtlas :=
  AtlasMap.atlasMap (rankedDominionAtlas owner).toAtlas (fun datum =>
    let covers := rankedDominionCoverage_spec owner _ datum
    ⟨rankedDominionCoverage owner _ datum, Atlas.coverageWitnessCovers_valid covers, covers⟩)

end Datra.Executable.RankedDominionAtlas
