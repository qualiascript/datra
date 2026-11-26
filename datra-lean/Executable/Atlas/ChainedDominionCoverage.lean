import Executable.Atlas.ChainedDominionOwner
import Executable.Atlas.Map

namespace Datra.Executable.ChainedDominionAtlas
open CategoryTheory
variable {A Owner : Type}

/-- Read the tagged runtime datum from the allocated accepted carrier. -/
def rawDatum (owner : RetainedAtlas Owner A)
    {source : (chainedDominionAtlas owner).toAtlas.Element}
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    ChainedDominionCellData A source.val.cell.Carrier :=
  cast (congrFun (chainedDominionAtlas_cellData owner) source.val.cell)
    (((chainedDominionAtlas owner).acceptedCarrierEquiv source) datum).val

theorem rawDatum_accepts (owner : RetainedAtlas Owner A)
    {source : (chainedDominionAtlas owner).toAtlas.Element}
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    chainedDominionAccepts (chainedDominionFirst owner) (chainedDominionChain owner)
      source.val (rawDatum owner datum) = true := by
  exact (chainedDominionMembership owner source.val
    (((chainedDominionAtlas owner).acceptedCarrierEquiv source) datum).val).symm.trans
      (((chainedDominionAtlas owner).acceptedCarrierEquiv source) datum).property

/-- Repackage a checked tagged datum without changing its value. -/
def acceptedDatum (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : ChainedDominionCellData A source.val.cell.Carrier)
    (accepted : chainedDominionAccepts (chainedDominionFirst owner) (chainedDominionChain owner)
      source.val datum = true) : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell :=
  ((chainedDominionAtlas owner).acceptedCarrierEquiv source).symm
    ⟨cast (congrFun (chainedDominionAtlas_cellData owner) source.val.cell).symm datum, by
      rw [chainedDominionMembership]
      simpa using accepted⟩

@[simp] theorem rawDatum_acceptedDatum (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : ChainedDominionCellData A source.val.cell.Carrier) (accepted) :
    rawDatum owner (acceptedDatum owner source datum accepted) = datum := by
  simp [rawDatum, acceptedDatum]

/-- Select the actual allocated final page at the datum's chain position. -/
def coverageRegion (owner : RetainedAtlas Owner A) (value : A) :
    (chainedDominionAtlas owner).toAtlas.Element :=
  FolioData.ValidElement.lastElement (chainedDominionAtlas owner).toAtlas.pages
    ((chainedDominionAtlas owner).toAtlas.pagination.final.chain.chainIndexOf
      (cast (congrArg Page.Carrier (chainedDominionAtlas_final owner)).symm value))

theorem coverageRegion_page (owner : RetainedAtlas Owner A) (value : A) :
    (coverageRegion owner value).val.page = 1 := by
  have length := chainedDominionAtlas_length owner
  have depth := (chainedDominionAtlas owner).atlasDescription.pagination.pages.length_eq_depth
    (chainedDominionAtlas owner).atlasDescription.pagination.folio.valid
  change (chainedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1 = 1
  omega

theorem coverageRegion_position (owner : RetainedAtlas Owner A) (value : A) :
    (coverageRegion owner value).val.position = (chainedDominionChain owner).position value := by
  rcases owner with ⟨first, chain, dominion, ⟨presentation⟩, owned⟩
  obtain ⟨root, pages, twoPages, same⟩ := owned
  change presentation = _ at same
  subst presentation
  exact FolioData.ValidElement.lastElement_position pages.data (chain.chainIndexOf value)

theorem rawDatum_injective (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element) :
    Function.Injective (rawDatum owner (source := source)) := by
  intro left right same
  apply ((chainedDominionAtlas owner).acceptedCarrierEquiv source).injective
  apply Subtype.ext
  exact (Equiv.cast (congrFun (chainedDominionAtlas_cellData owner) source.val.cell)).injective same

theorem rawDatum_map (owner : RetainedAtlas Owner A)
    {source target : (chainedDominionAtlas owner).toAtlas.Element} (arrow : source ⟶ target)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    rawDatum owner (((chainedDominionAtlas owner).toAtlas.data.action.normalizedMap arrow).map datum) =
      cellMap (chainedDominionChain owner)
        (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) source.val)
        (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) target.val)
        (rawDatum owner datum) := by
  let allocation := chainedDominionAtlas owner
  letI := allocation.atlasDescription.ownership
  have mapped := AtlasMembershipAction.canonical_map allocation.atlasDescription.pagination
    allocation.atlasDescription.action allocation.atlasDescription.laws arrow datum
  exact (congrArg (cast (congrFun (chainedDominionAtlas_cellData owner) target.val.cell)) mapped).trans
    (chainedDominionTransport owner arrow (allocation.atlasDescription.action.canonicalCarrierEquiv source datum))

-- ALIGN: CHAINED-ORIGIN-IMAGE.
theorem chainedOriginImage (owner : RetainedAtlas Owner A)
    {source target : (chainedDominionAtlas owner).toAtlas.Element} (arrow : source ⟶ target)
    (atOrigin : target.val.page = 0)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    rawDatum owner (((chainedDominionAtlas owner).toAtlas.data.action.normalizedMap arrow).map datum) =
      .extent (cellValue (rawDatum owner datum)) := by
  rw [rawDatum_map]
  have accepted := rawDatum_accepts owner datum
  change cellAccepts _ _ _ = true at accepted
  have targetCell : chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner)
      target.val = .extent := by simp [chainedDominionCell, atOrigin]
  rw [targetCell]
  cases selected : chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) source.val <;>
    cases value : rawDatum owner datum <;>
    simp_all [cellMap, cellAccepts, extentAccepts, retagCell, regionToExtent, cellValue]

theorem finalRegion_normalized (owner : RetainedAtlas Owner A)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1) :
    region.normalize.val.page = (chainedDominionAtlas owner).toAtlas.coverageFinalPage := by
  have length := chainedDominionAtlas_length owner
  have depth := (chainedDominionAtlas owner).atlasDescription.pagination.pages.length_eq_depth
    (chainedDominionAtlas owner).atlasDescription.pagination.folio.valid
  change min region.val.page ((chainedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1) =
    (chainedDominionAtlas owner).atlasDescription.pagination.pages.depth - 1
  omega

def chainedRegionCoverage (owner : RetainedAtlas Owner A)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData region.val.cell) :
    (chainedDominionAtlas owner).toAtlas.CoverageWitness :=
  (chainedDominionAtlas owner).toAtlas.atlasCoverageWitness region region datum datum
    ⟨finalRegion_normalized owner region atFinal, rfl⟩

-- ALIGN: CHAINED-REGION-COVERAGE.
theorem chainedRegionCoverage_spec (owner : RetainedAtlas Owner A)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData region.val.cell) :
    (chainedDominionAtlas owner).toAtlas.coverageWitnessCovers region datum
      (chainedRegionCoverage owner region atFinal datum) = true := by
  have normalized := ((chainedDominionAtlas owner).toAtlas.atlasCoverageWitness_spec region region datum datum
    ⟨finalRegion_normalized owner region atFinal, rfl⟩).2
  apply Atlas.coverageWitnessAlongArrow region.toNormalized datum
  simpa only [(chainedDominionAtlas owner).toAtlas.data.coherence] using normalized

theorem regionAt_accepts (owner : RetainedAtlas Owner A)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (value : A)
    (atFinal : region.val.page = 1)
    (position : region.val.position = (chainedDominionChain owner).position value) :
    chainedDominionAccepts (Object := region.val.cell.Carrier) (chainedDominionFirst owner)
      (chainedDominionChain owner) region.val (.region value) = true := by
  simp [chainedDominionAccepts, chainedDominionCell, atFinal, chainValueAt, position,
    Chain.chainIndex_position, Chain.chainIndexOf, cellAccepts, regionAccepts]

def chainedCoverageAt (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (position : region.val.position = (chainedDominionChain owner).position (cellValue (rawDatum owner datum))) :
    (chainedDominionAtlas owner).toAtlas.CoverageWitness :=
  chainedRegionCoverage owner region atFinal
    (acceptedDatum owner region (.region (cellValue (rawDatum owner datum)))
      (regionAt_accepts owner region _ atFinal position))

-- ALIGN: CHAINED-COVERAGE-AT.
theorem chainedCoverageAt_spec (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell)
    (region : (chainedDominionAtlas owner).toAtlas.Element) (atFinal : region.val.page = 1)
    (position : region.val.position = (chainedDominionChain owner).position (cellValue (rawDatum owner datum))) :
    (chainedDominionAtlas owner).toAtlas.coverageWitnessCovers source datum
      (chainedCoverageAt owner source datum region atFinal position) = true := by
  let regionDatum := acceptedDatum owner region (.region (cellValue (rawDatum owner datum)))
    (regionAt_accepts owner region _ atFinal position)
  have same : (chainedDominionAtlas owner).toAtlas.originImage source datum =
      (chainedDominionAtlas owner).toAtlas.originImage region regionDatum := by
    apply rawDatum_injective owner
    have sourceImage := chainedOriginImage owner source.toOrigin rfl datum
    have regionImage := chainedOriginImage owner region.toOrigin rfl regionDatum
    exact sourceImage.trans (by simpa [regionDatum, cellValue] using regionImage.symm)
  have covered := chainedRegionCoverage_spec owner region atFinal regionDatum
  simpa only [Atlas.coverageWitnessCovers, Atlas.originImageRank, same] using covered

def chainedDominionCoverage (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (chainedDominionAtlas owner).toAtlas.CoverageWitness :=
  chainedCoverageAt owner source datum (coverageRegion owner (cellValue (rawDatum owner datum)))
    (coverageRegion_page owner _) (coverageRegion_position owner _)

-- ALIGN: CHAINED-OWNER-COVERAGE.
theorem chainedDominionCoverage_spec (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (chainedDominionAtlas owner).toAtlas.coverageWitnessCovers source datum
      (chainedDominionCoverage owner source datum) = true :=
  chainedCoverageAt_spec owner source datum _ _ _

-- ALIGN: CHAINED-OWNER-COVERAGE-MAP.
def chainedDominionAtlasMap (owner : RetainedAtlas Owner A) :
    AtlasMap (chainedDominionAtlas owner).toAtlas :=
  AtlasMap.atlasMap (chainedDominionAtlas owner).toAtlas (fun datum =>
    let covers := chainedDominionCoverage_spec owner _ datum
    ⟨chainedDominionCoverage owner _ datum, Atlas.coverageWitnessCovers_valid covers, covers⟩)

end Datra.Executable.ChainedDominionAtlas
