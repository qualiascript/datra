import Executable.Atlas.Coverage

namespace Datra.Executable.Atlas

theorem twoPageRegion_normalized (owner : Atlas) (twoPages : owner.pages.length = 2)
    (region : owner.Element) (atFinal : region.val.page = 1) :
    region.normalize.val.page = owner.coverageFinalPage := by
  have depth := owner.pages.length_eq_depth owner.pagination.folio.valid
  change min region.val.page (owner.pages.depth - 1) = owner.pages.depth - 1
  omega

def twoPageRegionCoverage (owner : Atlas) (twoPages : owner.pages.length = 2)
    (region : owner.Element) (atFinal : region.val.page = 1)
    (datum : owner.cellData region.val.cell) : owner.CoverageWitness :=
  owner.atlasCoverageWitness region region datum datum
    ⟨twoPageRegion_normalized owner twoPages region atFinal, rfl⟩

-- ALIGN: TWO-PAGE-REGION-COVERAGE.
theorem twoPageRegionCoverage_spec (owner : Atlas) (twoPages : owner.pages.length = 2)
    (region : owner.Element) (atFinal : region.val.page = 1)
    (datum : owner.cellData region.val.cell) :
    owner.coverageWitnessCovers region datum
      (owner.twoPageRegionCoverage twoPages region atFinal datum) = true := by
  have normalized := (owner.atlasCoverageWitness_spec region region datum datum
    ⟨twoPageRegion_normalized owner twoPages region atFinal, rfl⟩).2
  apply coverageWitnessAlongArrow region.toNormalized datum
  simpa only [owner.data.coherence] using normalized

end Datra.Executable.Atlas
