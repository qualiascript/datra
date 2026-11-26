import Executable.Atlas.ChainedDominionCoverage
import Executable.Atlas.Coalition

namespace Datra.Executable.ChainedDominionAtlas
variable {A Owner : Type}

-- ALIGN: CHAINED-COALITION-VIEW-VALUE.
def chainedViewValue (owner : RetainedAtlas Owner A)
    (view : (chainedDominionAtlas owner).toAtlas.CoalitionView) : A :=
  cellValue (rawDatum owner view.2)

-- ALIGN: CHAINED-COALITION-VALUE.
def chainedCoalitionValue (owner : RetainedAtlas Owner A)
    (element : (chainedDominionAtlas owner).toAtlas.CoalitionElement) : A :=
  chainedViewValue owner (Atlas.viewCoalitionElement element)

theorem origin_accepts (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (atOrigin : source = FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages)
    (value : A) :
    chainedDominionAccepts (Object := source.val.cell.Carrier) (chainedDominionFirst owner)
      (chainedDominionChain owner) source.val (.extent value) = true := by
  have page : source.val.page = 0 := by rw [atOrigin]; rfl
  simp [chainedDominionAccepts, chainedDominionCell, page, cellAccepts, extentAccepts]

-- ALIGN: CHAINED-COALITION-AT.
def chainedCoalitionAt (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (atOrigin : source = FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages)
    (value : A) : (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement :=
  let datum := acceptedDatum owner source (.extent value) (origin_accepts owner source atOrigin value)
  Atlas.coalitionElement_checked source atOrigin datum
    (chainedDominionCoverage owner source datum) (chainedDominionCoverage_spec owner source datum)

theorem chainedCoalitionAt_value (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (atOrigin : source = FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages)
    (value : A) : chainedCoalitionValue owner (chainedCoalitionAt owner source atOrigin value).val = value := by
  change cellValue (rawDatum owner (acceptedDatum owner source (.extent value)
    (origin_accepts owner source atOrigin value))) = value
  rw [rawDatum_acceptedDatum]
  rfl

theorem chainedCoalitionAt_source (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (atOrigin : source = FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages)
    (value : A) : (chainedCoalitionAt owner source atOrigin value).val.source = source := rfl

-- ALIGN: CHAINED-OWNER-COALITION.
def chainedDominionCoalitionElement (owner : RetainedAtlas Owner A) (value : A) :
    (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement :=
  chainedCoalitionAt owner (FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages) rfl value

-- ALIGN: CHAINED-COALITION-VALUE-ROUNDTRIP.
theorem chainedDominionCoalitionElement_value (owner : RetainedAtlas Owner A) (value : A) :
    chainedCoalitionValue owner (chainedDominionCoalitionElement owner value).val = value :=
  chainedCoalitionAt_value owner _ rfl value

end Datra.Executable.ChainedDominionAtlas
