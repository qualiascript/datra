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

/-- The raw dependent view assembled from a page occurrence and an extent value. -/
-- ALIGN: CHAINED-COALITION-VIEW-FROM.
def chainedViewFrom {Scope : Type*} {scope : Scope} (source : PageElement scope) (value : A) :
    (source : PageElement scope) × ChainedDominionCellData A source.cell.Carrier :=
  ⟨source, .extent value⟩

-- ALIGN: CHAINED-COALITION-ORIGIN-VIEW-AT.
theorem chainedOriginViewAt (owner : RetainedAtlas Owner A)
    (source : (chainedDominionAtlas owner).toAtlas.Element)
    (atOrigin : source = FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages)
    (datum : (chainedDominionAtlas owner).toAtlas.cellData source.val.cell) :
    (⟨source.val, rawDatum owner datum⟩ :
      (x : PageElement (chainedDominionAtlas owner).toAtlas.pages) × ChainedDominionCellData A x.cell.Carrier) =
      chainedViewFrom (FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages).val
        (cellValue (rawDatum owner datum)) := by
  have page : source.val.page = 0 := by rw [atOrigin]; rfl
  have accepted := rawDatum_accepts owner datum
  have tag : rawDatum owner datum = .extent (cellValue (rawDatum owner datum)) := by
    cases value : rawDatum owner datum <;>
      simp_all [chainedDominionAccepts, chainedDominionCell, cellAccepts, extentAccepts, cellValue]
  calc
    _ = chainedViewFrom source.val (cellValue (rawDatum owner datum)) :=
      congrArg (fun d : ChainedDominionCellData A source.val.cell.Carrier =>
        (⟨source.val, d⟩ : (x : PageElement (chainedDominionAtlas owner).toAtlas.pages) ×
          ChainedDominionCellData A x.cell.Carrier)) tag
    _ = _ := congrArg (fun x => chainedViewFrom x (cellValue (rawDatum owner datum)))
      (congrArg Subtype.val atOrigin)

-- ALIGN: CHAINED-COALITION-ORIGIN-VIEW.
theorem chainedCoalitionOriginView (owner : RetainedAtlas Owner A)
    (element : (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement) :
    (⟨element.val.source.val, rawDatum owner element.val.datum⟩ :
      (x : PageElement (chainedDominionAtlas owner).toAtlas.pages) × ChainedDominionCellData A x.cell.Carrier) =
      chainedViewFrom (FolioData.ValidElement.originElement (chainedDominionAtlas owner).toAtlas.pages).val
        (chainedCoalitionValue owner element.val) :=
  chainedOriginViewAt owner element.val.source element.property.2.2 element.val.datum

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

/-- Cached coalition data is uniquely determined by its underlying extent value. -/
theorem chainedCoalitionValue_injective (owner : RetainedAtlas Owner A) :
    Function.Injective (fun element : (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement =>
      chainedCoalitionValue owner element.val) := by
  intro left right same
  apply Atlas.CertifiedCoalitionElement.ext
  apply Subtype.ext
  apply rawDatum_injective owner
  change rawDatum owner ((chainedDominionAtlas owner).toAtlas.originImage left.val.source left.val.datum) =
    rawDatum owner ((chainedDominionAtlas owner).toAtlas.originImage right.val.source right.val.datum)
  rw [Atlas.originImage, Atlas.originImage,
    chainedOriginImage owner left.val.source.toOrigin rfl,
    chainedOriginImage owner right.val.source.toOrigin rfl]
  exact congrArg ChainedDominionCellData.extent same

-- ALIGN: CHAINED-COALITION-RECONSTRUCTION.
theorem chainedCoalitionReconstruct (owner : RetainedAtlas Owner A)
    (element : (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement) :
    chainedDominionCoalitionElement owner (chainedCoalitionValue owner element.val) = element :=
  chainedCoalitionValue_injective owner (chainedDominionCoalitionElement_value owner _)

/-- The complete canonical coalition carrier is equivalent to the supplied
value carrier; the equivalence preserves the actual allocation's caches. -/
def chainedCoalitionEquiv (owner : RetainedAtlas Owner A) :
    (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement ≃ A where
  toFun element := chainedCoalitionValue owner element.val
  invFun := chainedDominionCoalitionElement owner
  left_inv := chainedCoalitionReconstruct owner
  right_inv := chainedDominionCoalitionElement_value owner

-- ALIGN: CHAINED-COALITION-FORWARD.
def chainedCoalitionForward {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) (value : Source) :
    (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement :=
  chainedDominionCoalitionElement owner (insertion.map value)

-- ALIGN: CHAINED-COALITION-BACKWARD.
def chainedCoalitionBackward {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A)
    (element : (chainedDominionAtlas owner).toAtlas.CoalitionElement) : Option Source :=
  insertion.preimage (chainedCoalitionValue owner element)

-- ALIGN: CHAINED-COALITION-INSERTION-ROUNDTRIP.
theorem chainedCoalitionRoundTrip {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) (value : Source) :
    chainedCoalitionBackward owner insertion (chainedCoalitionForward owner insertion value).val = some value := by
  unfold chainedCoalitionForward chainedCoalitionBackward
  rw [chainedDominionCoalitionElement_value, insertion.leftInverse]

-- ALIGN: CHAINED-COALITION-INSERTION.
def chainedCoalitionInsertion {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) :
    DomanialInsertion Source (chainedDominionAtlas owner).toAtlas.CertifiedCoalitionElement where
  map := chainedCoalitionForward owner insertion
  preimage element := chainedCoalitionBackward owner insertion element.val
  leftInverse := chainedCoalitionRoundTrip owner insertion

/-- Both executable directions are exactly the original insertion transported
through the coalition equivalence, including failed inverse lookups. -/
theorem chainedCoalitionInsertion_reindex {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) :
    chainedCoalitionInsertion owner insertion =
      insertion.reindex (Equiv.refl Source) (chainedCoalitionEquiv owner).symm := by
  cases insertion
  simp [chainedCoalitionInsertion, chainedCoalitionBackward,
    DomanialInsertion.reindex, chainedCoalitionEquiv]
  rfl

end Datra.Executable.ChainedDominionAtlas
