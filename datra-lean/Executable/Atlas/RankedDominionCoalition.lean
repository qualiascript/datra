import Executable.Atlas.RankedDominionCoverage
import Executable.Atlas.Coalition
import Executable.Atlas.DomanialInclusion

namespace Datra.Executable.RankedDominionAtlas
open CategoryTheory
variable {A Owner : Type}

def rankedCoalitionValue (owner : RetainedAtlas Owner A)
    (element : (rankedDominionAtlas owner).toAtlas.CoalitionElement) : A :=
  cellValue (rawDatum owner element.datum)

theorem origin_accepts (owner : RetainedAtlas Owner A) (value : A) :
    rankedDominionAccepts (Object := (FolioData.ValidElement.originElement
      (rankedDominionAtlas owner).toAtlas.pages).val.cell.Carrier) owner.storedDominion
      (FolioData.ValidElement.originElement (rankedDominionAtlas owner).toAtlas.pages).val (.extent value) = true :=
  rfl

-- ALIGN: RANKED-OWNER-COALITION.
def rankedDominionCoalitionElement (owner : RetainedAtlas Owner A) (value : A) :
    (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement :=
  let source := FolioData.ValidElement.originElement (rankedDominionAtlas owner).toAtlas.pages
  let datum := acceptedDatum owner source (.extent value) (origin_accepts owner value)
  Atlas.coalitionElement_checked source rfl datum
    (rankedDominionCoverage owner source datum) (rankedDominionCoverage_spec owner source datum)

theorem rankedDominionCoalitionElement_value (owner : RetainedAtlas Owner A) (value : A) :
    rankedCoalitionValue owner (rankedDominionCoalitionElement owner value).val = value := by
  change cellValue (rawDatum owner (acceptedDatum owner _ (.extent value) (origin_accepts owner value))) = value
  rw [rawDatum_acceptedDatum]
  rfl

theorem rankedCoalitionRank (owner : RetainedAtlas Owner A)
    (element : (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement) :
    element.val.originRank = owner.storedDominion.rank (rankedCoalitionValue owner element.val) :=
  element.property.2.1.trans (rankedOriginImageRank owner element.val.source element.val.datum)

theorem rankedDominionCoalitionElement_rank (owner : RetainedAtlas Owner A) (value : A) :
    (rankedDominionCoalitionElement owner value).val.originRank = owner.storedDominion.rank value := by
  rw [rankedCoalitionRank, rankedDominionCoalitionElement_value]

theorem rankedCoalitionValue_injective (owner : RetainedAtlas Owner A) :
    Function.Injective (fun element : (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement =>
      rankedCoalitionValue owner element.val) := by
  intro left right same
  apply Atlas.CertifiedCoalitionElement.ext
  apply Subtype.ext
  apply rawDatum_injective owner
  change rawDatum owner ((rankedDominionAtlas owner).toAtlas.originImage left.val.source left.val.datum) =
    rawDatum owner ((rankedDominionAtlas owner).toAtlas.originImage right.val.source right.val.datum)
  rw [Atlas.originImage, Atlas.originImage,
    rankedOriginImage owner left.val.source.toOrigin rfl,
    rankedOriginImage owner right.val.source.toOrigin rfl]
  exact congrArg ChainedDominionCellData.extent same

def rankedCoalitionEquiv (owner : RetainedAtlas Owner A) :
    (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement ≃ A where
  toFun element := rankedCoalitionValue owner element.val
  invFun := rankedDominionCoalitionElement owner
  left_inv _ := rankedCoalitionValue_injective owner (rankedDominionCoalitionElement_value owner _)
  right_inv := rankedDominionCoalitionElement_value owner

/-- Decode the stored origin rank before invoking the supplied partial inverse.
This definition also retains the runtime behavior on uncertified raw records. -/
def rankedCoalitionBackward {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A)
    (element : (rankedDominionAtlas owner).toAtlas.CoalitionElement) : Option Source :=
  (owner.storedDominion.unrank element.originRank).bind insertion.preimage

theorem rankedCoalitionBackward_valid {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A)
    (element : (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement) :
    rankedCoalitionBackward owner insertion element.val = insertion.preimage (rankedCoalitionValue owner element.val) := by
  simp [rankedCoalitionBackward, rankedCoalitionRank owner element, owner.storedDominion.coherence]

-- ALIGN: RANKED-COALITION-INSERTION.
def rankedCoalitionInsertion {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) :
    DomanialInsertion Source (rankedDominionAtlas owner).toAtlas.CertifiedCoalitionElement where
  map value := rankedDominionCoalitionElement owner (insertion.map value)
  preimage element := rankedCoalitionBackward owner insertion element.val
  leftInverse value := by
    rw [rankedCoalitionBackward_valid, rankedDominionCoalitionElement_value, insertion.leftInverse]

theorem rankedCoalitionInsertion_reindex {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) :
    rankedCoalitionInsertion owner insertion =
      insertion.reindex (Equiv.refl Source) (rankedCoalitionEquiv owner).symm := by
  apply DomanialInsertion.ext
  · rfl
  · funext element
    simpa [rankedCoalitionInsertion, DomanialInsertion.reindex, rankedCoalitionEquiv] using
      rankedCoalitionBackward_valid owner insertion element

def rankedValueInsertion {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) :
    DomanialInsertion Source (rankedDominionAtlas owner).toAtlas.CoalitionValue :=
  (rankedCoalitionInsertion owner insertion).reindex (Equiv.refl Source)
    (Atlas.coalitionValueEquiv (rankedDominionAtlas owner).toAtlas)

def rankedComponentBackward {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A)
    (datum : (rankedDominionAtlas owner).toAtlas.cellData
      (FolioData.ValidElement.originElement (rankedDominionAtlas owner).toAtlas.pages).val.cell) : Option Source :=
  insertion.preimage (cellValue (rawDatum owner datum))

theorem rankedComponentLeftInverse {Source : Type} (owner : RetainedAtlas Owner A)
    (insertion : DomanialInsertion Source A) (value : Source) :
    rankedComponentBackward owner insertion ((rankedValueInsertion owner insertion).map value).val = some value := by
  let element := rankedDominionCoalitionElement owner (insertion.map value)
  change insertion.preimage (cellValue (rawDatum owner
    ((rankedDominionAtlas owner).toAtlas.originImage element.val.source element.val.datum))) = some value
  rw [Atlas.originImage, rankedOriginImage owner element.val.source.toOrigin rfl]
  change insertion.preimage (rankedCoalitionValue owner element.val) = some value
  rw [rankedDominionCoalitionElement_value, insertion.leftInverse]

-- ALIGN: RANKED-INSERTION-TRAVERSAL.
def rankedDominionInsertionTraversal {Source : Type} (source : Dominion Source)
    (owner : RetainedAtlas Owner A) (insertion : DomanialInsertion Source A) :
    Atlas.StableTransversal (DomanialInclusion.dominionAtlas source) (rankedDominionAtlas owner).toAtlas :=
  DomanialInclusion.coaToDomInc source (rankedDominionAtlas owner).toAtlas
    (rankedValueInsertion owner insertion) (rankedComponentBackward owner insertion)
    (rankedComponentLeftInverse owner insertion)

theorem rankedDominionInsertionTraversal_interpretation {Source : Type} (source : Dominion Source)
    (owner : RetainedAtlas Owner A) (insertion : DomanialInsertion Source A) :
    (rankedDominionInsertionTraversal source owner insertion).toSemantics.val.val =
      DomanialInclusion.interpretationHom source ≫
        (Datra.Semantics.coaToDomInc
          (DomanialInclusion.coalitionInsertionToSemantics source (rankedDominionAtlas owner).toAtlas
            (rankedValueInsertion owner insertion))).val.val :=
  DomanialInclusion.coaToDomInc_interpretation source (rankedDominionAtlas owner).toAtlas
    (rankedValueInsertion owner insertion) (rankedComponentBackward owner insertion)
    (rankedComponentLeftInverse owner insertion)

end Datra.Executable.RankedDominionAtlas
