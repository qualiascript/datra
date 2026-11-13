import Executable.Atlas.Derived

namespace Datra.Executable
open CategoryTheory Opposite

theorem componentFinite_normalize (X : Atlas) (n : Nat) (value : (X.pages.pageAt n).Carrier) :
    (FolioData.ValidElement.fromFinite X.pages).obj
      (⟨op (X.toSemantics.Fo.paddedIndex n), value⟩ : X.toSemantics.El) =
      (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence)).normalize := by
  have result := FolioData.ValidElement.fromFinite_collapse
    (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence))
  change (FolioData.ValidElement.fromFinite X.pages).obj
    (X.pages.toSemantics.collapseElements.obj ((FolioData.Occurrence.toSemantics X.pages).obj
      (FolioData.ValidElement.ofOccurrence (⟨n, value⟩ : X.pages.Occurrence)).occurrence)) = _ at result
  rw [FolioData.ValidElement.occurrence_ofOccurrence] at result
  exact result

theorem componentContainsRank_interpretation (X : Atlas) (n : Nat)
    (value : (X.pages.pageAt n).Carrier) (valueRank : Nat) :
    X.cellContainsRank (FolioData.ValidElement.ofOccurrence ⟨n, value⟩) valueRank = true ↔
      ∃ datum : X.toSemantics.Da.obj ⟨op (X.toSemantics.Fo.paddedIndex n), value⟩,
        (Datra.Semantics.extent X.toSemantics).toDom.rank
          (Datra.Semantics.originImage X.toSemantics _ datum) = valueRank := by
  rw [← X.cellContainsRank_normalize, ← componentFinite_normalize, X.cellContainsRank_iff]
  simp only [X.originImageRank_interpretation]
  rfl

theorem extentContainsRank_interpretation (X : Atlas) (valueRank : Nat) :
    X.extentContainsRank valueRank = true ↔
      ∃ datum : Datra.Semantics.extent X.toSemantics,
        (Datra.Semantics.extent X.toSemantics).toDom.rank datum = valueRank := by
  rw [← X.extent_interpretation]
  exact X.extentContainsRank_iff valueRank

theorem imageDom_rank_exists {A R : Datra.Semantics.DomIns} (map : A ⟶ R) (valueRank : Nat) :
    (∃ value : Datra.Semantics.imageDom map,
      (Datra.Semantics.imageDom map).toDom.rank value = valueRank) ↔
    ∃ value : A, R.toDom.rank (map value) = valueRank := by
  constructor
  · rintro ⟨⟨value, original, rfl⟩, same⟩
    exact ⟨original, same⟩
  · rintro ⟨value, same⟩
    exact ⟨⟨map value, value, rfl⟩, same⟩

end Datra.Executable
