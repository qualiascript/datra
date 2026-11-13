import Executable.Atlas.Derived
import Executable.Folio.Prefix

namespace Datra.Executable

/-- Clamp only beyond the given limit, which may exceed the component's own
finite depth. This retains the genuine intermediate pages of a larger merge. -/
def clampedElement (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) : X.Element :=
  FolioData.ValidElement.ofOccurrence ⟨min source.occurrence.page limit,
    cast (congrArg Page.Carrier (X.pages.pageAt_clamp limit source.occurrence.page bound).symm)
      source.occurrence.value⟩

theorem clampedElement_page (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) :
    (clampedElement X limit bound source).val.page = min source.val.page limit := by
  change min source.occurrence.toRaw.page limit = _
  rw [FolioData.ValidElement.occurrence_toRaw]

theorem clampedElement_position (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) :
    (clampedElement X limit bound source).val.position = source.val.position := by
  exact (Page.cast_position (X.pages.pageAt_clamp limit source.occurrence.page bound).symm
    source.occurrence.value).trans (congrArg PageElement.position source.occurrence_toRaw)

theorem clampedElement_normalize (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) : (clampedElement X limit bound source).normalize = source.normalize := by
  apply FolioData.ValidElement.eq_of_page_position
  · change min (clampedElement X limit bound source).val.page (X.pages.depth - 1) =
      min source.val.page (X.pages.depth - 1)
    rw [clampedElement_page]
    omega
  · exact clampedElement_position X limit bound source

theorem clampedElement_containsRank (X : Atlas) (limit : Nat) (bound : X.pages.depth - 1 ≤ limit)
    (source : X.Element) (rank : Nat) :
    X.cellContainsRank (clampedElement X limit bound source) rank = X.cellContainsRank source rank := by
  rw [← X.cellContainsRank_normalize, clampedElement_normalize, X.cellContainsRank_normalize]

end Datra.Executable
