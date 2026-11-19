import Executable.Folio

namespace Datra.Executable.Folio

-- ALIGN: FOLIO-COLLAPSE-ORIGIN.
def collapseToOrigin {A : Type} (source : Chain A) (target : Chain Unit) (chosen : A) :
    OrderedConsolidation A Unit :=
  ⟨source, target, {
    map _ := ()
    preimage _ := chosen
    monotone _ _ _ := le_rfl
    rightInverse value := by cases value; rfl }⟩

-- ALIGN: FOLIO-APPEND-ACCEPTED.
def appendOrderedPage {origin previous : Page} {Next : Type}
    (pages : Folio origin previous) (transition : OrderedConsolidation Next previous.Carrier)
    (target : transition.target = previous.chain) : Folio origin ⟨Next, transition.source⟩ :=
  let step : Consolidation transition.source previous.chain := target ▸ transition.map
  ⟨pages.data.append ⟨Next, transition.source⟩ step,
    pages.data.append_valid pages.valid ⟨Next, transition.source⟩ step⟩

end Datra.Executable.Folio
