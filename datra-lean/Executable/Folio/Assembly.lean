import Executable.Folio
import Executable.Chain.Singleton

namespace Datra.Executable.Folio

-- ALIGN: FOLIO-COLLAPSE-ORIGIN.
def collapseToOrigin {A : Type} (source : Chain A) (target : Chain Unit) (chosen : A) :
    OrderedConsolidation A Unit :=
  ⟨source, target, {
    map _ := ()
    preimage _ := chosen
    monotone _ _ _ := le_rfl
    rightInverse value := by cases value; rfl }⟩

def firstPageTrace (position : Ordinal) : List Ordinal := [position, Ordinal.finiteOrdinal 0]

/-- The first appended page retains its actual trace above the fresh origin. -/
structure OriginExtension {A : Type} (source : Chain A) where
  pages : Folio ⟨Unit, Chain.singletonChain⟩ ⟨A, source⟩
  length : pages.data.length = 2
  trace : ∀ value, pages.data.genuineTrace value = firstPageTrace (source.position value)

-- ALIGN: FOLIO-ORIGIN-EXTENSION.
def extendOrigin {A : Type} (source : Chain A) (chosen : A) : OriginExtension source :=
  let origin := FolioData.singleton ⟨Unit, Chain.singletonChain⟩ () (fun value => by cases value; rfl)
  let transition := collapseToOrigin source Chain.singletonChain chosen
  { pages := ⟨origin.append ⟨A, source⟩ transition.map,
      origin.append_valid rfl _ _⟩
    length := rfl
    trace := fun _ => rfl }

-- ALIGN: FOLIO-APPEND-ACCEPTED.
def appendOrderedPage {origin previous : Page} {Next : Type}
    (pages : Folio origin previous) (transition : OrderedConsolidation Next previous.Carrier)
    (target : transition.target = previous.chain) : Folio origin ⟨Next, transition.source⟩ :=
  let step : Consolidation transition.source previous.chain := target ▸ transition.map
  ⟨pages.data.append ⟨Next, transition.source⟩ step,
    pages.data.append_valid pages.valid ⟨Next, transition.source⟩ step⟩

end Datra.Executable.Folio
