import Executable.Chain

namespace Datra.Executable.Chain

-- ALIGN: CHAIN-SINGLETON.
def singletonChain : Chain Unit where
  orderType := Ordinal.finiteOrdinal 1
  position := fun _ => Ordinal.finiteOrdinal 0
  lookup position := if position = Ordinal.finiteOrdinal 0 then some () else none
  positionBelow _ := by decide
  positionInjective _ _ _ := Subsingleton.elim _ _
  positionSurjective position below := by
    have hz := Ordinal.ordinalBelowOne position below
    subst position
    exact ⟨(), by simp, rfl⟩

-- ALIGN: CHAIN-SINGLETON-POSITION.
theorem singletonChain_position (value : Unit) :
    singletonChain.position value = Ordinal.finiteOrdinal 0 := rfl

end Datra.Executable.Chain
