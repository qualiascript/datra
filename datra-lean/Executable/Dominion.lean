import Semantics

namespace Datra.Executable

/-- Dominion.Internal.Dominion, including its executable partial inverse. -/
structure Dominion (Carrier : Type) where
  rank : Carrier → Nat
  unrank : Nat → Option Carrier
  coherence : ∀ x, unrank (rank x) = some x

-- ALIGN: DOMINION-RANK-INJECTIVE.
theorem Dominion.rank_injective {A : Type} (D : Dominion A) :
    Function.Injective D.rank := by
  intro x y h
  have := congrArg D.unrank h
  simpa [D.coherence] using this

def Dominion.toSemantics {A : Type} (D : Dominion A) : Datra.Semantics.Dominion :=
  ⟨A, ⟨D.rank, D.rank_injective⟩⟩

end Datra.Executable
