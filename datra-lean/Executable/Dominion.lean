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

/-- Change only the presentation of a carrier, retaining both executable
ranking and optional decoding. -/
def Dominion.reindex {A B : Type} (D : Dominion A) (equiv : A ≃ B) : Dominion B where
  rank value := D.rank (equiv.symm value)
  unrank n := (D.unrank n).map equiv
  coherence value := by simp [D.coherence]

@[simp] theorem Dominion.reindex_rank {A B : Type} (D : Dominion A) (equiv : A ≃ B)
    (value : A) : (D.reindex equiv).rank (equiv value) = D.rank value := by
  simp [reindex]

@[simp] theorem Dominion.reindex_unrank {A B : Type} (D : Dominion A) (equiv : A ≃ B)
    (n : Nat) : (D.reindex equiv).unrank n = (D.unrank n).map equiv := rfl

/-- An ambient Haskell type together with the predicate restricting the actual
Dominion carrier. The predicate remains available after existential packaging. -/
structure MembershipDominion (A : Type) where
  accepts : A → Bool
  dominion : Dominion {value : A // accepts value = true}

-- ALIGN: DOMINION-MEMBERSHIP-PACKAGE.
def MembershipDominion.package {A : Type} (accepts : A → Bool)
    (dominion : Dominion {value : A // accepts value = true}) : MembershipDominion A :=
  ⟨accepts, dominion⟩

theorem MembershipDominion.unrank_accepted {A : Type} (D : MembershipDominion A)
    (n : Nat) (datum : {value : A // D.accepts value = true})
    (_found : D.dominion.unrank n = some datum) : D.accepts datum.val = true :=
  datum.property

end Datra.Executable
