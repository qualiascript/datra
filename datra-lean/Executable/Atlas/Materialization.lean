import Executable.Atlas.Morphism

namespace Datra.Executable.Atlas

-- ALIGN: ATLAS-MORPHISM-SOURCE-OWNER.
def Morphism.sourceOwner {X Y : Atlas} : Morphism X Y → AtlasOwner
  | .primitive _ => atlasOwner X
  | .identity => atlasOwner X
  | .composite _ first => Morphism.sourceOwner first

-- ALIGN: ATLAS-MORPHISM-TARGET-OWNER.
def Morphism.targetOwner {X Y : Atlas} : Morphism X Y → AtlasOwner
  | .primitive _ => atlasOwner Y
  | .identity => atlasOwner Y
  | .composite second _ => Morphism.targetOwner second

-- ALIGN: ATLAS-MATERIALIZED-IDENTITY-OWNERS.
theorem Morphism.identity_owners (X : Atlas) :
    Morphism.sourceOwner (AtlasMorphism.identity : Morphism X X) = atlasOwner X ∧
      Morphism.targetOwner (AtlasMorphism.identity : Morphism X X) = atlasOwner X := ⟨rfl, rfl⟩

-- ALIGN: ATLAS-MATERIALIZED-COMPOSITION-OWNERS.
theorem Morphism.composite_owners {X M Y : Atlas} (second : Morphism M Y) (first : Morphism X M) :
    Morphism.sourceOwner (AtlasMorphism.composite second first) = Morphism.sourceOwner first ∧
      Morphism.targetOwner (AtlasMorphism.composite second first) = Morphism.targetOwner second := ⟨rfl, rfl⟩

/-- The interpreted indices identify the actual owners; raw Haskell callers
must separately discharge these owner agreements before using this model. -/
theorem Morphism.owners {X Y : Atlas} (morphism : Morphism X Y) :
    Morphism.sourceOwner morphism = atlasOwner X ∧ Morphism.targetOwner morphism = atlasOwner Y := by
  induction morphism with
  | primitive => exact ⟨rfl, rfl⟩
  | identity => exact ⟨rfl, rfl⟩
  | composite second first ihSecond ihFirst => exact ⟨ihFirst.1, ihSecond.2⟩

def Morphism.targetWitness {X Y : Atlas} : Morphism X Y → AtlasWitness
  | .primitive _ => atlasWitness Y
  | .identity => atlasWitness Y
  | .composite second _ => Morphism.targetWitness second

-- ALIGN: ATLAS-MORPHISM-TARGET-WITNESS.
theorem Morphism.targetWitness_owner {X Y : Atlas} (morphism : Morphism X Y) :
    atlasWitnessOwner (Morphism.targetWitness morphism) = Morphism.targetOwner morphism := by
  induction morphism with
  | primitive => rfl
  | identity => rfl
  | composite second first ihSecond _ => exact ihSecond

theorem Morphism.targetWitness_eq {X Y : Atlas} (morphism : Morphism X Y) :
    Morphism.targetWitness morphism = atlasWitness Y := by
  induction morphism with
  | primitive => rfl
  | identity => rfl
  | composite second first ihSecond _ => exact ihSecond

/-- Symbolic identity retains the supplied witness. Primitive and composite
cases recover the actual targets stored by the materialized operations. -/
def Hom.targetWitness {X Y : Atlas} (source : AtlasWitness) : Hom X Y → AtlasWitness
  | .primitive operation => Morphism.targetWitness operation
  | .identity => source
  | .composite second first => Hom.targetWitness (Hom.targetWitness source first) second

-- ALIGN: ATLASHOM-SOURCE-OWNER.
def Hom.sourceOwner {X Y : Atlas} (source : AtlasWitness) : Hom X Y → AtlasOwner
  | .primitive operation => Morphism.sourceOwner operation
  | .identity => atlasWitnessOwner source
  | .composite _ first => Hom.sourceOwner source first

-- ALIGN: ATLASHOM-TARGET-OWNER.
def Hom.targetOwner {X Y : Atlas} (source : AtlasWitness) : Hom X Y → AtlasOwner
  | .primitive operation => Morphism.targetOwner operation
  | .identity => atlasWitnessOwner source
  | .composite second first => Hom.targetOwner (Hom.targetWitness source first) second

/-- Follow the second subtree after recovering the first subtree's witness;
no nominal index is used as a substitute for that retained owner. -/
-- ALIGN: ATLASHOM-RETAINED-TARGET-WITNESS.
theorem Hom.targetWitness_owner {X Y : Atlas} (hom : Hom X Y) (source : AtlasWitness) :
    atlasWitnessOwner (Hom.targetWitness source hom) = Hom.targetOwner source hom := by
  induction hom generalizing source with
  | primitive operation => exact Morphism.targetWitness_owner operation
  | identity => rfl
  | composite second first ihSecond _ => exact ihSecond (Hom.targetWitness source first)

theorem Hom.targetWitness_eq {X Y : Atlas} (hom : Hom X Y) (source : AtlasWitness)
    (owns : source.owner = X) : Hom.targetWitness source hom = atlasWitness Y := by
  induction hom generalizing source with
  | primitive operation => exact Morphism.targetWitness_eq operation
  | identity => cases source; cases owns; rfl
  | composite second first ihSecond ihFirst =>
    simp only [targetWitness, ihFirst source owns]
    exact ihSecond (atlasWitness _) rfl

theorem Hom.sourceOwner_eq {X Y : Atlas} (hom : Hom X Y) (source : AtlasWitness)
    (owns : source.owner = X) : Hom.sourceOwner source hom = atlasOwner X := by
  induction hom generalizing source with
  | primitive operation => exact (Morphism.owners operation).1
  | identity => exact congrArg atlasOwner owns
  | composite second first _ ihFirst => exact ihFirst source owns

/-- Induction recovers the actual intermediate witness. On the owner-consistent
interpretation, materialization preserves both complete endpoint observations. -/
-- ALIGN: ATLASHOM-MATERIALIZED-OWNERS.
theorem Hom.materialize_owners {X Y : Atlas} (hom : Hom X Y) (source : AtlasWitness)
    (owns : source.owner = X) :
    Morphism.sourceOwner (Hom.materialize hom) = Hom.sourceOwner source hom ∧
      Morphism.targetOwner (Hom.materialize hom) = Hom.targetOwner source hom := by
  refine ⟨(Morphism.owners (Hom.materialize hom)).1.trans (Hom.sourceOwner_eq hom source owns).symm, ?_⟩
  rw [← Hom.targetWitness_owner hom source, Hom.targetWitness_eq hom source owns]
  exact (Morphism.owners (Hom.materialize hom)).2

end Datra.Executable.Atlas
