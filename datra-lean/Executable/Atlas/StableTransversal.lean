import Executable.Atlas.Coalition

namespace Datra.Executable.Atlas
open CategoryTheory

def stableOrigin (X : Atlas) : X.TransposalElement :=
  X.transposalElement (FolioData.ValidElement.originElement X.pages)

-- ALIGN: ATLAS-STABLE-ORIGIN.
theorem stableOrigin_interpretation (X : Atlas) :
    (stableOrigin X).toSemantics = X.toSemantics.Fo.originElement := by
  have h : stableOrigin X = TransposalElement.fromSemantics X X.toSemantics.Fo.originElement := by
    apply Subtype.ext
    change (FolioData.ValidElement.originElement X.pages).normalize = _
    rw [FolioData.ValidElement.originElement_interpretation]
    exact FolioData.ValidElement.normalize_fromFinite _ _
  rw [h, TransposalElement.toSemantics_fromSemantics]

/-- The runtime predicate compares the normalized image's page and ordinal
with the canonical origin's page and ordinal. -/
def stableOriginPreserved {X Y : Atlas} (f : Transversal X Y) : Bool :=
  TransposalElement.equal (f.underlying.mapObject (stableOrigin X)) (stableOrigin Y)

-- ALIGN: ATLAS-STABLE-PREDICATE.
theorem stableOriginPreserved_interpretation {X Y : Atlas} (f : Transversal X Y) :
    stableOriginPreserved f = true ↔ Datra.Semantics.IsStableTransversal f.toSemantics := by
  rw [stableOriginPreserved, TransposalElement.equal_iff,
    ← (TransposalElement.semanticsEquiv Y).injective.eq_iff]
  change (f.underlying.mapObject (stableOrigin X)).toSemantics = (stableOrigin Y).toSemantics ↔ _
  rw [OrderedTransposal.mapObject, Transposal.mapObject_interpretation,
    stableOrigin_interpretation, stableOrigin_interpretation]
  rfl

/-- The primitive certificate is precisely the checked Haskell boundary.
Identity and composition derive stability by their constructor cases. -/
inductive StableTransversal : Atlas → Atlas → Type 2
  | primitive {X Y} (transversal : Transversal X Y)
      (preserves : stableOriginPreserved transversal = true)
      (backward : Y.CoalitionValue → Option X.CoalitionValue)
      (leftInverse : ∀ value, backward (mapCoalitionValue transversal value) = some value) :
      StableTransversal X Y
  | identity {X} : StableTransversal X X
  | composite {X Y Z} : StableTransversal Y Z → StableTransversal X Y → StableTransversal X Z

namespace StableTransversal

def underlying {X Y : Atlas} : StableTransversal X Y → Transversal X Y
  | .primitive transversal _ _ _ => transversal
  | .identity => .identity
  | .composite second first => Transversal.comp second.underlying first.underlying

-- ALIGN: ATLAS-STABLE-INTERPRETATION.
theorem semantic_stable {X Y : Atlas} (f : StableTransversal X Y) :
    Datra.Semantics.IsStableTransversal f.underlying.toSemantics := by
  induction f with
  | primitive transversal preserves _ _ => exact (stableOriginPreserved_interpretation transversal).mp preserves
  | identity =>
      change Datra.Semantics.IsStableTransversal (Transversal.identity.toSemantics)
      rw [Transversal.toSemantics_identity]
      exact Datra.Semantics.IsStableTransversal.id_mem _
  | composite second first ih₂ ih₁ =>
      change Datra.Semantics.IsStableTransversal ((Transversal.comp second.underlying first.underlying).toSemantics)
      rw [Transversal.toSemantics_comp]
      exact Datra.Semantics.IsStableTransversal.comp_mem _ _ ih₁ ih₂

-- ALIGN: ATLAS-STABLE-EXTENT.
theorem preservesExtent {X Y : Atlas} (f : StableTransversal X Y) :
    stableOriginPreserved f.underlying = true :=
  (stableOriginPreserved_interpretation f.underlying).mpr f.semantic_stable

noncomputable def toSemantics {X Y : Atlas} (f : StableTransversal X Y) :
    (WideSubcategory.mk (WideSubcategory.mk X.toSemantics) : Datra.Semantics.StaAtlTrav) ⟶
      (WideSubcategory.mk (WideSubcategory.mk Y.toSemantics) : Datra.Semantics.StaAtlTrav) :=
  ⟨f.underlying.toSemantics, f.semantic_stable⟩

def comp {X Y Z : Atlas} : StableTransversal Y Z → StableTransversal X Y → StableTransversal X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (comp second middle) first
  | second, first => .composite second first

-- ALIGN: ATLAS-STABLE-IDENTITY.
@[simp] theorem toSemantics_identity (X : Atlas) :
    (identity : StableTransversal X X).toSemantics =
      𝟙 (WideSubcategory.mk (WideSubcategory.mk X.toSemantics) : Datra.Semantics.StaAtlTrav) := by
  apply Subtype.ext
  exact Transversal.toSemantics_identity X

@[simp] theorem toSemantics_composite {X Y Z : Atlas}
    (second : StableTransversal Y Z) (first : StableTransversal X Y) :
    (composite second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact Transversal.toSemantics_comp second.underlying first.underlying

-- ALIGN: ATLAS-STABLE-COMPOSITION.
theorem toSemantics_comp {X Y Z : Atlas} (second : StableTransversal Y Z) (first : StableTransversal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  induction first with
  | identity => cases second <;> simp [comp]
  | primitive _ _ _ _ => cases second <;> simp [comp]
  | composite middle first ih _ => cases second <;> simp_all [comp, Category.assoc]

def mapCovered {X Y : Atlas} (f : StableTransversal X Y) : X.CertifiedCoveredElement → Y.CertifiedCoveredElement :=
  f.underlying.mapCovered

-- ALIGN: ATLAS-STABLE-COVERED.
theorem mapCovered_interpretation {X Y : Atlas} (f : StableTransversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    (f.mapCovered c).data = fromSemanticData Y (mapSemanticData f.toSemantics.val.val source) :=
  f.underlying.mapCovered_interpretation c source h

/-- Match the stored primitive insertion and the structural identity and
composition cases of stableAtlasTransversalCoalitionInsertion. -/
def coalitionInsertion {X Y : Atlas} : StableTransversal X Y → DomanialInsertion X.CoalitionValue Y.CoalitionValue
  | .primitive transversal _ backward leftInverse =>
      ⟨mapCoalitionValue transversal, backward, leftInverse⟩
  | .identity => DomanialInsertion.identity _
  | .composite second first => first.coalitionInsertion.comp second.coalitionInsertion

-- ALIGN: COALITION-LEFT-INVERSE.
theorem coalition_leftInverse {X Y : Atlas} (f : StableTransversal X Y) (value : X.CoalitionValue) :
    f.coalitionInsertion.preimage (f.coalitionInsertion.map value) = some value :=
  f.coalitionInsertion.leftInverse value

-- ALIGN: COALITION-IDENTITY.
theorem coalitionInsertion_identity (X : Atlas) :
    (identity : StableTransversal X X).coalitionInsertion = DomanialInsertion.identity _ := rfl

-- ALIGN: COALITION-COMPOSITION.
theorem coalitionInsertion_comp {X Y Z : Atlas} (second : StableTransversal Y Z)
    (first : StableTransversal X Y) :
    (comp second first).coalitionInsertion = first.coalitionInsertion.comp second.coalitionInsertion := by
  induction first with
  | identity => cases second <;> simp [comp, coalitionInsertion]
  | primitive _ _ _ _ => cases second <;> simp [comp, coalitionInsertion]
  | composite middle first ih _ =>
      cases second <;> simp_all [comp, coalitionInsertion, DomanialInsertion.comp_assoc]

-- ALIGN: COALITION-STABLE-INTERPRETATION.
theorem coalitionInsertion_interpretation {X Y : Atlas} (f : StableTransversal X Y)
    (c : X.CoalitionValue) :
    CoalitionValue.semanticsEquiv Y (f.coalitionInsertion.map c) =
      Datra.Semantics.stableCoalitionMap f.toSemantics (CoalitionValue.semanticsEquiv X c) := by
  induction f with
  | primitive transversal preserves backward leftInverse =>
      apply Subtype.ext
      rw [Datra.Semantics.stableCoalitionMap_val]
      exact mapCoalitionValue_interpretation transversal c
  | @identity A =>
      rw [toSemantics_identity]
      change CoalitionValue.semanticsEquiv A c = Datra.Semantics.Coa.map
        (𝟙 (WideSubcategory.mk (WideSubcategory.mk A.toSemantics) : Datra.Semantics.StaAtlTrav))
        (CoalitionValue.semanticsEquiv A c)
      rw [Datra.Semantics.Coa.map_id]
      rfl
  | composite second first ih₂ ih₁ =>
      rw [toSemantics_composite]
      change CoalitionValue.semanticsEquiv _ (second.coalitionInsertion.map (first.coalitionInsertion.map c)) =
        Datra.Semantics.Coa.map (first.toSemantics ≫ second.toSemantics) _
      rw [Datra.Semantics.Coa.map_comp]
      exact (ih₂ (first.coalitionInsertion.map c)).trans
        (congrArg (Datra.Semantics.stableCoalitionMap second.toSemantics) (ih₁ c))

end StableTransversal
end Datra.Executable.Atlas
