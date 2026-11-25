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

/-- Specialize an insertion to accepted values at a specified canonical key. -/
-- ALIGN: ATLAS-STABLE-SOURCE-INSERTION.
def stableCoalitionInsertionOn {Source Target Key : Type*} (accepts : Source → Bool)
    (key : Source → Key) (origin : Key)
    (forward : {value // accepts value = true ∧ key value = origin} → Target)
    (backward : Target → Option {value // accepts value = true ∧ key value = origin})
    (leftInverse : ∀ value, backward (forward value) = some value) :
    DomanialInsertion {value // accepts value = true ∧ key value = origin} Target :=
  ⟨forward, backward, leftInverse⟩

/-- The stored primitive insertion restricts its source to canonical records.
Its inverse accepts raw target records and returns only certified source data. -/
structure StableTransversalAction (X Y : Atlas) where
  transversal : Transversal X Y
  preserves : stableOriginPreserved transversal = true
  insertion : DomanialInsertion X.Coalition Y.CoalitionElement
  forward : ∀ value, insertion.map value = (mapCoalitionElement transversal value).val

-- ALIGN: ATLAS-STABLE-SOURCE-PACKAGE.
def StableTransversalAction.ofInverse {X Y : Atlas} (transversal : Transversal X Y)
    (preserves : stableOriginPreserved transversal = true)
    (backward : Y.CoalitionElement → Option X.Coalition)
    (leftInverse : ∀ value, backward (mapCoalitionElement transversal value).val = some value) :
    StableTransversalAction X Y where
  transversal := transversal
  preserves := preserves
  insertion := ⟨fun value => (mapCoalitionElement transversal value).val, backward, leftInverse⟩
  forward _ := rfl

theorem StableTransversalAction.ofInverse_preimage {X Y : Atlas} (transversal : Transversal X Y)
    (preserves : stableOriginPreserved transversal = true)
    (backward : Y.CoalitionElement → Option X.Coalition)
    (leftInverse : ∀ value, backward (mapCoalitionElement transversal value).val = some value)
    (value : Y.CoalitionElement) :
    (ofInverse transversal preserves backward leftInverse).insertion.preimage value = backward value := rfl

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

/-- A primitive executable certificate acts on the canonical record. The
covered-value presentation is an equivalent carrier, including for failed
inverse lookups. -/
-- ALIGN: ATLAS-STABLE-CARRIER-CONSTRUCTOR.
def primitiveFromCarrier {X Y : Atlas} (transversal : Transversal X Y)
    (preserves : stableOriginPreserved transversal = true)
    (backward : Y.Coalition → Option X.Coalition)
    (leftInverse : ∀ value, backward (mapCoalitionElement transversal value) = some value) :
    StableTransversal X Y :=
  .primitive transversal preserves
    (fun value => (backward value.presentation).map CertifiedCoalitionElement.value)
    (fun value => by
      change (backward (mapCoalitionValue transversal value).presentation).map
        CertifiedCoalitionElement.value = some value
      have mapped : (mapCoalitionValue transversal value).presentation =
          mapCoalitionElement transversal value.presentation := by
        rw [mapCoalitionElement_presentation, value.presentation_value]
      rw [mapped, leftInverse]
      exact congrArg some value.presentation_value)

/-- Restrict only the target input of the stored inverse to the certified
carrier used by the semantic bridge. Its successful source data are unchanged. -/
def ofAction {X Y : Atlas} (action : StableTransversalAction X Y) : StableTransversal X Y :=
  primitiveFromCarrier action.transversal action.preserves
    (fun value => action.insertion.preimage value.val)
    (fun value => by
      change action.insertion.preimage (mapCoalitionElement action.transversal value).val = some value
      rw [← action.forward value]
      exact action.insertion.leftInverse value)

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

/-- Retain both directions on the exact executable carrier. The value-level
insertion remains the small-carrier interface to the written mathematics. -/
def coalitionCarrierInsertion {X Y : Atlas} (f : StableTransversal X Y) :
    DomanialInsertion X.Coalition Y.Coalition :=
  f.coalitionInsertion.reindex (coalitionValueEquiv X).symm (coalitionValueEquiv Y).symm

-- ALIGN: ATLAS-STABLE-CARRIER-FORWARD.
theorem coalitionCarrierInsertion_primitive_map {X Y : Atlas} (transversal : Transversal X Y)
    (preserves : stableOriginPreserved transversal = true)
    (backward : Y.Coalition → Option X.Coalition)
    (leftInverse : ∀ value, backward (mapCoalitionElement transversal value) = some value)
    (value : X.Coalition) :
    (primitiveFromCarrier transversal preserves backward leftInverse).coalitionCarrierInsertion.map value =
      mapCoalitionElement transversal value :=
  (mapCoalitionElement_presentation transversal value).symm

-- ALIGN: ATLAS-STABLE-CARRIER-INVERSE.
theorem coalitionCarrierInsertion_primitive_preimage {X Y : Atlas} (transversal : Transversal X Y)
    (preserves : stableOriginPreserved transversal = true)
    (backward : Y.Coalition → Option X.Coalition)
    (leftInverse : ∀ value, backward (mapCoalitionElement transversal value) = some value)
    (value : Y.Coalition) :
    (primitiveFromCarrier transversal preserves backward leftInverse).coalitionCarrierInsertion.preimage value =
      backward value := by
  change ((backward value.value.presentation).map CertifiedCoalitionElement.value).map
    CoalitionValue.presentation = backward value
  have rebuild (c : X.Coalition) : c.value.presentation = c :=
    (coalitionValueEquiv X).left_inv c
  have targetRebuild : value.value.presentation = value := (coalitionValueEquiv Y).left_inv value
  rw [targetRebuild, Option.map_map]
  simp only [Function.comp_def, rebuild]
  cases backward value <;> rfl

theorem coalitionCarrierInsertion_ofAction_map {X Y : Atlas} (action : StableTransversalAction X Y)
    (value : X.Coalition) :
    (ofAction action).coalitionCarrierInsertion.map value = mapCoalitionElement action.transversal value :=
  coalitionCarrierInsertion_primitive_map _ _ _ _ value

theorem coalitionCarrierInsertion_ofAction_preimage {X Y : Atlas} (action : StableTransversalAction X Y)
    (value : Y.Coalition) :
    (ofAction action).coalitionCarrierInsertion.preimage value = action.insertion.preimage value.val :=
  coalitionCarrierInsertion_primitive_preimage _ _ _ _ value

-- ALIGN: COALITION-LEFT-INVERSE.
theorem coalitionCarrier_leftInverse {X Y : Atlas} (f : StableTransversal X Y) (value : X.Coalition) :
    f.coalitionCarrierInsertion.preimage (f.coalitionCarrierInsertion.map value) = some value :=
  f.coalitionCarrierInsertion.leftInverse value

theorem coalitionInsertion_comp {X Y Z : Atlas} (second : StableTransversal Y Z)
    (first : StableTransversal X Y) :
    (comp second first).coalitionInsertion = first.coalitionInsertion.comp second.coalitionInsertion := by
  induction first with
  | identity => cases second <;> simp [comp, coalitionInsertion]
  | primitive _ _ _ _ => cases second <;> simp [comp, coalitionInsertion]
  | composite middle first ih _ =>
      cases second <;> simp_all [comp, coalitionInsertion, DomanialInsertion.comp_assoc]

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

-- ALIGN: COALITION-IDENTITY.
theorem coalitionCarrierInsertion_identity (X : Atlas) :
    (identity : StableTransversal X X).coalitionCarrierInsertion = DomanialInsertion.identity _ := by
  exact DomanialInsertion.reindex_identity (coalitionValueEquiv X).symm

-- ALIGN: COALITION-COMPOSITION.
theorem coalitionCarrierInsertion_comp {X Y Z : Atlas} (second : StableTransversal Y Z)
    (first : StableTransversal X Y) :
    (comp second first).coalitionCarrierInsertion =
      first.coalitionCarrierInsertion.comp second.coalitionCarrierInsertion := by
  unfold coalitionCarrierInsertion
  rw [coalitionInsertion_comp]
  exact DomanialInsertion.reindex_comp _ _ _ _ _

-- ALIGN: COALITION-STABLE-INTERPRETATION.
theorem coalitionCarrierInsertion_interpretation {X Y : Atlas} (f : StableTransversal X Y)
    (c : X.Coalition) :
    coalitionSemanticsEquiv Y (f.coalitionCarrierInsertion.map c) =
      Datra.Semantics.stableCoalitionMap f.toSemantics (coalitionSemanticsEquiv X c) := by
  change CoalitionValue.semanticsEquiv Y
    (f.coalitionInsertion.map c.value).presentation.value = _
  rw [CoalitionValue.presentation_value]
  exact f.coalitionInsertion_interpretation c.value

/-- An unchanged inverse retains the caller's owner. A restored inverse stores
the certified source carrier, whose Atlas index is the retained owner. -/
inductive CoalitionPreimage : Atlas → Atlas → Type 2
  | unchanged {X} : CoalitionPreimage X X
  | restored {X Y} : X.Coalition → CoalitionPreimage X Y

def CoalitionPreimage.resolve {X Y : Atlas} : CoalitionPreimage X Y → Y.Coalition → X.Coalition
  | .unchanged, value => value
  | .restored source, _ => source

def CoalitionPreimage.bind {X Y Z : Atlas} (image : CoalitionPreimage Y Z)
    (target : Z.Coalition) (restore : Y.Coalition → Option (CoalitionPreimage X Y)) :
    Option (CoalitionPreimage X Z) :=
  match image with
  | .unchanged => restore target
  | .restored middle => (restore middle).map fun source =>
    match source with
    | .unchanged => .restored middle
    | .restored source => .restored source

theorem CoalitionPreimage.resolve_bind {X Y Z : Atlas} (image : CoalitionPreimage Y Z)
    (target : Z.Coalition) (restore : Y.Coalition → Option (CoalitionPreimage X Y)) :
    (image.bind target restore).map (fun source => source.resolve target) =
      (restore (image.resolve target)).map (fun source => source.resolve (image.resolve target)) := by
  cases image with
  | unchanged => rfl
  | restored middle =>
    cases found : restore middle with
    | none => simp [bind, resolve, found]
    | some source => cases source <;> simp [bind, resolve, found]

-- ALIGN: ATLAS-STABLE-OWNED-PREIMAGE.
def coalitionPreimage {X Y : Atlas} (arrow : StableTransversal X Y)
    (target : Y.Coalition) : Option (CoalitionPreimage X Y) :=
  match arrow with
  | .identity => some .unchanged
  | .primitive transversal preserves backward leftInverse =>
    ((primitive transversal preserves backward leftInverse).coalitionCarrierInsertion.preimage target).map
      CoalitionPreimage.restored
  | .composite second first =>
    (second.coalitionPreimage target).bind fun middle =>
      middle.bind target first.coalitionPreimage

theorem coalitionPreimage_resolve {X Y : Atlas} (arrow : StableTransversal X Y)
    (target : Y.Coalition) :
    (arrow.coalitionPreimage target).map (fun source => source.resolve target) =
      arrow.coalitionCarrierInsertion.preimage target := by
  induction arrow with
  | primitive transversal preserves backward leftInverse =>
    simp [coalitionPreimage, Option.map_map, CoalitionPreimage.resolve, Function.comp_def]
  | identity =>
    simp [coalitionPreimage, CoalitionPreimage.resolve,
      coalitionCarrierInsertion_identity, DomanialInsertion.identity]
  | @composite X Y Z second first ihSecond ihFirst =>
    have composition : (composite second first).coalitionCarrierInsertion =
        first.coalitionCarrierInsertion.comp second.coalitionCarrierInsertion :=
      DomanialInsertion.reindex_comp _ _ _ _ _
    rw [composition]
    simp only [coalitionPreimage, Option.map_bind, Function.comp_def]
    simp_rw [CoalitionPreimage.resolve_bind, ihFirst]
    change _ = (second.coalitionCarrierInsertion.preimage target).bind
      first.coalitionCarrierInsertion.preimage
    rw [← ihSecond target, Option.bind_map]
    rfl

-- ALIGN: ATLAS-STABLE-OWNED-PREIMAGE-ELIMINATION.
def withCoalitionPreimage {X Y : Atlas} {Result : Type*} (arrow : StableTransversal X Y)
    (target : Y.Coalition) (usePreimage : X.Coalition → Result) : Option Result :=
  (arrow.coalitionPreimage target).map fun source => usePreimage (source.resolve target)

theorem withCoalitionPreimage_eq {X Y : Atlas} {Result : Type*} (arrow : StableTransversal X Y)
    (target : Y.Coalition) (usePreimage : X.Coalition → Result) :
    arrow.withCoalitionPreimage target usePreimage =
      (arrow.coalitionCarrierInsertion.preimage target).map usePreimage := by
  rw [← coalitionPreimage_resolve]
  simp [withCoalitionPreimage, Option.map_map, Function.comp_def]

end StableTransversal
end Datra.Executable.Atlas
