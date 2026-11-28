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

/-- The stored primitive insertion restricts its source to canonical records.
Its inverse accepts raw target records and returns only certified source data. -/
structure StableTransversalAction (X Y : Atlas) where
  transversal : Transversal X Y
  preserves : stableOriginPreserved transversal = true
  insertion : DomanialInsertion X.Coalition Y.CoalitionElement
  forward : ∀ value, insertion.map value = (mapCoalitionElement transversal value).val

/-- The stored raw-target insertion maps every canonical source into the
canonical carrier of the mapper's retained target Atlas. -/
-- ALIGN: ATLAS-STABLE-TARGET-PACKAGE.
theorem StableTransversalAction.forward_valid {X Y : Atlas}
    (action : StableTransversalAction X Y) (value : X.Coalition) :
    CoalitionElement.Valid (action.insertion.map value) := by
  rw [action.forward value]
  exact (mapCoalitionElement action.transversal value).property

/-- The mapped coalition is accepted by the next action when its retained
source owner equals the first action's actual mapped target owner. -/
-- ALIGN: ATLAS-STABLE-NEXT-SOURCE-DOMAIN.
theorem StableTransversalAction.next_source_valid {X M N Y : Atlas}
    (first : StableTransversalAction X M) (_second : StableTransversalAction N Y)
    (owners : atlasOwner N = atlasOwner M) (source : X.Coalition) :
    let sameOwner : M = N := congrArg AtlasOwner.value owners.symm
    CoalitionElement.Valid (sameOwner ▸ first.insertion.map source) :=
  (CoalitionElement.owners_agree M N owners.symm _).1.mp (first.forward_valid source)

/-- Restrict the retained raw target to the mapper's canonical carrier. No
successful or failed inverse lookup is changed. -/
def StableTransversalAction.canonicalInsertion {X Y : Atlas}
    (action : StableTransversalAction X Y) : DomanialInsertion X.Coalition Y.Coalition where
  map source := ⟨action.insertion.map source, action.forward_valid source⟩
  preimage target := action.insertion.preimage target.val
  leftInverse source := action.insertion.leftInverse source

/-- Complete-owner equality permits the requested target's canonical domain. -/
def StableTransversalAction.insertionForOwner {X Y : Atlas}
    (action : StableTransversalAction X Y) (target : Atlas)
    (owners : atlasOwner target = atlasOwner Y) :
    DomanialInsertion X.Coalition target.Coalition :=
  let sameOwner : Y = target := (congrArg AtlasOwner.value owners).symm
  sameOwner ▸ action.canonicalInsertion

@[simp] theorem StableTransversalAction.canonicalInsertion_map {X Y : Atlas}
    (action : StableTransversalAction X Y) (source : X.Coalition) :
    (action.canonicalInsertion.map source).val = action.insertion.map source := rfl

@[simp] theorem StableTransversalAction.canonicalInsertion_preimage {X Y : Atlas}
    (action : StableTransversalAction X Y) (target : Y.Coalition) :
    action.canonicalInsertion.preimage target = action.insertion.preimage target.val := rfl

/-- Scalar observations decode the same canonical record before calling the
stored primitive operation. They introduce no alternative insertion. -/
def StableTransversalAction.forwardCode {X Y : Atlas} (action : StableTransversalAction X Y)
    (code : Nat) : Option Nat :=
  (coalitionUnrank X code).map (fun source => coalitionElementCode (action.insertion.map source))

def StableTransversalAction.inverseCode {X Y : Atlas} (action : StableTransversalAction X Y)
    (code : Nat) : Option Nat :=
  (coalitionUnrank Y code).bind (fun target => coalitionMaybeCode (action.insertion.preimage target.val))

namespace StableCoalitionSyntax

/-- Actual owner indices supply the native syntax's complete-owner certificates. -/
abbrev Syntax := AtlasHom StableTransversalAction

def sourceOwner {X Y : Atlas} (arrow : Syntax X Y) : Option AtlasOwner :=
  TransposalPath.sourceOwner (fun {X _} _ => atlasOwner X) arrow

def targetOwner {X Y : Atlas} (arrow : Syntax X Y) : Option AtlasOwner :=
  TransposalPath.targetOwner (fun {_ Y} _ => atlasOwner Y) arrow

def OwnersCompatible {X Y : Atlas} (arrow : Syntax X Y) : Prop :=
  TransposalPath.OwnersCompatible (fun {X _} _ => atlasOwner X)
    (fun {_ Y} _ => atlasOwner Y) arrow

/-- Normalization preserves the actual endpoint owners and every join premise. -/
-- ALIGN: ATLAS-STABLE-NORMALIZED-OWNERS.
theorem normalized_owners {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    sourceOwner (AtlasHom.composeAtlasHoms second first) = sourceOwner (.composite second first) ∧
    targetOwner (AtlasHom.composeAtlasHoms second first) = targetOwner (.composite second first) ∧
    (OwnersCompatible (AtlasHom.composeAtlasHoms second first) ↔
      OwnersCompatible (.composite second first)) := by
  have expanded {A B : Atlas} (arrow : Syntax A B) :
      arrow.expandPrimitives (fun action => .primitive action) = arrow := by
    induction arrow <;> simp_all [AtlasHom.expandPrimitives]
  have retained := TransposalPath.normalized_expansion_owners
    (fun action : StableTransversalAction _ _ => .primitive action)
    (fun {X _} _ => atlasOwner X) (fun {_ Y} _ => atlasOwner Y) first second
  simpa only [expanded] using retained

def scopedInsertion {X Y : Atlas} : Syntax X Y → DomanialInsertion X.Coalition Y.Coalition
  | .primitive action => action.canonicalInsertion
  | .identity => DomanialInsertion.identity _
  | .composite second first => (scopedInsertion first).comp (scopedInsertion second)

/-- The public Coalizing operation accepts actual source and target owners.
Complete-owner equality transports both canonical domains of the same insertion. -/
def insertionForOwners {X Y : Atlas} (arrow : Syntax X Y) (source target : Atlas)
    (sourceOwner : atlasOwner source = atlasOwner X)
    (targetOwner : atlasOwner target = atlasOwner Y) :
    DomanialInsertion source.Coalition target.Coalition := by
  have sourceEq : source = X := congrArg AtlasOwner.value sourceOwner
  have targetEq : target = Y := congrArg AtlasOwner.value targetOwner
  cases sourceEq
  cases targetEq
  exact scopedInsertion arrow

/-- Naming equal owners changes neither the forward map nor any partial-inverse
result, including failure and successful lookups outside the forward image. -/
-- ALIGN: COALITION-OWNED-DOMAINS.
theorem insertionForOwners_agrees {X Y : Atlas} (arrow : Syntax X Y) (source target : Atlas)
    (sourceOwner : atlasOwner source = atlasOwner X)
    (targetOwner : atlasOwner target = atlasOwner Y) :
    HEq (insertionForOwners arrow source target sourceOwner targetOwner) (scopedInsertion arrow) := by
  have sourceEq : source = X := congrArg AtlasOwner.value sourceOwner
  have targetEq : target = Y := congrArg AtlasOwner.value targetOwner
  cases sourceEq
  cases targetEq
  rfl

theorem scopedInsertion_primitive_map {X Y : Atlas} (action : StableTransversalAction X Y)
    (source : X.Coalition) :
    ((scopedInsertion (.primitive action)).map source).val = action.insertion.map source := rfl

theorem scopedInsertion_primitive_preimage {X Y : Atlas} (action : StableTransversalAction X Y)
    (target : Y.Coalition) :
    (scopedInsertion (.primitive action)).preimage target = action.insertion.preimage target.val := rfl

def forwardCodes {X Y : Atlas} : Syntax X Y → Nat → Option Nat
  | .primitive action => action.forwardCode
  | .identity => some
  | .composite second first => fun code => (forwardCodes first code).bind (forwardCodes second)

def inverseCodes {X Y : Atlas} : Syntax X Y → Nat → Option Nat
  | .primitive action => action.inverseCode
  | .identity => some
  | .composite second first => fun code => (inverseCodes second code).bind (inverseCodes first)

/-- Both scalar observations share one owner-independent package. -/
structure CodeFunctions where
  forward : Nat → Option Nat
  inverse : Nat → Option Nat

-- ALIGN: ATLAS-STABLE-CODE-OBSERVATIONS.
def codeFunctions {X Y : Atlas} (arrow : Syntax X Y) : CodeFunctions :=
  ⟨forwardCodes arrow, inverseCodes arrow⟩

theorem codeFunctions_observations {X Y : Atlas} (arrow : Syntax X Y) :
    (codeFunctions arrow).forward = forwardCodes arrow ∧
      (codeFunctions arrow).inverse = inverseCodes arrow := ⟨rfl, rfl⟩

/-- Induct on the first tree and split on the second in each case. Identity
and primitive cases reduce directly; reassociation uses the child equation
and `Option.bind_assoc`. -/
-- ALIGN: ATLAS-STABLE-NORMALIZED-FORWARD-CODES.
theorem forwardCodes_comp {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    forwardCodes (AtlasHom.composeAtlasHoms second first) =
      fun code => (forwardCodes first code).bind (forwardCodes second) := by
  induction first with
  | identity => cases second <;> simp [AtlasHom.composeAtlasHoms, forwardCodes]
  | primitive action => cases second <;> simp [AtlasHom.composeAtlasHoms, forwardCodes]
  | composite middle first ihMiddle _ =>
    cases second <;> simp_all [AtlasHom.composeAtlasHoms, forwardCodes, funext_iff, Option.bind_assoc]

/-- The same syntax induction uses reverse-order binds for the inverse;
`Option.bind_assoc` also preserves either unsuccessful lookup. -/
-- ALIGN: ATLAS-STABLE-NORMALIZED-INVERSE-CODES.
theorem inverseCodes_comp {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    inverseCodes (AtlasHom.composeAtlasHoms second first) =
      fun code => (inverseCodes second code).bind (inverseCodes first) := by
  induction first with
  | identity => cases second <;> simp [AtlasHom.composeAtlasHoms, inverseCodes]
  | primitive action => cases second <;> simp [AtlasHom.composeAtlasHoms, inverseCodes]
  | composite middle first ihMiddle _ =>
    cases second <;> simp_all [AtlasHom.composeAtlasHoms, inverseCodes, funext_iff, Option.bind_assoc]

/-- A normalization result retains its owners, compatibility, and both pointwise
observations of the original syntax. -/
structure NormalizedStable (X Y : Atlas) where
  original : Syntax X Y
  result : Syntax X Y
  source : sourceOwner result = sourceOwner original
  target : targetOwner result = targetOwner original
  compatible : OwnersCompatible result ↔ OwnersCompatible original
  forward : ∀ code, forwardCodes result code = forwardCodes original code
  inverse : ∀ code, inverseCodes result code = inverseCodes original code

-- ALIGN: ATLAS-STABLE-NORMALIZATION-PACKAGE.
def normalizedData {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    NormalizedStable X Y where
  original := .composite second first
  result := AtlasHom.composeAtlasHoms second first
  source := (normalized_owners second first).1
  target := (normalized_owners second first).2.1
  compatible := (normalized_owners second first).2.2
  forward code := congrFun (forwardCodes_comp second first) code
  inverse code := congrFun (inverseCodes_comp second first) code

theorem normalizedData_result {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    (normalizedData second first).result = AtlasHom.composeAtlasHoms second first := rfl

-- ALIGN: COALITION-FORWARD-CODE-OBSERVATION.
theorem forwardCodes_at {X Y : Atlas} (arrow : Syntax X Y) (source : X.Coalition) :
    forwardCodes arrow (coalitionElementCode source.val) =
      some (coalitionElementCode ((scopedInsertion arrow).map source).val) := by
  induction arrow with
  | primitive action =>
    simp [forwardCodes, StableTransversalAction.forwardCode, coalition_roundtrip,
      scopedInsertion, StableTransversalAction.canonicalInsertion]
  | identity => rfl
  | composite second first ihSecond ihFirst =>
    simp only [forwardCodes, ihFirst, Option.bind_some]
    exact ihSecond ((scopedInsertion first).map source)

-- ALIGN: COALITION-INVERSE-CODE-OBSERVATION.
theorem inverseCodes_at {X Y : Atlas} (arrow : Syntax X Y) (target : Y.Coalition) :
    inverseCodes arrow (coalitionElementCode target.val) =
      coalitionMaybeCode ((scopedInsertion arrow).preimage target) := by
  induction arrow with
  | primitive action =>
    simp [inverseCodes, StableTransversalAction.inverseCode, coalition_roundtrip,
      scopedInsertion, StableTransversalAction.canonicalInsertion]
  | identity => rfl
  | composite second first ihSecond ihFirst =>
    simp only [inverseCodes, ihSecond]
    cases found : (scopedInsertion second).preimage target with
    | none => simp [coalitionMaybeCode, found, scopedInsertion, DomanialInsertion.comp]
    | some middle =>
      simp only [coalitionMaybeCode, Option.map_some, Option.bind_some]
      rw [ihFirst middle]
      simp [coalitionMaybeCode, scopedInsertion, DomanialInsertion.comp, found]

-- ALIGN: COALITION-IDENTITY-MAP.
def identityMap (X : Atlas) : DomanialInsertion X.Coalition X.Coalition :=
  scopedInsertion (.identity : Syntax X X)

-- ALIGN: COALITION-IDENTITY.
theorem identityMap_observations (X : Atlas) (value : X.Coalition) :
    (identityMap X).map value = value ∧ (identityMap X).preimage value = some value :=
  ⟨rfl, rfl⟩

/-- Simplifying the syntax preserves the complete insertion, including the
chosen inverse on targets outside the image. Induction follows the first tree:
identity and primitive cases reduce after splitting the second tree; the
composite case uses the child equation and `DomanialInsertion.comp_assoc`. -/
theorem scopedInsertion_comp {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M) :
    scopedInsertion (AtlasHom.composeAtlasHoms second first) =
      (scopedInsertion first).comp (scopedInsertion second) := by
  induction first with
  | identity => cases second <;> simp [AtlasHom.composeAtlasHoms, scopedInsertion]
  | primitive action => cases second <;> simp [AtlasHom.composeAtlasHoms, scopedInsertion]
  | composite middle first ihMiddle _ =>
    cases second <;> simp_all [AtlasHom.composeAtlasHoms, scopedInsertion, DomanialInsertion.comp_assoc]

-- ALIGN: COALITION-COMPOSITION.
theorem scopedInsertion_comp_map {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M)
    (source : X.Coalition) :
    (scopedInsertion (AtlasHom.composeAtlasHoms second first)).map source =
      (scopedInsertion second).map ((scopedInsertion first).map source) := by
  rw [scopedInsertion_comp]
  rfl

-- ALIGN: COALITION-COMPOSITION-PREIMAGE.
theorem scopedInsertion_comp_preimage {X M Y : Atlas} (second : Syntax M Y) (first : Syntax X M)
    (target : Y.Coalition) :
    (scopedInsertion (AtlasHom.composeAtlasHoms second first)).preimage target =
      ((scopedInsertion second).preimage target).bind (scopedInsertion first).preimage := by
  rw [scopedInsertion_comp]
  rfl

theorem scopedInsertion_composite_preimage {X M Y : Atlas}
    (second : Syntax M Y) (first : Syntax X M) (target : Y.Coalition) :
    (scopedInsertion (.composite second first)).preimage target =
      ((scopedInsertion second).preimage target).bind (scopedInsertion first).preimage := rfl

end StableCoalitionSyntax

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

theorem coalitionCarrierInsertion_identity (X : Atlas) :
    (identity : StableTransversal X X).coalitionCarrierInsertion = DomanialInsertion.identity _ := by
  exact DomanialInsertion.reindex_identity (coalitionValueEquiv X).symm

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

/-- The inverse package retains an unchanged identity or a function returning
certified sources. Composition builds this function before any target lookup. -/
inductive CoalitionInverse : Atlas → Atlas → Type 2
  | unchanged {X} : CoalitionInverse X X
  | restoring {X Y} : (Y.Coalition → Option X.Coalition) → CoalitionInverse X Y

def CoalitionInverse.apply {X Y : Atlas} : CoalitionInverse X Y → Y.Coalition → Option X.Coalition
  | .unchanged, value => some value
  | .restoring backward, value => backward value

-- ALIGN: ATLAS-STABLE-OWNED-INVERSE-COMPOSITION.
def CoalitionInverse.comp {X Y Z : Atlas} (second : CoalitionInverse Y Z)
    (first : CoalitionInverse X Y) : CoalitionInverse X Z :=
  match second with
  | .unchanged => first
  | .restoring backwardSecond => match first with
    | .unchanged => .restoring backwardSecond
    | .restoring backwardFirst =>
      .restoring (DomanialInsertion.composePartialInverses backwardFirst backwardSecond)

theorem CoalitionInverse.apply_comp {X Y Z : Atlas} (second : CoalitionInverse Y Z)
    (first : CoalitionInverse X Y) (target : Z.Coalition) :
    (second.comp first).apply target = (second.apply target).bind first.apply := by
  cases second <;> cases first <;> simp [comp, apply]

-- ALIGN: ATLAS-STABLE-OWNED-INVERSE.
def coalitionInverse {X Y : Atlas} : StableTransversal X Y → CoalitionInverse X Y
  | .identity => .unchanged
  | .primitive transversal preserves backward leftInverse =>
    .restoring (primitive transversal preserves backward leftInverse).coalitionCarrierInsertion.preimage
  | .composite second first => second.coalitionInverse.comp first.coalitionInverse

theorem coalitionInverse_apply {X Y : Atlas} (arrow : StableTransversal X Y)
    (target : Y.Coalition) :
    arrow.coalitionInverse.apply target = arrow.coalitionCarrierInsertion.preimage target := by
  induction arrow with
  | primitive transversal preserves backward leftInverse => rfl
  | identity =>
    simp [coalitionInverse, CoalitionInverse.apply,
      coalitionCarrierInsertion_identity, DomanialInsertion.identity]
  | @composite X Y Z second first ihSecond ihFirst =>
    have composition : (composite second first).coalitionCarrierInsertion =
        first.coalitionCarrierInsertion.comp second.coalitionCarrierInsertion :=
      DomanialInsertion.reindex_comp _ _ _ _ _
    rw [composition]
    simp only [coalitionInverse, CoalitionInverse.apply_comp, ihSecond]
    simp_rw [ihFirst]
    rfl

-- ALIGN: ATLAS-STABLE-OWNED-PREIMAGE-ELIMINATION.
def withCoalitionPreimage {X Y : Atlas} {Result : Type*} (arrow : StableTransversal X Y)
    (target : Y.Coalition) (usePreimage : X.Coalition → Result) : Option Result :=
  (arrow.coalitionInverse.apply target).map usePreimage

theorem withCoalitionPreimage_eq {X Y : Atlas} {Result : Type*} (arrow : StableTransversal X Y)
    (target : Y.Coalition) (usePreimage : X.Coalition → Result) :
    arrow.withCoalitionPreimage target usePreimage =
      (arrow.coalitionCarrierInsertion.preimage target).map usePreimage := by
  rw [withCoalitionPreimage, coalitionInverse_apply]

end StableTransversal

namespace StableCoalitionSyntax

/-- Interpret the retained primitive actions in the stable category. -/
def toStable {X Y : Atlas} : Syntax X Y → StableTransversal X Y
  | .primitive action => StableTransversal.ofAction action
  | .identity => .identity
  | .composite second first => .composite (toStable second) (toStable first)

/-- The scoped interpreter retains both executable directions of the existing
stable interpretation, including unsuccessful inverse lookups. -/
-- ALIGN: ATLAS-STABLE-SCOPED-INSERTION.
theorem scopedInsertion_agrees {X Y : Atlas} (arrow : Syntax X Y) :
    scopedInsertion arrow = (toStable arrow).coalitionCarrierInsertion := by
  induction arrow with
  | primitive action =>
    change action.canonicalInsertion = (StableTransversal.ofAction action).coalitionCarrierInsertion
    apply DomanialInsertion.ext
    · funext source
      apply Subtype.ext
      rw [StableTransversal.coalitionCarrierInsertion_ofAction_map]
      exact action.forward source
    · funext target
      exact (StableTransversal.coalitionCarrierInsertion_ofAction_preimage action target).symm
  | identity => exact (StableTransversal.coalitionCarrierInsertion_identity _).symm
  | composite second first ihSecond ihFirst =>
    simp only [scopedInsertion, toStable, ihFirst, ihSecond]
    exact (DomanialInsertion.reindex_comp _ _ _ _ _).symm

end StableCoalitionSyntax
end Datra.Executable.Atlas
