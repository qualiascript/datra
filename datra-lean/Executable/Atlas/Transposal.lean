import Executable.Atlas.Morphism
import Executable.Atlas.Order

namespace Datra.Executable.TransposalPath

universe u v w
variable {Object : Type u} {Primitive : Object → Object → Type v}
variable {Raw : Object → Type w}

def sourceOwner {Owner : Type*} (owner : ∀ {X Y}, Primitive X Y → Owner)
    {X Y} : AtlasHom Primitive X Y → Option Owner
  | .primitive operation => some (owner operation)
  | .identity => none
  | .composite second first =>
      match sourceOwner @owner first with
      | none => sourceOwner @owner second
      | some value => some value

def targetOwner {Owner : Type*} (owner : ∀ {X Y}, Primitive X Y → Owner)
    {X Y} : AtlasHom Primitive X Y → Option Owner
  | .primitive operation => some (owner operation)
  | .identity => none
  | .composite second first =>
      match targetOwner @owner second with
      | none => targetOwner @owner first
      | some value => some value

/-- Recover the actual target evidence stored in each primitive, carrying the
supplied evidence unchanged through symbolic identities. -/
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-TARGET-WITNESS.
theorem targetEvidence_owner {Evidence : Object → Type*} {Owner : Type*}
    (primitiveEvidence : ∀ {X Y}, Primitive X Y → Evidence Y)
    (owner : ∀ {X}, Evidence X → Owner) {X Y} (arrow : AtlasHom Primitive X Y) :
    ∀ source : Evidence X,
      owner (arrow.targetEvidence @primitiveEvidence source) =
        (targetOwner (fun operation => owner (primitiveEvidence operation)) arrow).getD (owner source) := by
  induction arrow with
  | primitive => intro source; rfl
  | identity => intro source; rfl
  | composite second first ih₂ ih₁ =>
      intro source
      simp only [AtlasHom.targetEvidence, ih₂, ih₁, targetOwner]
      cases targetOwner (fun operation => owner (primitiveEvidence operation)) second <;> rfl

/-- The native constructors use the shared primitive/identity/composite syntax.
These operations retain raw callbacks, independently of owner compatibility. -/
def mapObject (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    {X Y} : AtlasHom Primitive X Y → Raw X → Raw Y
  | .primitive operation, source => forward operation source
  | .identity, source => source
  | .composite second first, source => mapObject @forward second (mapObject @forward first source)

def preimage (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {X Y} : AtlasHom Primitive X Y → Raw Y → Option (Raw X)
  | .primitive operation, target => backward operation target
  | .identity, target => some target
  | .composite second first, target => (preimage @backward second target).bind (preimage @backward first)

-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-IDENTITY-CALLBACKS.
theorem identity_callbacks
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {X} (source : Raw X) :
    mapObject @forward (.identity : AtlasHom Primitive X X) source = source ∧
      preimage @backward (.identity : AtlasHom Primitive X X) source = some source := ⟨rfl, rfl⟩

def sourceValid (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    {X Y} : AtlasHom Primitive X Y → Raw X → Prop
  | .primitive operation, source => domain operation source
  | .identity, _ => True
  | .composite _ first, source => sourceValid @domain first source

def pathValid (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    {X Y} : AtlasHom Primitive X Y → Raw X → Prop
  | .primitive operation, source => domain operation source
  | .identity, _ => True
  | .composite second first, source =>
      pathValid @domain @forward first source ∧
        pathValid @domain @forward second (mapObject @forward first source)

-- ALIGN: ATLAS-TRANSPOSAL-PATH-SOURCE.
theorem pathValid_sourceValid
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    {X Y} (arrow : AtlasHom Primitive X Y) (source : Raw X)
    (valid : pathValid @domain @forward arrow source) : sourceValid @domain arrow source := by
  induction arrow with
  | primitive => exact valid
  | identity => trivial
  | composite _ _ _ ih => exact ih source valid.1

/-- Path acceptance supplies the primitive domains; witnessed membership is
also necessary for a tree containing only symbolic identities. -/
-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-TARGET-VALID.
theorem targetEvidence_map_valid {Evidence : Object → Type*}
    (primitiveEvidence : ∀ {X Y}, Primitive X Y → Evidence Y)
    (accepted : ∀ {X}, Evidence X → Raw X → Prop)
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (primitiveValid : ∀ {X Y} (operation : Primitive X Y) (source : Raw X),
      domain operation source → accepted (primitiveEvidence operation) (forward operation source))
    {X Y} (arrow : AtlasHom Primitive X Y) :
    ∀ (witness : Evidence X) (source : Raw X), accepted witness source →
      pathValid @domain @forward arrow source →
      accepted (arrow.targetEvidence @primitiveEvidence witness) (mapObject @forward arrow source) := by
  induction arrow with
  | primitive operation => exact fun _ source _ valid => primitiveValid operation source valid
  | identity => exact fun _ _ valid _ => valid
  | composite second first ih₂ ih₁ =>
      intro witness source valid path
      exact ih₂ _ _ (ih₁ witness source valid path.1) path.2

-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-COMPOSITION-CALLBACKS.
theorem composite_callbacks
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {X Y Z} (second : AtlasHom Primitive Y Z) (first : AtlasHom Primitive X Y)
    (source : Raw X) (target : Raw Z) :
    mapObject @forward (.composite second first) source =
      mapObject @forward second (mapObject @forward first source) ∧
    preimage @backward (.composite second first) target =
      (preimage @backward second target).bind (preimage @backward first) ∧
    (pathValid @domain @forward (.composite second first) source ↔
      pathValid @domain @forward first source ∧
        pathValid @domain @forward second (mapObject @forward first source)) := ⟨rfl, rfl, Iff.rfl⟩

-- ALIGN: ATLAS-TRANSPOSAL-LEFT-IDENTITY.
theorem left_identity {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {X Y} (arrow : AtlasHom Primitive X Y) (source : Raw X) (target : Raw Y) :
    mapObject @forward (.composite .identity arrow) source = mapObject @forward arrow source ∧
      preimage @backward (.composite .identity arrow) target = preimage @backward arrow target ∧
      (pathValid @domain @forward (.composite .identity arrow) source ↔ pathValid @domain @forward arrow source) ∧
      sourceOwner @sourceOf (.composite .identity arrow) = sourceOwner @sourceOf arrow ∧
      targetOwner @targetOf (.composite .identity arrow) = targetOwner @targetOf arrow := by
  simp [mapObject, preimage, pathValid, sourceOwner, targetOwner]
  cases sourceOwner @sourceOf arrow <;> rfl

-- ALIGN: ATLAS-TRANSPOSAL-RIGHT-IDENTITY.
theorem right_identity {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {X Y} (arrow : AtlasHom Primitive X Y) (source : Raw X) (target : Raw Y) :
    mapObject @forward (.composite arrow .identity) source = mapObject @forward arrow source ∧
      preimage @backward (.composite arrow .identity) target = preimage @backward arrow target ∧
      (pathValid @domain @forward (.composite arrow .identity) source ↔ pathValid @domain @forward arrow source) ∧
      sourceOwner @sourceOf (.composite arrow .identity) = sourceOwner @sourceOf arrow ∧
      targetOwner @targetOf (.composite arrow .identity) = targetOwner @targetOf arrow := by
  simp [mapObject, preimage, pathValid, sourceOwner, targetOwner]
  cases targetOwner @targetOf arrow <;> rfl

-- ALIGN: ATLAS-TRANSPOSAL-ASSOCIATIVITY.
theorem associativity {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    {W X Y Z} (third : AtlasHom Primitive Y Z) (second : AtlasHom Primitive X Y)
    (first : AtlasHom Primitive W X) (source : Raw W) (target : Raw Z) :
    let left := AtlasHom.composite third (.composite second first)
    let right := AtlasHom.composite (.composite third second) first
    mapObject @forward left source = mapObject @forward right source ∧
      preimage @backward left target = preimage @backward right target ∧
      (sourceValid @domain left source ↔ sourceValid @domain right source) ∧
      (pathValid @domain @forward left source ↔ pathValid @domain @forward right source) ∧
      sourceOwner @sourceOf left = sourceOwner @sourceOf right ∧
      targetOwner @targetOf left = targetOwner @targetOf right := by
  simp [mapObject, preimage, sourceValid, pathValid, sourceOwner, targetOwner, Option.bind_assoc, and_assoc]
  constructor
  · cases sourceOwner @sourceOf first <;> rfl
  · cases targetOwner @targetOf third <;> rfl

/-- This proves the native recursive inverse calculation. It does not replace
the source domain with an intersection or assert matching nominal indices imply
compatibility of the stored owner domains. -/
-- ALIGN: ATLAS-TRANSPOSAL-PATH-LEFT-INVERSE.
theorem leftInverse
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    (primitiveLaw : ∀ {X Y} (operation : Primitive X Y) source,
      domain operation source → backward operation (forward operation source) = some source)
    {X Y} (transposal : AtlasHom Primitive X Y) (source : Raw X)
    (valid : pathValid @domain @forward transposal source) :
    preimage @backward transposal (mapObject @forward transposal source) = some source := by
  induction transposal with
  | primitive operation => exact primitiveLaw operation source valid
  | identity => rfl
  | composite second first ih₂ ih₁ =>
      change (preimage @backward second
        (mapObject @forward second (mapObject @forward first source))).bind
          (preimage @backward first) = some source
      rw [ih₂ _ valid.2]
      exact ih₁ _ valid.1

/-- Complete-owner equality is required at every materialized join. Symbolic
identities have no stored endpoints and preserve the supplied owning witness. -/
def OwnersCompatible {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X Y} : AtlasHom Primitive X Y → Prop
  | .primitive _ => True
  | .identity => True
  | .composite second first =>
      OwnersCompatible @sourceOf @targetOf first ∧ OwnersCompatible @sourceOf @targetOf second ∧
        (targetOwner @targetOf first = none ∨ sourceOwner @sourceOf second = none ∨
          targetOwner @targetOf first = sourceOwner @sourceOf second)

theorem owners_empty {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X Y} (arrow : AtlasHom Primitive X Y) :
    sourceOwner @sourceOf arrow = none ↔ targetOwner @targetOf arrow = none := by
  induction arrow with
  | primitive => simp [sourceOwner, targetOwner]
  | identity => simp [sourceOwner, targetOwner]
  | composite second first ih₂ ih₁ =>
      cases hs : sourceOwner @sourceOf first <;>
        cases ht : targetOwner @targetOf second <;> simp_all [sourceOwner, targetOwner]

/-- Equality of endpoint owners and of the complete join certificate. -/
def SameOwners {Owner : Type*} (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X Y X' Y'} (first : AtlasHom Primitive X Y) (second : AtlasHom Primitive X' Y') : Prop :=
  sourceOwner @sourceOf first = sourceOwner @sourceOf second ∧
  targetOwner @targetOf first = targetOwner @targetOf second ∧
  (OwnersCompatible @sourceOf @targetOf first ↔ OwnersCompatible @sourceOf @targetOf second)

theorem SameOwners.trans {Owner : Type*} {sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner}
    {X Y M N U V} {first : AtlasHom Primitive X Y} {middle : AtlasHom Primitive M N} {last : AtlasHom Primitive U V}
    (a : SameOwners @sourceOf @targetOf first middle) (b : SameOwners @sourceOf @targetOf middle last) :
    SameOwners @sourceOf @targetOf first last :=
  ⟨a.1.trans b.1, a.2.1.trans b.2.1, a.2.2.trans b.2.2⟩

theorem sameOwners_comp_left {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X M Y} (first : AtlasHom Primitive X M) (second other : AtlasHom Primitive M Y)
    (same : SameOwners @sourceOf @targetOf second other) :
    SameOwners @sourceOf @targetOf (.composite second first) (.composite other first) := by
  rcases same with ⟨hs, ht, hc⟩
  simp [SameOwners, sourceOwner, targetOwner, OwnersCompatible, hs, ht, hc]

-- ALIGN: ATLAS-TRANSPOSAL-COMPOSITION-OWNERS.
theorem composition_owners {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X M Y} (second : AtlasHom Primitive M Y) (first : AtlasHom Primitive X M) :
    sourceOwner @sourceOf (.composite second first) =
      (sourceOwner @sourceOf first).orElse (fun _ => sourceOwner @sourceOf second) ∧
    targetOwner @targetOf (.composite second first) =
      (targetOwner @targetOf second).orElse (fun _ => targetOwner @targetOf first) ∧
    (OwnersCompatible @sourceOf @targetOf (.composite second first) ↔
      OwnersCompatible @sourceOf @targetOf first ∧ OwnersCompatible @sourceOf @targetOf second ∧
      (targetOwner @targetOf first = none ∨ sourceOwner @sourceOf second = none ∨
        targetOwner @targetOf first = sourceOwner @sourceOf second)) := by
  constructor
  · cases hs : sourceOwner @sourceOf first <;> simp [sourceOwner, hs, Option.orElse]
  constructor
  · cases ht : targetOwner @targetOf second <;> simp [targetOwner, ht, Option.orElse]
  · rfl

-- ALIGN: ATLAS-TRANSPOSAL-OWNER-ASSOCIATIVITY.
theorem owners_associativity {Owner : Type*}
    (sourceOf targetOf : ∀ {X Y}, Primitive X Y → Owner)
    {X M N Y} (third : AtlasHom Primitive N Y) (second : AtlasHom Primitive M N)
    (first : AtlasHom Primitive X M) :
    sourceOwner @sourceOf (.composite third (.composite second first)) =
      sourceOwner @sourceOf (.composite (.composite third second) first) ∧
    targetOwner @targetOf (.composite third (.composite second first)) =
      targetOwner @targetOf (.composite (.composite third second) first) ∧
    (OwnersCompatible @sourceOf @targetOf (.composite third (.composite second first)) ↔
      OwnersCompatible @sourceOf @targetOf (.composite (.composite third second) first)) := by
  constructor
  · cases hs : sourceOwner @sourceOf first <;> cases hm : sourceOwner @sourceOf second <;>
      simp [sourceOwner, hs, hm]
  constructor
  · cases ht : targetOwner @targetOf third <;> cases hm : targetOwner @targetOf second <;>
      simp [targetOwner, ht, hm]
  have empty := owners_empty @sourceOf @targetOf second
  cases hs : sourceOwner @sourceOf second <;> cases ht : targetOwner @targetOf second <;>
    simp_all [OwnersCompatible, sourceOwner, targetOwner, and_assoc, and_comm, and_left_comm]

/-- The existing syntax composition preserves owner evidence when its second
subtree is owned by the first subtree's recovered target witness. -/
-- ALIGN: ATLAS-TRANSPOSAL-OWNER-COMPATIBLE-COMPOSITION.
theorem ownerCompatible_comp {Evidence : Object → Type*} {Owner : Type*}
    (primitiveEvidence : ∀ {X Y}, Primitive X Y → Evidence Y)
    (owner : ∀ {X}, Evidence X → Owner)
    (sourceOf : ∀ {X Y}, Primitive X Y → Owner)
    {X M Y} (first : AtlasHom Primitive X M) (second : AtlasHom Primitive M Y) (witness : Evidence X)
    (firstCompatible : OwnersCompatible @sourceOf (fun operation => owner (primitiveEvidence operation)) first)
    (secondCompatible : OwnersCompatible @sourceOf (fun operation => owner (primitiveEvidence operation)) second)
    (firstOwner : sourceOwner @sourceOf first = none ∨ sourceOwner @sourceOf first = some (owner witness))
    (secondOwner : sourceOwner @sourceOf second = none ∨ sourceOwner @sourceOf second =
      some (owner (first.targetEvidence @primitiveEvidence witness))) :
    OwnersCompatible @sourceOf (fun operation => owner (primitiveEvidence operation)) (.composite second first) ∧
      (sourceOwner @sourceOf (.composite second first) = none ∨
        sourceOwner @sourceOf (.composite second first) = some (owner witness)) := by
  have firstEmpty := owners_empty @sourceOf (fun operation => owner (primitiveEvidence operation)) first
  have recovered := targetEvidence_owner @primitiveEvidence @owner first witness
  cases hs : sourceOwner @sourceOf first <;>
    cases ht : targetOwner (fun operation => owner (primitiveEvidence operation)) first <;>
    cases hn : sourceOwner @sourceOf second <;> simp_all [OwnersCompatible, sourceOwner]

/-- Owner compatibility discharges every path-domain premise from membership
in the supplied source witness, without treating a symbolic identity's total
raw source predicate as owning membership. -/
-- ALIGN: ATLAS-TRANSPOSAL-OWNER-COMPATIBLE-PATH.
theorem ownerCompatible_pathValid {Evidence : Object → Type*} {Owner : Type*}
    (primitiveEvidence : ∀ {X Y}, Primitive X Y → Evidence Y)
    (owner : ∀ {X}, Evidence X → Owner)
    (sourceOf : ∀ {X Y}, Primitive X Y → Owner)
    (accepted : ∀ {X}, Evidence X → Raw X → Prop)
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (primitiveDomain : ∀ {X Y} (operation : Primitive X Y) (witness : Evidence X) (source : Raw X),
      sourceOf operation = owner witness → accepted witness source → domain operation source)
    (primitiveValid : ∀ {X Y} (operation : Primitive X Y) (source : Raw X),
      domain operation source → accepted (primitiveEvidence operation) (forward operation source))
    {X Y} (arrow : AtlasHom Primitive X Y) :
    ∀ (witness : Evidence X) (source : Raw X),
      OwnersCompatible @sourceOf (fun operation => owner (primitiveEvidence operation)) arrow →
      (sourceOwner @sourceOf arrow = none ∨ sourceOwner @sourceOf arrow = some (owner witness)) →
      accepted witness source → pathValid @domain @forward arrow source := by
  induction arrow with
  | primitive operation =>
      intro witness source _ ownerMatches valid
      apply primitiveDomain operation witness source _ valid
      simpa [sourceOwner] using ownerMatches
  | identity => intro _ _ _ _ _; trivial
  | composite second first ih₂ ih₁ =>
      intro witness source compatible ownerMatches valid
      have firstEmpty := owners_empty @sourceOf (fun operation => owner (primitiveEvidence operation)) first
      have recovered := targetEvidence_owner @primitiveEvidence @owner first witness
      have joins := compatible.2.2
      have stages :
          (sourceOwner @sourceOf first = none ∨ sourceOwner @sourceOf first = some (owner witness)) ∧
          (sourceOwner @sourceOf second = none ∨ sourceOwner @sourceOf second =
            some (owner (first.targetEvidence @primitiveEvidence witness))) := by
        cases hs : sourceOwner @sourceOf first <;>
          cases ht : targetOwner (fun operation => owner (primitiveEvidence operation)) first <;>
          cases hn : sourceOwner @sourceOf second <;> simp_all [sourceOwner]
      have firstPath := ih₁ witness source compatible.1 stages.1 valid
      have middleValid := targetEvidence_map_valid @primitiveEvidence @accepted @domain @forward
        @primitiveValid first witness source valid firstPath
      exact ⟨firstPath, ih₂ _ _ compatible.2.1 stages.2 middleValid⟩

end Datra.Executable.TransposalPath

namespace Datra.Executable.Atlas
open CategoryTheory

abbrev TransposalElementData.Accepted (X : Atlas) :=
  {element : TransposalElementData X // TransposalElementData.valid X element}

/-- Raw lookup remains observable. Membership and the inverse law apply on the
actual owners' accepted carriers, without filtering any lookup result. -/
structure TransposalAction (X Y : Atlas) where
  map : TransposalElementData X → TransposalElementData Y
  preimage : TransposalElementData Y → Option (TransposalElementData X)
  map_valid : ∀ source, TransposalElementData.valid X source → TransposalElementData.valid Y (map source)
  preimage_valid : ∀ target source, TransposalElementData.valid Y target → preimage target = some source → TransposalElementData.valid X source
  leftInverse : ∀ source, TransposalElementData.valid X source → preimage (map source) = some source

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-ACTION.
def transposalAction {X Y : Atlas}
    (forward : TransposalElementData X → TransposalElementData Y)
    (backward : TransposalElementData Y → Option (TransposalElementData X))
    (forwardValid : ∀ source, TransposalElementData.valid X source → TransposalElementData.valid Y (forward source))
    (backwardValid : ∀ target source, TransposalElementData.valid Y target → backward target = some source → TransposalElementData.valid X source)
    (leftInverse : ∀ source, TransposalElementData.valid X source → backward (forward source) = some source) : TransposalAction X Y :=
  ⟨forward, backward, forwardValid, backwardValid, leftInverse⟩

namespace TransposalAction

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-LEFT-INVERSE.
theorem accepted_leftInverse {X Y : Atlas} (action : TransposalAction X Y)
    (source : TransposalElementData X) (valid : TransposalElementData.valid X source) :
    action.preimage (action.map source) = some source := action.leftInverse source valid

def acceptedPreimage {X Y : Atlas} (action : TransposalAction X Y)
    (target : TransposalElementData.Accepted Y) : Option (TransposalElementData.Accepted X) :=
  match found : action.preimage target.val with
  | none => none
  | some source => some ⟨source, action.preimage_valid _ _ target.property found⟩

theorem acceptedPreimage_raw {X Y : Atlas} (action : TransposalAction X Y)
    (target : TransposalElementData.Accepted Y) :
    (action.acceptedPreimage target).map Subtype.val = action.preimage target.val := by
  unfold acceptedPreimage
  split <;> simp_all

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-INSERTION.
def objectInsertion {X Y : Atlas} (action : TransposalAction X Y) :
    DomanialInsertion (TransposalElementData.Accepted X) (TransposalElementData.Accepted Y) where
  map source := ⟨action.map source.val, action.map_valid _ source.property⟩
  preimage := action.acceptedPreimage
  leftInverse source := by
    apply Option.map_injective Subtype.val_injective
    rw [acceptedPreimage_raw]
    exact action.leftInverse source.val source.property

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-IDENTITY.
def identity (X : Atlas) : TransposalAction X X where
  map := id
  preimage := some
  map_valid _ valid := valid
  preimage_valid _ _ valid found := by cases found; exact valid
  leftInverse _ _ := rfl

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-IDENTITY-CALLBACKS.
theorem identity_callbacks (X : Atlas) (source : TransposalElementData X) :
    (identity X).map source = source ∧ (identity X).preimage source = some source := ⟨rfl, rfl⟩

def comp {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y) :
    TransposalAction X Z where
  map source := second.map (first.map source)
  preimage := DomanialInsertion.composePartialInverses first.preimage second.preimage
  map_valid source valid := second.map_valid _ (first.map_valid source valid)
  preimage_valid target source valid found := by
    cases middleFound : second.preimage target with
    | none => simp [DomanialInsertion.composePartialInverses, middleFound] at found
    | some middle =>
      exact first.preimage_valid middle source (second.preimage_valid _ _ valid middleFound)
        (by simpa [DomanialInsertion.composePartialInverses, middleFound] using found)
  leftInverse source valid := by
    simp [DomanialInsertion.composePartialInverses,
      second.leftInverse _ (first.map_valid source valid), first.leftInverse source valid]

theorem comp_map {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (source : TransposalElementData X) :
    (comp second first).map source = second.map (first.map source) := rfl

theorem comp_preimage {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (target : TransposalElementData Z) :
    (comp second first).preimage target = (second.preimage target).bind first.preimage := rfl

/-- Equality of the complete middle owners suffices, independently of how the
hidden endpoint carriers were packaged. Both raw callbacks are transported. -/
-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION.
def compAlongOwner {X Y₁ Y₂ Z : Atlas} (second : TransposalAction Y₂ Z)
    (first : TransposalAction X Y₁) (owners : atlasOwner Y₁ = atlasOwner Y₂) : TransposalAction X Z :=
  let sameOwner : Y₂ = Y₁ := (congrArg AtlasOwner.value owners).symm
  comp (sameOwner ▸ second) first

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-MAP.
theorem compAlongOwner_map {X Y₁ Y₂ Z : Atlas} (second : TransposalAction Y₂ Z)
    (first : TransposalAction X Y₁) (owners : atlasOwner Y₁ = atlasOwner Y₂)
    (source : TransposalElementData X) :
    let sameOwner : Y₁ = Y₂ := congrArg AtlasOwner.value owners
    (compAlongOwner second first owners).map source =
      second.map (sameOwner ▸ first.map source) := by
  have sameOwner : Y₁ = Y₂ := congrArg AtlasOwner.value owners
  cases sameOwner
  rfl

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-PREIMAGE.
theorem compAlongOwner_preimage {X Y₁ Y₂ Z : Atlas} (second : TransposalAction Y₂ Z)
    (first : TransposalAction X Y₁) (owners : atlasOwner Y₁ = atlasOwner Y₂)
    (target : TransposalElementData Z) :
    let sameOwner : Y₂ = Y₁ := (congrArg AtlasOwner.value owners).symm
    (compAlongOwner second first owners).preimage target =
      (second.preimage target).bind (fun middle =>
        first.preimage (sameOwner ▸ middle)) := by
  have sameOwner : Y₁ = Y₂ := congrArg AtlasOwner.value owners
  cases sameOwner
  rfl

end TransposalAction

/-! With actual owners as indices, source membership propagates through every
stage, including symbolic identities. The native witness bridge must establish
this owner-indexed interpretation rather than infer it from scope equality. -/
namespace OwnedTransposalSyntax

abbrev Syntax := AtlasHom TransposalAction

def sourceOwner {X Y : Atlas} (arrow : Syntax X Y) : Option AtlasOwner :=
  TransposalPath.sourceOwner (fun {X _} _ => atlasOwner X) arrow

def targetOwner {X Y : Atlas} (arrow : Syntax X Y) : Option AtlasOwner :=
  TransposalPath.targetOwner (fun {_ Y} _ => atlasOwner Y) arrow

-- ALIGN: ATLAS-TRANSPOSAL-NATIVE-OWNERS.
theorem primitive_retains {X Y : Atlas} (witness : AtlasWitness)
    (action : TransposalAction X Y) (ownerMatches : atlasOwner X = atlasWitnessOwner witness) :
    sourceOwner (.primitive action) = some (atlasWitnessOwner witness) ∧
      targetOwner (.primitive action) = some (atlasOwner Y) ∧
      TransposalPath.sourceValid (Primitive := TransposalAction) (fun {X _} _ source =>
        TransposalElementData.valid X source) (.primitive action) = TransposalElementData.valid X ∧
      TransposalPath.pathValid (Primitive := TransposalAction) (fun {X _} _ source =>
        TransposalElementData.valid X source) (fun operation => operation.map)
          (.primitive action) = TransposalElementData.valid X ∧
      TransposalPath.mapObject (Primitive := TransposalAction) (fun operation => operation.map) (.primitive action) = action.map ∧
      TransposalPath.preimage (Primitive := TransposalAction) (fun operation => operation.preimage) (.primitive action) = action.preimage :=
  ⟨congrArg some ownerMatches, rfl, rfl, rfl, rfl, rfl⟩

def mapObject {X Y : Atlas} (arrow : Syntax X Y) : TransposalElementData X → TransposalElementData Y :=
  TransposalPath.mapObject (fun action => action.map) arrow

def pathValid {X Y : Atlas} (arrow : Syntax X Y) (source : TransposalElementData X) : Prop :=
  TransposalPath.pathValid (fun {X _} _ source => TransposalElementData.valid X source)
    (fun action => action.map) arrow source

theorem map_valid {X Y : Atlas} (arrow : Syntax X Y) (source : TransposalElementData X)
    (valid : TransposalElementData.valid X source) :
    TransposalElementData.valid Y (mapObject arrow source) := by
  induction arrow with
  | primitive action => exact action.map_valid source valid
  | identity => exact valid
  | composite second first ih₂ ih₁ => exact ih₂ _ (ih₁ _ valid)

theorem path_valid {X Y : Atlas} (arrow : Syntax X Y) (source : TransposalElementData X)
    (valid : TransposalElementData.valid X source) : pathValid arrow source := by
  induction arrow with
  | primitive => exact valid
  | identity => trivial
  | composite second first ih₂ ih₁ => exact ⟨ih₁ _ valid, ih₂ _ (map_valid first source valid)⟩

theorem leftInverse {X Y : Atlas} (arrow : Syntax X Y) (source : TransposalElementData X)
    (valid : TransposalElementData.valid X source) :
    TransposalPath.preimage (fun action => action.preimage) arrow (mapObject arrow source) = some source :=
  TransposalPath.leftInverse (Primitive := TransposalAction) (Raw := TransposalElementData)
    (fun {X _} _ source => TransposalElementData.valid X source)
    (fun action => action.map) (fun action => action.preimage)
    (fun action source accepted => action.leftInverse source accepted)
    arrow source (path_valid arrow source valid)

end OwnedTransposalSyntax

def mapTransposalMorphismElement {X Y : Atlas}
    (object : PageElement X.pages → PageElement Y.pages)
    (source : TransposalElementData X) : TransposalElementData Y :=
  TransposalElementData.ofSource Y
    (object (source.source.normalize (X.pages.depth - 1) X.pages.depth))

-- ALIGN: ATLAS-TRANSPOSAL-MORPHISM-ELEMENT.
theorem mapTransposalMorphismElement_valid {X Y : Atlas}
    (object : PageElement X.pages → PageElement Y.pages)
    (preservesTrace : ∀ source, X.pages.traceValid source = true → Y.pages.traceValid (object source) = true)
    (source : TransposalElementData X) (valid : TransposalElementData.valid X source) :
    TransposalElementData.valid Y (mapTransposalMorphismElement object source) :=
  (TransposalElementData.at_valid Y _ (preservesTrace _
    (X.pages.traceValid_normalize X.pagination.folio.valid _ valid.1))).1

theorem mapTransposalMorphismElement_primitive {X Y : Atlas}
    (operation : PrimitiveAtlasMorphism X Y)
    (object : PageElement X.pages → PageElement Y.pages)
    (objectMatches : ∀ source : X.Element, object source.val = (operation.object source).val)
    (source : X.TransposalElement) :
    mapTransposalMorphismElement object (TransposalElementData.ofElement source) =
      TransposalElementData.ofElement
        (TransposalElement.mapHom (.primitive (.primitive operation)) source) := by
  change TransposalElementData.ofSource Y (object source.val.normalize.val) =
    TransposalElementData.ofSource Y (operation.object source.val.normalize).val
  rw [objectMatches source.val.normalize]

/-- Materialization hides dependent morphism indices while retaining its one
raw object function and the two owner domains used to certify that function. -/
structure TransposalObjects (X Y : Atlas) where
  map : TransposalElementData X → TransposalElementData Y
  map_valid : ∀ source, TransposalElementData.valid X source → TransposalElementData.valid Y (map source)

-- ALIGN: ATLAS-TRANSPOSAL-MIDDLE-DOMAIN.
theorem transposalObjects_middle_valid {X M N Y : Atlas}
    (first : TransposalObjects X M) (_second : TransposalObjects N Y)
    (owners : atlasOwner M = atlasOwner N)
    (source : TransposalElementData X) (valid : TransposalElementData.valid X source) :
    let sameOwner : M = N := congrArg AtlasOwner.value owners
    TransposalElementData.valid N (sameOwner ▸ first.map source) :=
  (TransposalElementData.owners_agree M N owners (first.map source)).mp (first.map_valid source valid)

def transposalObjectsSourceOwner {X Y : Atlas} (_ : TransposalObjects X Y) : AtlasOwner :=
  atlasOwner X

def transposalObjectsTargetOwner {X Y : Atlas} (_ : TransposalObjects X Y) : AtlasOwner :=
  atlasOwner Y

def transposalObjectsTargetWitness {X Y : Atlas} (_ : TransposalObjects X Y) : AtlasWitness :=
  atlasWitness Y

-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-TARGET-WITNESS.
theorem transposalObjectsTargetWitness_owner {X Y : Atlas} (objects : TransposalObjects X Y) :
    atlasWitnessOwner (transposalObjectsTargetWitness objects) = transposalObjectsTargetOwner objects := rfl

/-- In the owner-indexed model, materialization retains the Hom's target Atlas. -/
def atlasHomTargetWitness {X Y : Atlas} (_ : Hom X Y) : AtlasWitness := atlasWitness Y

-- ALIGN: ATLAS-TRANSPOSAL-HOM-TARGET-WITNESS.
theorem atlasHomTargetWitness_owner {X Y : Atlas} (hom : Hom X Y) (objects : TransposalObjects X Y) :
    atlasWitnessOwner (atlasHomTargetWitness hom) = transposalObjectsTargetOwner objects := rfl

-- ALIGN: ATLAS-TRANSPOSAL-DERIVED-MIDDLE-DOMAIN.
theorem transposalObjects_next_source_valid {X M N Y : Atlas}
    (first : TransposalObjects X M) (second : TransposalObjects N Y)
    (owners : atlasOwner N = atlasWitnessOwner (transposalObjectsTargetWitness first))
    (source : TransposalElementData X) (valid : TransposalElementData.valid X source) :
    let sameOwner : M = N := congrArg AtlasOwner.value owners.symm
    TransposalElementData.valid N (sameOwner ▸ first.map source) :=
  transposalObjects_middle_valid first second owners.symm source valid

def transposalObjects {X Y : Atlas}
    (object : PageElement X.pages → PageElement Y.pages)
    (preservesTrace : ∀ source, X.pages.traceValid source = true → Y.pages.traceValid (object source) = true) :
    TransposalObjects X Y :=
  ⟨mapTransposalMorphismElement object, mapTransposalMorphismElement_valid object preservesTrace⟩

-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-OWNERS.
theorem transposalObjects_owners {X Y : Atlas}
    (object : PageElement X.pages → PageElement Y.pages)
    (preservesTrace : ∀ source, X.pages.traceValid source = true → Y.pages.traceValid (object source) = true) :
    transposalObjectsSourceOwner (transposalObjects object preservesTrace) = atlasOwner X ∧
      transposalObjectsTargetOwner (transposalObjects object preservesTrace) = atlasOwner Y :=
  ⟨rfl, rfl⟩

-- ALIGN: ATLAS-TRANSPOSAL-OBJECTS-ELIMINATION.
def withTransposalObjects {X Y : Atlas} {Result : Sort*} (objects : TransposalObjects X Y)
    (useObjects : (sourceOwner targetOwner : Atlas) → sourceOwner = X → targetOwner = Y →
      (forward : TransposalElementData X → TransposalElementData Y) →
      (∀ source, TransposalElementData.valid X source → TransposalElementData.valid Y (forward source)) →
      (∀ source, forward source = objects.map source) → Result) : Result :=
  useObjects X Y rfl rfl objects.map objects.map_valid (fun _ => rfl)

/-- Runtime transposals retain their symbolic Atlas arrow and executable
object insertion. The agreement proof records their checked construction. -/
structure Transposal (X Y : Atlas) where
  hom : Hom X Y
  objectInsertion : DomanialInsertion X.TransposalElement Y.TransposalElement
  object_eq : ∀ x, objectInsertion.map x = TransposalElement.mapHom hom x

def transposal {X Y : Atlas} (hom : Hom X Y)
    (preimage : Y.TransposalElement → Option X.TransposalElement)
    (leftInverse : ∀ x, preimage (TransposalElement.mapHom hom x) = some x) : Transposal X Y :=
  ⟨hom, ⟨TransposalElement.mapHom hom, preimage, leftInverse⟩, fun _ => rfl⟩

namespace Transposal

def identity (X : Atlas) : Transposal X X where
  hom := .identity
  objectInsertion := DomanialInsertion.identity _
  object_eq x := (Subtype.ext x.property).symm

def comp {X Y Z : Atlas} (second : Transposal Y Z) (first : Transposal X Y) : Transposal X Z where
  hom := AtlasHom.composeAtlasHoms second.hom first.hom
  objectInsertion := first.objectInsertion.comp second.objectInsertion
  object_eq x := by
    change second.objectInsertion.map (first.objectInsertion.map x) = _
    rw [second.object_eq, first.object_eq, TransposalElement.mapHom_compose]

def mapObject {X Y : Atlas} (f : Transposal X Y) : X.TransposalElement → Y.TransposalElement :=
  f.objectInsertion.map

def preimage {X Y : Atlas} (f : Transposal X Y) : Y.TransposalElement → Option X.TransposalElement :=
  f.objectInsertion.preimage

-- ALIGN: ATLAS-TRANSPOSAL-LEFT-INVERSE.
theorem leftInverse {X Y : Atlas} (f : Transposal X Y) (x : X.TransposalElement) :
    f.preimage (f.mapObject x) = some x := f.objectInsertion.leftInverse x

theorem mapObject_injective {X Y : Atlas} (f : Transposal X Y) : Function.Injective f.mapObject :=
  f.objectInsertion.injective

-- ALIGN: ATLAS-TRANSPOSAL-INJECTIVITY.
theorem mapObject_interpretation {X Y : Atlas} (f : Transposal X Y) (x : X.TransposalElement) :
    (f.mapObject x).toSemantics = f.hom.finiteSemantics.Pa.obj x.toSemantics := by
  rw [mapObject, f.object_eq]
  exact TransposalElement.mapHom_interpretation f.hom x

theorem semantic_injective {X Y : Atlas} (f : Transposal X Y) :
    Datra.Semantics.IsTransposal f.hom.finiteSemantics := by
  intro x y h
  have hm : (TransposalElement.mapHom f.hom (TransposalElement.fromSemantics X x)).toSemantics =
      (TransposalElement.mapHom f.hom (TransposalElement.fromSemantics X y)).toSemantics := by
    simpa only [TransposalElement.mapHom_interpretation,
      TransposalElement.toSemantics_fromSemantics] using h
  have he := (TransposalElement.semanticsEquiv Y).injective hm
  rw [← f.object_eq, ← f.object_eq] at he
  have hs := f.objectInsertion.injective he
  simpa only [TransposalElement.toSemantics_fromSemantics] using
    congrArg TransposalElement.toSemantics hs

noncomputable def toSemantics {X Y : Atlas} (f : Transposal X Y) :
    (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrap) ⟶
      (WideSubcategory.mk Y.toSemantics : Datra.Semantics.AtlTrap) :=
  ⟨f.hom.finiteSemantics, f.semantic_injective⟩

-- ALIGN: ATLAS-TRANSPOSAL-IDENTITY.
theorem toSemantics_identity (X : Atlas) :
    (identity X).toSemantics = 𝟙 (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrap) := by
  apply Subtype.ext
  exact Hom.finiteSemantics_identity X

-- ALIGN: ATLAS-TRANSPOSAL-COMPOSITION.
theorem toSemantics_comp {X Y Z : Atlas} (second : Transposal Y Z) (first : Transposal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact Hom.finiteSemantics_compose second.hom first.hom

end Transposal

namespace TransposalAction

/-- The raw object function must agree with the supplied Hom on genuine owning
cells before its inverse certificate can justify the written transposal. -/
def Agrees {X Y : Atlas} (action : TransposalAction X Y) (hom : Hom X Y) : Prop :=
  ∀ source : X.TransposalElement,
    action.map (TransposalElementData.ofElement source) =
      TransposalElementData.ofElement (TransposalElement.mapHom hom source)

theorem semantic_injective {X Y : Atlas} (action : TransposalAction X Y) (hom : Hom X Y)
    (agrees : action.Agrees hom) : Datra.Semantics.IsTransposal hom.finiteSemantics := by
  intro x y same
  let left := TransposalElement.fromSemantics X x
  let right := TransposalElement.fromSemantics X y
  have mappedSame : TransposalElement.mapHom hom left = TransposalElement.mapHom hom right := by
    apply (TransposalElement.semanticsEquiv Y).injective
    change (TransposalElement.mapHom hom left).toSemantics =
      (TransposalElement.mapHom hom right).toSemantics
    simpa only [left, right, TransposalElement.mapHom_interpretation,
      TransposalElement.toSemantics_fromSemantics] using same
  have rawSame : action.map (TransposalElementData.ofElement left) =
      action.map (TransposalElementData.ofElement right) := by
    rw [agrees left, agrees right, mappedSame]
  have decoded := congrArg action.preimage rawSame
  rw [action.leftInverse _ (TransposalElementData.ofElement_valid left),
    action.leftInverse _ (TransposalElementData.ofElement_valid right)] at decoded
  have sameElements : left = right := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg TransposalElementData.source (Option.some.inj decoded)
  simpa only [left, right, TransposalElement.toSemantics_fromSemantics] using
    congrArg TransposalElement.toSemantics sameElements

noncomputable def toSemantics {X Y : Atlas} (action : TransposalAction X Y)
    (hom : Hom X Y) (agrees : action.Agrees hom) :
    (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrap) ⟶
      (WideSubcategory.mk Y.toSemantics : Datra.Semantics.AtlTrap) :=
  ⟨hom.finiteSemantics, action.semantic_injective hom agrees⟩

theorem identity_agrees (X : Atlas) : (identity X).Agrees .identity := by
  intro source
  exact congrArg TransposalElementData.ofElement ((Transposal.identity X).object_eq source)

theorem comp_agrees {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (secondHom : Hom Y Z) (firstHom : Hom X Y)
    (secondAgrees : second.Agrees secondHom) (firstAgrees : first.Agrees firstHom) :
    (comp second first).Agrees (AtlasHom.composeAtlasHoms secondHom firstHom) := by
  intro source
  rw [comp_map, firstAgrees source, secondAgrees, TransposalElement.mapHom_compose]

theorem toSemantics_identity (X : Atlas) :
    (identity X).toSemantics .identity (identity_agrees X) =
      𝟙 (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrap) := by
  apply Subtype.ext
  exact Hom.finiteSemantics_identity X

theorem toSemantics_comp {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (secondHom : Hom Y Z) (firstHom : Hom X Y)
    (secondAgrees : second.Agrees secondHom) (firstAgrees : first.Agrees firstHom) :
    (comp second first).toSemantics (AtlasHom.composeAtlasHoms secondHom firstHom)
        (comp_agrees second first secondHom firstHom secondAgrees firstAgrees) =
      first.toSemantics firstHom firstAgrees ≫ second.toSemantics secondHom secondAgrees := by
  apply Subtype.ext
  exact Hom.finiteSemantics_compose secondHom firstHom

end TransposalAction
end Datra.Executable.Atlas
