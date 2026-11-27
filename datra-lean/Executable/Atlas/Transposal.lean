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

/-- The separate obligation needed to derive path acceptance from the declared
source domain. It includes both subtrees and the middle-domain implication. -/
def Compatible (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    {X Y} : AtlasHom Primitive X Y → Prop
  | .primitive _ => True
  | .identity => True
  | .composite second first =>
      Compatible @domain @forward first ∧ Compatible @domain @forward second ∧
        ∀ source, sourceValid @domain first source →
          sourceValid @domain second (mapObject @forward first source)

theorem sourceValid_pathValid
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    {X Y} (transposal : AtlasHom Primitive X Y)
    (compatible : Compatible @domain @forward transposal)
    (source : Raw X) (valid : sourceValid @domain transposal source) :
    pathValid @domain @forward transposal source := by
  induction transposal with
  | primitive => exact valid
  | identity => trivial
  | composite second first ih₂ ih₁ =>
      exact ⟨ih₁ compatible.1 _ valid, ih₂ compatible.2.1 _ (compatible.2.2 source valid)⟩

theorem leftInverse_of_compatible
    (domain : ∀ {X Y}, Primitive X Y → Raw X → Prop)
    (forward : ∀ {X Y}, Primitive X Y → Raw X → Raw Y)
    (backward : ∀ {X Y}, Primitive X Y → Raw Y → Option (Raw X))
    (primitiveLaw : ∀ {X Y} (operation : Primitive X Y) source,
      domain operation source → backward operation (forward operation source) = some source)
    {X Y} (transposal : AtlasHom Primitive X Y)
    (compatible : Compatible @domain @forward transposal)
    (source : Raw X) (valid : sourceValid @domain transposal source) :
    preimage @backward transposal (mapObject @forward transposal source) = some source :=
  leftInverse @domain @forward @backward @primitiveLaw transposal source
    (sourceValid_pathValid @domain @forward transposal compatible source valid)

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

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION.
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

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-MAP.
theorem comp_map {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (source : TransposalElementData X) :
    (comp second first).map source = second.map (first.map source) := rfl

-- ALIGN: ATLAS-TRANSPOSAL-OWNED-COMPOSITION-PREIMAGE.
theorem comp_preimage {X Y Z : Atlas} (second : TransposalAction Y Z) (first : TransposalAction X Y)
    (target : TransposalElementData Z) :
    (comp second first).preimage target = (second.preimage target).bind first.preimage := rfl

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
      TransposalPath.mapObject (Primitive := TransposalAction) (fun operation => operation.map) (.primitive action) = action.map ∧
      TransposalPath.preimage (Primitive := TransposalAction) (fun operation => operation.preimage) (.primitive action) = action.preimage :=
  ⟨congrArg some ownerMatches, rfl, rfl, rfl, rfl⟩

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

def transposalObjectsSourceOwner {X Y : Atlas} (_ : TransposalObjects X Y) : AtlasOwner :=
  atlasOwner X

def transposalObjectsTargetOwner {X Y : Atlas} (_ : TransposalObjects X Y) : AtlasOwner :=
  atlasOwner Y

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
