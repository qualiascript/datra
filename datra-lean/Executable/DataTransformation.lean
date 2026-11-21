import Executable.Atlas.Morphism

namespace Datra.Executable

universe v w t
variable {Object : Type v} (Primitive : Object → Object → Type w)

/-- The named wrapper used to store a rank-polymorphic action. -/
structure DataTransformationAction (Value : Object → Type t) where
  map : ∀ {X Y}, AtlasHom Primitive X Y → Value Y → Value X

-- ALIGN: PRESHEAF-ACTION-ELIM.
variable {Primitive} in
def DataTransformationAction.apply {Value : Object → Type t}
    (action : DataTransformationAction Primitive Value) {X Y}
    (arrow : AtlasHom Primitive X Y) (value : Value Y) : Value X := action.map arrow value

/-- An indexed value family and its checked contravariant action. -/
structure DataTransformation (Value : Object → Type t) where
  storedAction : DataTransformationAction Primitive Value
  identity : ∀ {X} (x : Value X), storedAction.map .identity x = x
  composition : ∀ {X Y Z} (second : AtlasHom Primitive Y Z)
    (first : AtlasHom Primitive X Y) (x : Value Z),
    storedAction.map (AtlasHom.presheafCompose second first) x =
      storedAction.map first (storedAction.map second x)

-- ALIGN: PRESHEAF-MAP.
variable {Primitive} in
def DataTransformation.action {Value : Object → Type t}
    (transformation : DataTransformation Primitive Value) {X Y}
    (arrow : AtlasHom Primitive X Y) (value : Value Y) : Value X :=
  transformation.storedAction.apply arrow value

-- ALIGN: PRESHEAF-PACKAGE.
def dataTransformation {Value : Object → Type t}
    (action : ∀ {X Y}, AtlasHom Primitive X Y → Value Y → Value X)
    (identity : ∀ {X} (value : Value X), action .identity value = value)
    (composition : ∀ {X Y Z} (second : AtlasHom Primitive Y Z)
      (first : AtlasHom Primitive X Y) (value : Value Z),
      action (AtlasHom.presheafCompose second first) value = action first (action second value)) :
    DataTransformation Primitive Value := ⟨⟨action⟩, identity, composition⟩

-- ALIGN: PRESHEAF-IDENTITY.
theorem dataTransformationIdentity {Value : Object → Type t}
    (transformation : DataTransformation Primitive Value) {X} (value : Value X) :
    transformation.action .identity value = value := transformation.identity value

-- ALIGN: PRESHEAF-COMPOSITION.
theorem dataTransformationComposition {Value : Object → Type t}
    (transformation : DataTransformation Primitive Value) {X Y Z}
    (second : AtlasHom Primitive Y Z) (first : AtlasHom Primitive X Y) (value : Value Z) :
    transformation.action (AtlasHom.presheafCompose second first) value =
      transformation.action first (transformation.action second value) :=
  transformation.composition second first value

structure Yoneda (represented atlas : Object) where
  getYoneda : AtlasHom Primitive atlas represented

variable {Primitive}
def mapYoneda {represented X Y : Object} (arrow : AtlasHom Primitive X Y)
    (value : Yoneda Primitive represented Y) : Yoneda Primitive represented X :=
  ⟨AtlasHom.presheafCompose value.getYoneda arrow⟩

-- ALIGN: YONEDA-IDENTITY.
theorem yonedaIdentity {represented X : Object} (value : Yoneda Primitive represented X) :
    mapYoneda .identity value = value := by cases value; rfl

-- ALIGN: YONEDA-COMPOSITION.
theorem yonedaComposition {represented X Y Z : Object} (second : AtlasHom Primitive Y Z)
    (first : AtlasHom Primitive X Y) (value : Yoneda Primitive represented Z) :
    mapYoneda (AtlasHom.presheafCompose second first) value =
      mapYoneda first (mapYoneda second value) := by
  exact congrArg Yoneda.mk (AtlasHom.presheafAssociativity value.getYoneda second first)

-- ALIGN: YONEDA-PACKAGE.
def yoneda (represented : Object) :
    DataTransformation Primitive (Yoneda Primitive represented) where
  storedAction := ⟨mapYoneda⟩
  identity := yonedaIdentity
  composition := yonedaComposition

-- ALIGN: YONEDA-PACKAGE-ACTION.
theorem yonedaActionAgrees {represented X Y : Object} (arrow : AtlasHom Primitive X Y)
    (value : Yoneda Primitive represented Y) :
    (yoneda represented).action arrow value = mapYoneda arrow value := rfl

structure DataTransformationComponent (Value₁ Value₂ : Object → Type t) where
  map : ∀ {X}, Value₁ X → Value₂ X

-- ALIGN: PRESHEAF-COMPONENT-ELIM.
def DataTransformationComponent.apply {Value₁ Value₂ : Object → Type t}
    (component : DataTransformationComponent Value₁ Value₂) {X} (value : Value₁ X) : Value₂ X :=
  component.map value

/-- The naturality certificate refers to the two actual stored actions. -/
structure DataTransformationNatural (Value₁ Value₂ : Object → Type t) where
  source : DataTransformation Primitive Value₁
  target : DataTransformation Primitive Value₂
  storedComponent : DataTransformationComponent Value₁ Value₂
  naturality : ∀ {X Y} (arrow : AtlasHom Primitive X Y) (value : Value₁ Y),
    storedComponent.map (source.action arrow value) =
      target.action arrow (storedComponent.map value)

-- ALIGN: PRESHEAF-NATURAL-MAP.
def DataTransformationNatural.component {Value₁ Value₂ : Object → Type t}
    (natural : DataTransformationNatural (Primitive := Primitive) Value₁ Value₂)
    {X} (value : Value₁ X) : Value₂ X := natural.storedComponent.apply value

-- ALIGN: PRESHEAF-NATURAL-PACKAGE.
def dataTransformationNatural {Value₁ Value₂ : Object → Type t}
    (source : DataTransformation Primitive Value₁) (target : DataTransformation Primitive Value₂)
    (component : ∀ {X}, Value₁ X → Value₂ X)
    (naturality : ∀ {X Y} (arrow : AtlasHom Primitive X Y) (value : Value₁ Y),
      component (source.action arrow value) = target.action arrow (component value)) :
    DataTransformationNatural (Primitive := Primitive) Value₁ Value₂ :=
  ⟨source, target, ⟨component⟩, naturality⟩

-- ALIGN: PRESHEAF-NATURALITY.
theorem dataTransformationNaturalNaturality {Value₁ Value₂ : Object → Type t}
    (natural : DataTransformationNatural (Primitive := Primitive) Value₁ Value₂)
    {X Y} (arrow : AtlasHom Primitive X Y) (value : Value₁ Y) :
    natural.component (natural.source.action arrow value) =
      natural.target.action arrow (natural.component value) := natural.naturality arrow value

def mapYonedaNatural {R S X : Object} (arrow : AtlasHom Primitive R S)
    (value : Yoneda Primitive R X) : Yoneda Primitive S X :=
  ⟨AtlasHom.presheafCompose arrow value.getYoneda⟩

-- ALIGN: YONEDA-NATURALITY.
theorem yonedaNaturality {R S X Y : Object} (representedArrow : AtlasHom Primitive R S)
    (arrow : AtlasHom Primitive X Y) (value : Yoneda Primitive R Y) :
    mapYonedaNatural representedArrow (mapYoneda arrow value) =
      mapYoneda arrow (mapYonedaNatural representedArrow value) := by
  exact congrArg Yoneda.mk (AtlasHom.presheafAssociativity representedArrow value.getYoneda arrow)

-- ALIGN: YONEDA-PACKAGE-NATURALITY.
theorem yonedaNaturalityForAction {R S X Y : Object} (representedArrow : AtlasHom Primitive R S)
    (arrow : AtlasHom Primitive X Y) (value : Yoneda Primitive R Y) :
    mapYonedaNatural representedArrow ((yoneda R).action arrow value) =
      (yoneda S).action arrow (mapYonedaNatural representedArrow value) :=
  yonedaNaturality representedArrow arrow value

-- ALIGN: YONEDA-NATURAL-PACKAGE.
def yonedaNatural {R S : Object} (arrow : AtlasHom Primitive R S) :
    DataTransformationNatural (Primitive := Primitive)
      (Yoneda Primitive R) (Yoneda Primitive S) where
  source := yoneda R
  target := yoneda S
  storedComponent := ⟨mapYonedaNatural arrow⟩
  naturality := yonedaNaturality arrow

-- ALIGN: YONEDA-PACKAGE-COMPONENT.
theorem yonedaComponentAgrees {R S X : Object} (arrow : AtlasHom Primitive R S)
    (value : Yoneda Primitive R X) :
    (yonedaNatural arrow).component value = mapYonedaNatural arrow value := rfl

open CategoryTheory
universe u
variable {C : Type u} [Category C]

/-- Evaluate a symbolic representable value in the interpreted Atlas category.
This is a natural interpretation, without asserting that distinct syntax trees
with the same denotation are equal. -/
def Yoneda.evaluate (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {represented X : Object} (value : Yoneda Primitive represented X) : object X ⟶ object represented :=
  AtlasHom.evaluate object primitive value.getYoneda

-- ALIGN: YONEDA-ACTION-INTERPRETATION.
theorem Yoneda.evaluate_mapYoneda (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {represented X Y : Object} (arrow : AtlasHom Primitive X Y) (value : Yoneda Primitive represented Y) :
    (mapYoneda arrow value).evaluate object primitive =
      AtlasHom.evaluate object primitive arrow ≫ value.evaluate object primitive :=
  AtlasHom.evaluate_presheafCompose object primitive value.getYoneda arrow

-- ALIGN: YONEDA-COMPONENT-INTERPRETATION.
theorem Yoneda.evaluate_mapYonedaNatural (object : Object → C)
    (primitive : ∀ {X Y}, Primitive X Y → (object X ⟶ object Y))
    {R S X : Object} (arrow : AtlasHom Primitive R S) (value : Yoneda Primitive R X) :
    (mapYonedaNatural arrow value).evaluate object primitive =
      value.evaluate object primitive ≫ AtlasHom.evaluate object primitive arrow :=
  AtlasHom.evaluate_presheafCompose object primitive arrow value.getYoneda

end Datra.Executable
