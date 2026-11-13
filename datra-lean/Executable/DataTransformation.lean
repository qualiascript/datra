import Executable.Atlas.Morphism

namespace Datra.Executable

universe v w t
variable {Object : Type v} (Primitive : Object → Object → Type w)

/-- Defunctionalized value families: a symbol is interpreted at each Atlas. -/
structure ValueFamily (Object : Type v) where
  Symbol : Type t
  value : Symbol → Object → Type w

structure DataTransformation (Value : Object → Type t) where
  action : ∀ {X Y}, AtlasHom Primitive X Y → Value Y → Value X
  identity : ∀ {X} (x : Value X), action .identity x = x
  composition : ∀ {X Y Z} (second : AtlasHom Primitive Y Z)
    (first : AtlasHom Primitive X Y) (x : Value Z),
    action (AtlasHom.presheafCompose second first) x = action first (action second x)

/-- Interpreting a symbol selects the indexed family stored by the action and
its laws; it does not coerce the proof package to a different family. -/
abbrev DataTransformationFor (family : ValueFamily Object) (symbol : family.Symbol) :=
  DataTransformation Primitive (family.value symbol)

structure Yoneda (represented atlas : Object) where
  getYoneda : AtlasHom Primitive atlas represented

def yonedaValueFamily : ValueFamily Object where
  Symbol := Object
  value represented atlas := Yoneda Primitive represented atlas

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
    DataTransformationFor Primitive (yonedaValueFamily Primitive) represented where
  action := mapYoneda
  identity := yonedaIdentity
  composition := yonedaComposition

structure DataTransformationNatural {Value₁ Value₂ : Object → Type t}
    (source : DataTransformation Primitive Value₁) (target : DataTransformation Primitive Value₂) where
  component : ∀ {X}, Value₁ X → Value₂ X
  naturality : ∀ {X Y} (arrow : AtlasHom Primitive X Y) (value : Value₁ Y),
    component (source.action arrow value) = target.action arrow (component value)

def mapYonedaNatural {R S X : Object} (arrow : AtlasHom Primitive R S)
    (value : Yoneda Primitive R X) : Yoneda Primitive S X :=
  ⟨AtlasHom.presheafCompose arrow value.getYoneda⟩

-- ALIGN: YONEDA-NATURALITY.
theorem yonedaNaturality {R S X Y : Object} (representedArrow : AtlasHom Primitive R S)
    (arrow : AtlasHom Primitive X Y) (value : Yoneda Primitive R Y) :
    mapYonedaNatural representedArrow (mapYoneda arrow value) =
      mapYoneda arrow (mapYonedaNatural representedArrow value) := by
  exact congrArg Yoneda.mk (AtlasHom.presheafAssociativity representedArrow value.getYoneda arrow)

-- ALIGN: YONEDA-NATURAL-PACKAGE.
def yonedaNatural {R S : Object} (arrow : AtlasHom Primitive R S) :
    DataTransformationNatural (yoneda (Primitive := Primitive) R) (yoneda S) where
  component := mapYonedaNatural arrow
  naturality := yonedaNaturality arrow

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
