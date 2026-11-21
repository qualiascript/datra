import Mathlib

/-! ## Executable correspondence

Indices replace Haskell's existential equality witnesses: eliminating `Refl`
leaves precisely these three constructors. The morphism module instantiates this shared syntax with checked primitive Atlas actions;
no semantic category laws are used to prove the syntax equations.
-/
namespace Datra.Executable

universe v w

/-- Runtime Atlas equality contains only a type-equality witness. Its logical
representation forgets the endpoints, but not any computational Atlas data. -/
structure AtlasEquality {Object : Type v} (source target : Object) where
  witness : source = target

def AtlasEquality.erase {Object : Type v} {source target : Object}
    (_ : AtlasEquality source target) : Unit := ()

-- ALIGN: ATLAS-EQUALITY-ERASURE-INJECTIVE.
theorem AtlasEquality.erase_injective {Object : Type v} {source target : Object} :
    Function.Injective (@AtlasEquality.erase Object source target) := by
  intro a b _
  cases a
  cases b
  rfl

-- ALIGN: ATLAS-EQUALITY-UNIQUE.
theorem AtlasEquality.erase_unique {Object : Type v} {a b c d : Object}
    (first : AtlasEquality a b) (second : AtlasEquality c d) :
    first.erase = second.erase := rfl

inductive AtlasHom {Object : Type v} (Primitive : Object → Object → Type w) :
    Object → Object → Type (max v w)
  | primitive {X Y} : Primitive X Y → AtlasHom Primitive X Y
  | identity {X} : AtlasHom Primitive X X
  | composite {X Y Z} : AtlasHom Primitive Y Z → AtlasHom Primitive X Y →
      AtlasHom Primitive X Z

namespace AtlasHom
variable {Object : Type v} {Primitive : Object → Object → Type w}
variable {W X Y Z : Object}

def presheafIdentity : AtlasHom Primitive X X := .identity

/-- Eliminate the explicit Haskell equality wrapper into Lean's indexed
identity constructor. Equality-proof irrelevance makes this independent of
which witness was supplied. -/
def identityWithEquality (equality : AtlasEquality X Y) : AtlasHom Primitive X Y :=
  equality.witness ▸ (.identity : AtlasHom Primitive X X)

/-- The equations of DataTransformation.LiquidInternal.presheafCompose.
In particular a primitive right operand always produces a composite node. -/
def presheafCompose {X Y Z : Object} (second : AtlasHom Primitive Y Z) :
    AtlasHom Primitive X Y → AtlasHom Primitive X Z
  | .identity => second
  | .composite middle first => .composite (presheafCompose second middle) first
  | .primitive first => .composite second (.primitive first)

-- ALIGN: ATLASHOM-IDENTITY-WITNESS.
theorem presheafCompose_identityWithEquality (second : AtlasHom Primitive Y Z)
    (equality : AtlasEquality X Y) :
    presheafCompose second (identityWithEquality equality) =
      cast (congrArg (fun source => AtlasHom Primitive source Z) equality.witness.symm) second := by
  cases equality with
  | mk witness => cases witness; rfl

-- ALIGN: ATLASHOM-RIGHT-IDENTITY. Recipe: unfold the identity case.
@[simp] theorem presheafRightIdentity (arrow : AtlasHom Primitive X Y) :
    presheafCompose arrow presheafIdentity = arrow := rfl

-- ALIGN: ATLASHOM-ASSOC. Recipe: induct on first. Identity and primitive
-- reduce definitionally; composite uses the induction hypothesis for middle.
theorem presheafAssociativity (third : AtlasHom Primitive Y Z)
    (second : AtlasHom Primitive X Y) (first : AtlasHom Primitive W X) :
    presheafCompose third (presheafCompose second first) =
      presheafCompose (presheafCompose third second) first := by
  induction first with
  | identity => rfl
  | primitive _ => rfl
  | composite middle first ih _ =>
      simp only [presheafCompose, ih]

/-- The separate Control.Category composition, which also simplifies a left
identity. It must not be substituted for presheafCompose in structural proofs. -/
def composeAtlasHoms {X Y Z : Object} : AtlasHom Primitive Y Z → AtlasHom Primitive X Y →
    AtlasHom Primitive X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (composeAtlasHoms second middle) first
  | second, .primitive first => .composite second (.primitive first)

end AtlasHom

end Datra.Executable
