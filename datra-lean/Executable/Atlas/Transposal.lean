import Executable.Atlas.Morphism
import Executable.Atlas.Order

namespace Datra.Executable.Atlas
open CategoryTheory

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
end Datra.Executable.Atlas
