import Executable.Atlas.Transversal

namespace Datra.Executable
open CategoryTheory

/-- Atlas-map objects store their extent and a coverage callback there.
The owner index retains the Atlas carried by the Haskell existential witness. -/
structure AtlasMap (X : Atlas) where
  extent : X.Element
  isOrigin : extent = FolioData.ValidElement.originElement X.pages
  coversExtent : (datum : X.cellData extent.val.cell) →
    {w : X.CoverageWitness // w.Valid ∧ X.coverageWitnessCovers extent datum w = true}

namespace AtlasMap
variable {X : Atlas}

def atlasMap (X : Atlas)
    (covers : (datum : X.cellData (FolioData.ValidElement.originElement X.pages).val.cell) →
      {w : X.CoverageWitness // w.Valid ∧
        X.coverageWitnessCovers (FolioData.ValidElement.originElement X.pages) datum w = true}) : AtlasMap X :=
  ⟨FolioData.ValidElement.originElement X.pages, rfl, covers⟩

def withExtent {Result : Sort*} (value : AtlasMap X)
    (useExtent : (extent : X.Element) → Dominion (X.cellData extent.val.cell) →
      (X.cellData extent.val.cell → X.CertifiedCoveredElement) → Result) : Result :=
  useExtent value.extent (X.dataAt value.extent) (fun datum =>
    ⟨⟨value.extent, datum, (value.coversExtent datum).val⟩, (value.coversExtent datum).property⟩)

def toExtent (value : AtlasMap X) (source : X.Element) : source ⟶ value.extent :=
  source.toOrigin ≫ eqToHom value.isOrigin.symm

def coversDatum (value : AtlasMap X) (source : X.Element) (datum : X.cellData source.val.cell) :
    X.CoverageWitness :=
  (value.coversExtent ((X.data.action.normalizedMap (value.toExtent source)).map datum)).val

-- ALIGN: ATLAS-MAP-COVERAGE.
theorem coversDatum_spec (value : AtlasMap X) (source : X.Element) (datum : X.cellData source.val.cell) :
    (value.coversDatum source datum).Valid ∧
      X.coverageWitnessCovers source datum (value.coversDatum source datum) = true := by
  have valid := (value.coversExtent ((X.data.action.normalizedMap (value.toExtent source)).map datum)).property
  simpa only [Atlas.coverageWitnessCovers, Atlas.originImageRank, Atlas.originImage_map] using valid

theorem allCovered (value : AtlasMap X) (source : X.Element) (datum : X.cellData source.val.cell) :
    X.Covered source datum :=
  Atlas.coverageWitnessCovers_sound (value.coversDatum_spec source datum).1
    (value.coversDatum_spec source datum).2

-- ALIGN: ATLAS-MAP-OBJECT-INTERPRETATION.
theorem isAtlasMap (value : AtlasMap X) : Datra.Semantics.IsAtlasMap X.toSemantics := by
  intro datum
  exact (X.covered_interpretation X.toSemantics.Fo.originElement datum).mp
    (value.allCovered ((FolioData.ValidElement.fromFinite X.pages).obj X.toSemantics.Fo.originElement) datum)

noncomputable def toSemantics (value : AtlasMap X) : Datra.Semantics.AtlMap :=
  ⟨X.toSemantics, value.isAtlasMap⟩

noncomputable def toTransversalSemantics (value : AtlasMap X) : Datra.Semantics.AtlTravMap :=
  ⟨WideSubcategory.mk X.toSemantics, value.isAtlasMap⟩

/-- The runtime wrapper adds no arrow restriction and carries no object proof.
Those proofs are supplied separately when interpreting its endpoints. -/
structure Hom (X Y : Atlas) where
  hom : Atlas.Hom X Y

namespace Hom
variable {X Y Z : Atlas}

def identity (X : Atlas) : Hom X X := ⟨.identity⟩

def comp (second : Hom Y Z) (first : Hom X Y) : Hom X Z :=
  ⟨AtlasHom.composeAtlasHoms second.hom first.hom⟩

def materialize (f : Hom X Y) : Atlas.Morphism X Y := f.hom.materialize

def mapObject (f : Hom X Y) : X.Element → Y.Element := f.hom.mapObject

def image (f : Hom X Y) (source : X.Element) : Atlas.Morphism.Image X Y source :=
  f.materialize.image source

def mapData (f : Hom X Y) : X.DataElement → Y.DataElement := f.hom.mapData

noncomputable def toSemantics (source : AtlasMap X) (target : AtlasMap Y) (f : Hom X Y) :
    source.toSemantics ⟶ target.toSemantics := f.hom.finiteSemantics

-- ALIGN: ATLAS-MAP-HOM-IDENTITY.
theorem toSemantics_identity (source : AtlasMap X) :
    (identity X).toSemantics source source = 𝟙 source.toSemantics :=
  Atlas.Hom.finiteSemantics_identity X

-- ALIGN: ATLAS-MAP-HOM-COMPOSITION.
theorem toSemantics_comp (source : AtlasMap X) (middle : AtlasMap Y) (target : AtlasMap Z)
    (second : Hom Y Z) (first : Hom X Y) :
    (comp second first).toSemantics source target =
      first.toSemantics source middle ≫ second.toSemantics middle target :=
  Atlas.Hom.finiteSemantics_compose second.hom first.hom

-- ALIGN: ATLAS-MAP-HOM-DATA.
theorem mapData_interpretation (source : AtlasMap X) (target : AtlasMap Y) (f : Hom X Y)
    (datum : X.SemanticDataElement) :
    f.mapData (Atlas.fromSemanticData X datum) =
      Atlas.fromSemanticData Y (Atlas.mapSemanticData (f.toSemantics source target) datum) :=
  (f.hom.mapData_interpretation datum).symm

end Hom

/-- The dependent object result retains the same owner as Haskell's
AtlasWitness; the two rank-polymorphic actions remain explicit fields. -/
structure InclusionFunctor where
  object : {X : Atlas} → AtlasMap X → {atlas : Atlas // atlas = X}
  hom : {X Y : Atlas} → Hom X Y → Atlas.Hom X Y

def inclusionFunctor : InclusionFunctor :=
  ⟨fun {X} _ => ⟨X, rfl⟩, Hom.hom⟩

-- ALIGN: ATLAS-MAP-INCLUSION.
theorem inclusion_interpretation {Y : Atlas} (source : AtlasMap X) (target : AtlasMap Y)
    (f : Hom X Y) :
    (inclusionFunctor.hom f).finiteSemantics =
      Datra.Semantics.AtlMapInc.map (f.toSemantics source target) := rfl

end AtlasMap

/-- The full-subcategory wrapper retains the complete executable transversal. -/
structure AtlasTransversalMap (X Y : Atlas) where
  transversal : Atlas.Transversal X Y

namespace AtlasTransversalMap
variable {X Y Z : Atlas}

def hom (f : AtlasTransversalMap X Y) : AtlasMap.Hom X Y :=
  ⟨f.transversal.underlying.underlying.hom⟩

def identity (X : Atlas) : AtlasTransversalMap X X := ⟨.identity⟩

def comp (second : AtlasTransversalMap Y Z) (first : AtlasTransversalMap X Y) :
    AtlasTransversalMap X Z := ⟨Atlas.Transversal.comp second.transversal first.transversal⟩

def mapCovered (f : AtlasTransversalMap X Y) :
    X.CertifiedCoveredElement → Y.CertifiedCoveredElement := f.transversal.mapCovered

def objectInsertion (f : AtlasTransversalMap X Y) :
    DomanialInsertion X.TransposalElement Y.TransposalElement :=
  f.transversal.underlying.underlying.objectInsertion

noncomputable def toSemantics (source : AtlasMap X) (target : AtlasMap Y)
    (f : AtlasTransversalMap X Y) :
    source.toTransversalSemantics ⟶ target.toTransversalSemantics := f.transversal.toSemantics

-- ALIGN: ATLAS-TRANSVERSAL-MAP-IDENTITY.
theorem toSemantics_identity (source : AtlasMap X) :
    (identity X).toSemantics source source = 𝟙 source.toTransversalSemantics :=
  Atlas.Transversal.toSemantics_identity X

-- ALIGN: ATLAS-TRANSVERSAL-MAP-COMPOSITION.
theorem toSemantics_comp (source : AtlasMap X) (middle : AtlasMap Y) (target : AtlasMap Z)
    (second : AtlasTransversalMap Y Z) (first : AtlasTransversalMap X Y) :
    (comp second first).toSemantics source target =
      first.toSemantics source middle ≫ second.toSemantics middle target :=
  Atlas.Transversal.toSemantics_comp second.transversal first.transversal

structure InclusionFunctor where
  object : {X : Atlas} → AtlasMap X → {atlas : Atlas // atlas = X}
  hom : {X Y : Atlas} → AtlasTransversalMap X Y → Atlas.Transversal X Y

def inclusionFunctor : InclusionFunctor :=
  ⟨AtlasMap.inclusionFunctor.object, AtlasTransversalMap.transversal⟩

-- ALIGN: ATLAS-TRANSVERSAL-MAP-INCLUSION.
theorem inclusion_interpretation (source : AtlasMap X) (target : AtlasMap Y)
    (f : AtlasTransversalMap X Y) :
    (inclusionFunctor.hom f).toSemantics =
      Datra.Semantics.AtlTravMapInc.map (f.toSemantics source target) := rfl

end AtlasTransversalMap
end Datra.Executable
