import Executable.Atlas.OrderedTransposal
import Executable.Atlas.Coverage

namespace Datra.Executable.Atlas
open CategoryTheory

/-- Public covered elements retain the invariant of their hidden constructor. -/
abbrev CertifiedCoveredElement (X : Atlas) := {c : X.CoveredPageElement // c.Valid}

def CertifiedCoveredElement.data {X : Atlas} (c : X.CertifiedCoveredElement) : X.DataElement :=
  ⟨c.val.source, c.val.datum⟩

def DataElement.Covered {X : Atlas} (c : X.DataElement) : Prop := X.Covered c.1 c.2

theorem fromSemanticData_covered (X : Atlas) (c : X.SemanticDataElement) :
    (fromSemanticData X c).Covered ↔ Datra.Semantics.Covered X.toSemantics c.1 c.2 :=
  X.covered_interpretation c.1 c.2

noncomputable def CertifiedCoveredElement.fromSemantics {X : Atlas}
    (c : Datra.Semantics.CoveredPageElement X.toSemantics) : X.CertifiedCoveredElement :=
  let source : X.DataElement := fromSemanticData X ⟨c.pageElement, c.datum⟩
  let covered : X.Covered source.1 source.2 :=
    (X.covered_interpretation c.pageElement c.datum).mpr c.covered
  ⟨⟨source.1, source.2, X.findAtlasCoverage source.1 source.2 covered⟩,
    X.findAtlasCoverage_spec source.1 source.2 covered⟩

theorem CertifiedCoveredElement.fromSemantics_data {X : Atlas}
    (c : Datra.Semantics.CoveredPageElement X.toSemantics) :
    (CertifiedCoveredElement.fromSemantics c).data = fromSemanticData X ⟨c.pageElement, c.datum⟩ := rfl

theorem CertifiedCoveredElement.covered {X : Atlas} (c : X.CertifiedCoveredElement) :
    c.data.Covered := CoveredPageElement.covered c.property

abbrev TransversalImage (Y : Atlas) := Y.DataElement

def transversalImage {X Y : Atlas} (ordered : OrderedTransposal X Y)
    (covered : X.CertifiedCoveredElement) : TransversalImage Y :=
  ordered.underlying.hom.mapData covered.data

-- ALIGN: ATLAS-TRANSVERSAL-IMAGE.
def withTransversalImage {X Y : Atlas} {Result : Sort*} (ordered : OrderedTransposal X Y)
    (covered : X.CertifiedCoveredElement)
    (useImage : (target : Y.Element) → Y.cellData target.val.cell → Result) : Result :=
  let image := transversalImage ordered covered
  useImage image.1 image.2

-- ALIGN: ATLAS-TRANSVERSAL-IMAGE-COVERAGE.
def transversalImageCovered {X Y : Atlas} (ordered : OrderedTransposal X Y)
    (covered : X.CertifiedCoveredElement) (witness : Y.CoverageWitness) : Bool :=
  let image := transversalImage ordered covered
  Y.coverageWitnessCovers image.1 image.2 witness

/-- A primitive action stores the law of its exact image with the callback. -/
structure TransversalAction (X Y : Atlas) where
  ordered : OrderedTransposal X Y
  preserves : (c : X.CertifiedCoveredElement) →
    {w : Y.CoverageWitness // w.Valid ∧ transversalImageCovered ordered c w = true}

-- ALIGN: ATLAS-TRANSVERSAL-PRIMITIVE-COVERED.
def mapTransversalAction {X Y : Atlas} (action : TransversalAction X Y)
    (covered : X.CertifiedCoveredElement) : Y.CertifiedCoveredElement :=
  let witness := action.preserves covered
  let image := transversalImage action.ordered covered
  Y.atlasCoveredByWitness image.1 image.2 witness.val witness.property.2

theorem mapTransversalAction_valid {X Y : Atlas} (action : TransversalAction X Y)
    (covered : X.CertifiedCoveredElement) :
    Y.coveredPageElementValid (mapTransversalAction action covered).val = true :=
  (mapTransversalAction action covered).property.2

theorem mapTransversalAction_witness {X Y : Atlas} (action : TransversalAction X Y)
    (covered : X.CertifiedCoveredElement) :
    (mapTransversalAction action covered).val.witness = (action.preserves covered).val := rfl

inductive Transversal : Atlas → Atlas → Type 2
  | primitive {X Y} (action : TransversalAction X Y) : Transversal X Y
  | identity {X} : Transversal X X
  | composite {X Y Z} : Transversal Y Z → Transversal X Y → Transversal X Z

def atlasTransversal {X Y : Atlas} (ordered : OrderedTransposal X Y)
    (preserves : (c : X.CertifiedCoveredElement) →
      {w : Y.CoverageWitness // w.Valid ∧ transversalImageCovered ordered c w = true}) : Transversal X Y :=
  .primitive ⟨ordered, preserves⟩

/-- An unchanged result retains the caller's source owner. An actual mapped
result retains its certified target, even when followed by an identity. -/
inductive TransversalCoveredImage : Atlas → Atlas → Type 2
  | unchanged {X} : TransversalCoveredImage X X
  | mapped {X Y} (image : Y.CertifiedCoveredElement) : TransversalCoveredImage X Y

def TransversalCoveredImage.resolve {X Y : Atlas} (image : TransversalCoveredImage X Y)
    (source : X.CertifiedCoveredElement) : Y.CertifiedCoveredElement :=
  match image with
  | .unchanged => source
  | .mapped covered => covered

def TransversalCoveredImage.bind {X Y Z : Atlas} (image : TransversalCoveredImage X Y)
    (next : Y.CertifiedCoveredElement → TransversalCoveredImage Y Z)
    (source : X.CertifiedCoveredElement) : TransversalCoveredImage X Z :=
  match image with
  | .unchanged => next source
  | .mapped covered =>
      match next covered with
      | .unchanged => .mapped covered
      | .mapped result => .mapped result

theorem TransversalCoveredImage.resolve_bind {X Y Z : Atlas} (image : TransversalCoveredImage X Y)
    (next : Y.CertifiedCoveredElement → TransversalCoveredImage Y Z)
    (source : X.CertifiedCoveredElement) :
    (image.bind next source).resolve source = (next (image.resolve source)).resolve (image.resolve source) := by
  cases image with
  | unchanged => rfl
  | mapped covered => cases h : next covered <;> simp [bind, resolve, h]

-- ALIGN: ATLAS-TRANSVERSAL-OWNED-IMAGE.
def transversalCoveredImage {X Y : Atlas} :
    Transversal X Y → X.CertifiedCoveredElement → TransversalCoveredImage X Y
  | .identity, _ => .unchanged
  | .primitive action, covered => .mapped (mapTransversalAction action covered)
  | .composite second first, covered =>
      (transversalCoveredImage first covered).bind (transversalCoveredImage second) covered

-- ALIGN: ATLAS-TRANSVERSAL-OWNED-ELIMINATION.
def withAtlasTransversalCoveredImage {X Y : Atlas} {Result : Sort*}
    (f : Transversal X Y) (covered : X.CertifiedCoveredElement)
    (useImage : Y.CertifiedCoveredElement → Result) : Result :=
  useImage ((transversalCoveredImage f covered).resolve covered)

namespace Transversal

def underlying {X Y : Atlas} : Transversal X Y → OrderedTransposal X Y
  | .primitive action => action.ordered
  | .identity => .identity
  | .composite second first => OrderedTransposal.comp second.underlying first.underlying

def mapCovered {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) : Y.CertifiedCoveredElement :=
  (transversalCoveredImage f c).resolve c

theorem mapCovered_composite {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y)
    (c : X.CertifiedCoveredElement) :
    (composite second first).mapCovered c = second.mapCovered (first.mapCovered c) :=
  TransversalCoveredImage.resolve_bind (transversalCoveredImage first c) (transversalCoveredImage second) c

theorem withCoveredImage_agrees {X Y : Atlas} {Result : Sort*} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) (useImage : Y.CertifiedCoveredElement → Result) :
    withAtlasTransversalCoveredImage f c useImage = useImage (f.mapCovered c) := rfl

/-- Coverage callbacks may choose different witnesses, but the dependent image
is determined by the source cell and datum. -/
theorem mapCovered_data_congr {X Y : Atlas} (f : Transversal X Y)
    (left right : X.CertifiedCoveredElement) (same : left.data = right.data) :
    (f.mapCovered left).data = (f.mapCovered right).data := by
  induction f with
  | identity => exact same
  | primitive action =>
      change action.ordered.underlying.hom.mapData left.data =
        action.ordered.underlying.hom.mapData right.data
      rw [same]
  | composite second first ih₂ ih₁ =>
      rw [mapCovered_composite, mapCovered_composite]
      exact ih₂ _ _ (ih₁ left right same)

theorem underlying_composite {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (composite second first).underlying.underlying.hom.finiteSemantics =
      first.underlying.underlying.hom.finiteSemantics ≫ second.underlying.underlying.hom.finiteSemantics :=
  congrArg Subtype.val (OrderedTransposal.toSemantics_comp second.underlying first.underlying)

/-- The operational mapper produces precisely the semantic image, including
the dependent datum rather than only its page element. -/
-- ALIGN: ATLAS-TRANSVERSAL-COVERED-IMAGE.
theorem mapCovered_interpretation {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    (f.mapCovered c).data = fromSemanticData Y
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source) := by
  induction f with
  | primitive action =>
      change action.ordered.underlying.hom.mapData c.data = _
      rw [h]
      exact (action.ordered.underlying.hom.mapData_interpretation source).symm
  | identity =>
      change c.data = fromSemanticData _ (mapSemanticData (Hom.finiteSemantics .identity) source)
      rw [Hom.finiteSemantics_identity]
      exact h
  | composite second first ih₂ ih₁ =>
      rw [underlying_composite, mapCovered_composite]
      exact ih₂ (first.mapCovered c)
        (mapSemanticData first.underlying.underlying.hom.finiteSemantics source) (ih₁ c source h)

theorem mapCovered_covers_semantic {X Y : Atlas} (f : Transversal X Y)
    (c : X.CertifiedCoveredElement) (source : X.SemanticDataElement)
    (h : c.data = fromSemanticData X source) :
    Datra.Semantics.Covered Y.toSemantics
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source).1
      (mapSemanticData f.underlying.underlying.hom.finiteSemantics source).2 := by
  have imageCovered := (f.mapCovered c).covered
  rw [f.mapCovered_interpretation c source h] at imageCovered
  exact (fromSemanticData_covered Y
    (mapSemanticData f.underlying.underlying.hom.finiteSemantics source)).mp imageCovered

-- ALIGN: ATLAS-TRANSVERSAL-COVERAGE.
theorem semantic_preservesCoverage {X Y : Atlas} (f : Transversal X Y) :
    Datra.Semantics.PreservesCoveredPageElements f.underlying.underlying.hom.finiteSemantics := by
  intro c
  exact f.mapCovered_covers_semantic (CertifiedCoveredElement.fromSemantics c)
    ⟨c.pageElement, c.datum⟩ (CertifiedCoveredElement.fromSemantics_data c)

/-- The coverage contract applies to the complete executable component at
every occurrence, including padding. No factorwise coverage is required. -/
theorem preservesData {X Y : Atlas} (f : Transversal X Y) (source : X.DataElement)
    (covered : source.Covered) : (f.underlying.underlying.hom.mapData source).Covered := by
  have sourceCovered : Datra.Semantics.Covered X.toSemantics
      (toSemanticData X source).1 (toSemanticData X source).2 := by
    apply (fromSemanticData_covered X (toSemanticData X source)).mp
    rw [fromSemanticData_toSemanticData]
    exact (X.covered_normalize_iff source.1 source.2).mpr covered
  have imageCovered := f.semantic_preservesCoverage
    ⟨(toSemanticData X source).1, (toSemanticData X source).2, sourceCovered⟩
  have executable := (fromSemanticData_covered Y
    (mapSemanticData f.underlying.underlying.hom.finiteSemantics (toSemanticData X source))).mpr imageCovered
  rw [Hom.mapData_interpretation, fromSemanticData_toSemanticData] at executable
  change (f.underlying.underlying.hom.materialize.mapData ⟨source.1.normalize, source.2⟩).Covered at executable
  rw [Morphism.mapData_normalize] at executable
  exact executable

-- ALIGN: ATLAS-TRANSVERSAL-INTERPRETATION.
theorem semantic_transversal {X Y : Atlas} (f : Transversal X Y) :
    Datra.Semantics.IsTransversal f.underlying.underlying.hom.finiteSemantics :=
  ⟨f.underlying.semantic_order, f.semantic_preservesCoverage⟩

noncomputable def toSemantics {X Y : Atlas} (f : Transversal X Y) :
    (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) ⟶
      (WideSubcategory.mk Y.toSemantics : Datra.Semantics.AtlTrav) :=
  ⟨f.underlying.underlying.hom.finiteSemantics, f.semantic_transversal⟩

def comp {X Y Z : Atlas} : Transversal Y Z → Transversal X Y → Transversal X Z
  | .identity, first => first
  | second, .identity => second
  | second, .composite middle first => .composite (comp second middle) first
  | second, first => .composite second first

-- ALIGN: ATLAS-TRANSVERSAL-IDENTITY.
@[simp] theorem toSemantics_identity (X : Atlas) :
    (identity : Transversal X X).toSemantics =
      𝟙 (WideSubcategory.mk X.toSemantics : Datra.Semantics.AtlTrav) := by
  apply Subtype.ext
  exact Hom.finiteSemantics_identity X

@[simp] theorem toSemantics_composite {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (composite second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  apply Subtype.ext
  exact underlying_composite second first

-- ALIGN: ATLAS-TRANSVERSAL-COMPOSITION.
theorem toSemantics_comp {X Y Z : Atlas} (second : Transversal Y Z) (first : Transversal X Y) :
    (comp second first).toSemantics = first.toSemantics ≫ second.toSemantics := by
  induction first with
  | identity => cases second <;> simp [comp]
  | primitive _ => cases second <;> simp [comp]
  | composite middle first ih _ => cases second <;> simp_all [comp, Category.assoc]

end Transversal
end Datra.Executable.Atlas
