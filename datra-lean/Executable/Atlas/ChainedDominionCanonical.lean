import Executable.Atlas.ChainedDominionOwner
import Executable.Atlas.Construction

namespace Datra.Executable.ChainedDominionAtlas

variable {A : Type}

/-- The Haskell class dictionary selects this fixed tuple. Its `Proxy`
arguments carry only the datum type, not runtime configuration. -/
structure CanonicalChainedDominion (A : Type) where
  inputs : A × Chain A × Dominion A

/-- The fixed recipe's nominal Atlas owner needs no runtime inhabitant. The
occurrence owner is represented separately by the exact stored folio. -/
inductive CanonicalChainedRecipe (A : Type) : Type where

-- ALIGN: CHAINED-CANONICAL-FIRST.
def canonicalChainedFirst (recipe : CanonicalChainedDominion A) : A := recipe.inputs.1

-- ALIGN: CHAINED-CANONICAL-CHAIN.
def canonicalChainedChain (recipe : CanonicalChainedDominion A) : Chain A := recipe.inputs.2.1

-- ALIGN: CHAINED-CANONICAL-DOMINION.
def canonicalChainedValueDominion (recipe : CanonicalChainedDominion A) : Dominion A := recipe.inputs.2.2

def canonicalPagesRecipe (recipe : CanonicalChainedDominion A) :
    PageElementsConstruction ⟨Unit, Chain.singletonChain⟩ ⟨A, canonicalChainedChain recipe⟩ :=
  ⟨chainedDominionFolio (canonicalChainedFirst recipe) (canonicalChainedChain recipe)⟩

-- ALIGN: CHAINED-CANONICAL-PAGINATION.
def canonicalPagination (recipe : CanonicalChainedDominion A) : Pagination :=
  Pagination.fromPageElements (canonicalPagesRecipe recipe).constructPageElements

theorem canonicalPagination_length (recipe : CanonicalChainedDominion A) :
    (canonicalPagination recipe).pages.length = 2 :=
  chainedDominionFolio_length (canonicalChainedFirst recipe) (canonicalChainedChain recipe)

theorem canonicalPagination_final (recipe : CanonicalChainedDominion A) :
    (canonicalPagination recipe).final = ⟨A, canonicalChainedChain recipe⟩ := rfl

-- ALIGN: CHAINED-CANONICAL-PRESENTATION.
def canonicalPresentation (recipe : CanonicalChainedDominion A) : AtlasPresentation :=
  chainedDominionPresentation (canonicalPagination recipe) (canonicalPagination_length recipe)
    (canonicalChainedFirst recipe) (canonicalChainedChain recipe) rfl (canonicalChainedValueDominion recipe)

def canonicalAtlasRecipe (recipe : CanonicalChainedDominion A) : AtlasConstruction :=
  ⟨canonicalPresentation recipe⟩

-- ALIGN: CHAINED-CANONICAL-OWNER.
def canonicalOwner (recipe : CanonicalChainedDominion A) : RetainedAtlas (CanonicalChainedRecipe A) A :=
  retainChainedPresentation (canonicalChainedFirst recipe) (canonicalChainedChain recipe)
    (canonicalChainedValueDominion recipe) Chain.singletonChain
    (canonicalPagesRecipe recipe).constructPageElements (canonicalPagination_length recipe)
    (canonicalAtlasRecipe recipe).presentation.allocateStored rfl

-- ALIGN: CHAINED-CANONICAL-ALLOCATION.
def canonicalChainedDominionAtlas (recipe : CanonicalChainedDominion A) :
    RetainedAtlas (CanonicalChainedRecipe A) A := canonicalOwner recipe

-- ALIGN: CHAINED-CANONICAL-INPUTS.
theorem canonicalChainedDominionAtlas_inputs (recipe : CanonicalChainedDominion A) :
    chainedDominionFirst (canonicalChainedDominionAtlas recipe) = canonicalChainedFirst recipe ∧
    chainedDominionChain (canonicalChainedDominionAtlas recipe) = canonicalChainedChain recipe ∧
    chainedDominionValueDominion (canonicalChainedDominionAtlas recipe) = canonicalChainedValueDominion recipe :=
  ⟨rfl, rfl, rfl⟩

-- ALIGN: CHAINED-CANONICAL-DESCRIPTION.
theorem canonicalChainedDominionAtlas_presentation (recipe : CanonicalChainedDominion A) :
    (chainedDominionAtlas (canonicalChainedDominionAtlas recipe)).atlasDescription =
      canonicalPresentation recipe := rfl

-- ALIGN: CHAINED-CANONICAL-PAGINATION-OBSERVATION.
theorem canonicalChainedDominionAtlas_pagination (recipe : CanonicalChainedDominion A) :
    (chainedDominionAtlas (canonicalChainedDominionAtlas recipe)).atlasDescription.pagination =
      canonicalPagination recipe := rfl

theorem canonicalChainedDominionAtlas_allocated (recipe : CanonicalChainedDominion A) :
    (chainedDominionAtlas (canonicalChainedDominionAtlas recipe)).toAtlas =
      (canonicalAtlasRecipe recipe).constructAtlas := rfl

theorem canonicalChainedDominionAtlas_runtimePresentation (recipe : CanonicalChainedDominion A) :
    withChainedDominionAtlas (canonicalChainedFirst recipe) (canonicalChainedChain recipe)
        (canonicalChainedValueDominion recipe) (fun _ owner => (chainedDominionAtlas owner).atlasDescription) =
      (chainedDominionAtlas (canonicalChainedDominionAtlas recipe)).atlasDescription := rfl

end Datra.Executable.ChainedDominionAtlas
