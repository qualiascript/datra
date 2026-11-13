#!/usr/bin/env python3
"""Require LiquidHaskell to reject false Atlas, coverage, and inverse laws.

Each check compiles an isolated copy of the production module using the built
library's interfaces. No failed proof or expected-failure directive enters the
library, and the temporary sources and compiler artifacts are always removed.
Run after `make -C datra-haskell verify-liquid`.
"""
import argparse
import json
import os
import re
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HASKELL = ROOT / "datra-haskell"
SOURCE = HASKELL / "src/DatraCore/DataTransformations/DataTransformations/DataTransformation/LiquidInternal.hs"
GUARDS = {
    "inhabited equality witnesses cannot prove False": """
{-@ proofGuard :: AtlasEquality a b -> { proof:() | False } @-}
proofGuard :: AtlasEquality a b -> ()
proofGuard (AtlasEquality Refl) = ()
""",
    "identity and composite constructors remain distinct": """
{-@
proofGuard :: () -> { proof:() |
  presheafIdentity == CompositeAtlasHom presheafIdentity presheafIdentity }
@-}
proofGuard :: () -> ()
proofGuard () = ()
""",
    "symbolic composition does not acquire a false left unit": """
{-@
proofGuard :: arrow:AtlasHom source target -> { proof:() |
  presheafCompose presheafIdentity arrow == arrow }
@-}
proofGuard :: AtlasHom source target -> ()
proofGuard (IdentityAtlasHom (AtlasEquality Refl)) = ()
proofGuard (PrimitiveAtlasHom _ _ _) = ()
proofGuard (CompositeAtlasHom _ _) = ()
""",
}

STABLE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/StableAtlasTransversal/Internal.hs"
STABLE_GUARDS = {
    "stable transversals reject an inverse that drops every image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> transversal:AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> { proof:() | stableOriginPreserved sourceAtlas targetAtlas transversal }
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> ()
  -> StableAtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas transversal originProof =
  stableAtlasTransversal sourceAtlas targetAtlas transversal originProof
    (const Nothing) (const ())
""",
}


DOMINC_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Coalitions/DomanialInclusion/LiquidInternal.hs"
DOMINC_GUARDS = {
    "coalition components reject an inverse that drops every image": """
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> (a -> CoalitionElement (AtlasObject atlasScope scope cellData))
  -> DomanialInsertion (DominionCellData a sourceObject) (cellData object)
proofGuard targetAtlas targetOccurrence forward =
  coalitionComponentInsertion targetAtlas targetOccurrence forward
    (const Nothing) (const ())
""",
}


TRANSVERSAL_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasTransposals/AtlasTransversal/Internal.hs"
TRANSVERSAL_GUARDS = {
    "transversals reject coverage evidence for the wrong image": """
{-@
proofGuard
  :: sourceAtlas:Atlas sa ss sd so sf
  -> targetAtlas:Atlas ta ts td to tf
  -> ordered:OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> badCoverage:(covered:AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> {w:AtlasCoverageWitness (AtlasObject ta ts td) |
         not (transversalImageCovered sourceAtlas targetAtlas ordered covered w)})
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
@-}
proofGuard
  :: Atlas sa ss sd so sf
  -> Atlas ta ts td to tf
  -> OrderedAtlasTransposal (AtlasObject sa ss sd) (AtlasObject ta ts td)
  -> (AtlasCoveredPageElement (AtlasObject sa ss sd)
       -> AtlasCoverageWitness (AtlasObject ta ts td))
  -> AtlasTransversal (AtlasObject sa ss sd) (AtlasObject ta ts td)
proofGuard sourceAtlas targetAtlas ordered badCoverage =
  atlasTransversal sourceAtlas targetAtlas ordered badCoverage
""",
}


CHARTER_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/Cartography/Charter/LiquidInternal.hs"
CHARTER_GUARDS = {
    "charted components reject a source inverse that drops every covered value": """
proofGuard
  :: DomanialInsertion (AtlasObjectCellData source sourceObject) (AtlasObjectCellData target targetObject)
  -> DomanialInsertion (ChartedCellData source sourceObject) (ChartedCellData target targetObject)
proofGuard original = chartMapInsertion original (const Nothing) (const ())
""",
    "chart counits reject an inverse that drops every covered value": """
proofGuard
  :: DomanialInsertion (ChartedCellData atlasObject object) (AtlasObjectCellData atlasObject object)
proofGuard = chartCounitInsertion (const Nothing) (const ())
""",
    "charted data rejects a witness that does not cover the datum": """
{-@
proofGuard
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> occurrence:PageElement scope object
  -> datum:cellData object
  -> witness:{w:AtlasCoverageWitness (AtlasObject atlasScope scope cellData) |
       not (coverageWitnessCovers valueAtlas occurrence datum w)}
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
@-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness (AtlasObject atlasScope scope cellData)
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
proofGuard valueAtlas occurrence datum witness =
  chartCellData valueAtlas occurrence datum witness ()
""",
}


RANK_IMAGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/DomanialInsertion/LiquidInternal.hs"
RANK_IMAGE_GUARDS = {
    "unranking does not certify a rank outside the Dominion image": """
{-@
proofGuard
  :: valueDominion:Dominion a
  -> valueRank:Natural
  -> {value:a | unrank valueDominion valueRank == Just value}
  -> {proof:() | rank valueDominion value == valueRank}
@-}
proofGuard :: Dominion a -> Natural -> a -> ()
proofGuard _ _ _ = ()
""",
    "a partial inverse does not certify a candidate outside the insertion image": """
{-@
proofGuard
  :: valueDominion:Dominion b
  -> insertion:DomanialInsertion a b
  -> root:b
  -> {value:a | preimage insertion root == Just value}
  -> {proof:() | rankImage valueDominion insertion value == rank valueDominion root}
@-}
proofGuard :: Dominion b -> DomanialInsertion a b -> b -> a -> ()
proofGuard _ _ _ _ = ()
""",
}


MERGE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasMerge/LiquidInternal.hs"
MERGE_GUARDS = {
    "merge unranking requires the datum's cell membership": """
{-@
proofGuard
  :: contains:(AtlasMergeDatum object -> Bool)
  -> datum:AtlasMergeDatum object
  -> { mergeDatumLookup contains (atlasMergeDatumRank datum) == Just datum }
@-}
proofGuard :: (AtlasMergeDatum object -> Bool) -> AtlasMergeDatum object -> ()
proofGuard contains datum = mergeDatumLookupRoundTrip contains datum
""",
    "merge insertions require target membership preservation": """
proofGuard :: AtlasMergeDatum source -> AtlasMergeDatum target
proofGuard = mergeDatumMap (const True) (const False) (const ())
""",
}

SEQUENCE_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasConfederations/AtlasSequence/LiquidInternal.hs"
SEQUENCE_GUARDS = {
    "sequence decoding requires a positive member count": """
proofGuard :: Natural -> AtlasSequenceDatum object
proofGuard = decodeSequenceDatum 0
""",
    "sequence roundtrips require a bounded member index": """
proofGuard :: Natural -> ()
proofGuard valueRank = decodeSequenceDatumRank 3 (AtlasSequenceDatum 3 valueRank)
""",
    "sequence unranking requires cell membership": """
proofGuard :: Natural -> ()
proofGuard valueRank = sequenceDatumLookupRoundTrip 3 (const False) (AtlasSequenceDatum 0 valueRank)
""",
    "sequence insertions require target membership preservation": """
proofGuard :: AtlasSequenceDatum source -> AtlasSequenceDatum target
proofGuard = sequenceDatumMap (const True) (const False) (const ())
""",
}


EXTENT_SOURCE = HASKELL / "src/DatraCore/Atlases/Derived/AtlasDerived/AtlasExtent/Internal.hs"
EXTENT_GUARDS = {
    "extent origin insertions require a valid origin arrow": """
{-@ proofGuard
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:PageElement scope object
      -> DomanialInsertion (cellData object) Natural @-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> DomanialInsertion (cellData object) Natural
proofGuard = atlasCellOriginRankInsertion
""",
    "extent inverse soundness requires a successful lookup": """
{-@ proofGuard
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source}
      -> valueRank:Natural
      -> datum:cellData object
      -> {applyInsertion (atlasCellOriginRankInsertion valueAtlas source) datum == valueRank} @-}
proofGuard
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> cellData object -> ()
proofGuard = cellOriginRankPreimageSound
""",
}


FOLIO_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Folio/LiquidInternal.hs"
FOLIO_GUARDS = {
    "folio origins reject a zero cached length": """
proofGuard :: page origin -> SingletonOrigin origin -> FolioData page origin origin
proofGuard = OriginFolio 0
""",
    "folio origins reject a cached length greater than one": """
proofGuard :: page origin -> SingletonOrigin origin -> FolioData page origin origin
proofGuard = OriginFolio 2
""",
    "folio append rejects an unchanged cached length": """
proofGuard :: FolioData page origin previous -> page next
  -> Coconsolidation previous next -> FolioData page origin next
proofGuard pages = SnocPage (folioLengthData pages) pages
""",
}

PAGE_INDEX_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/PageElements/Internal.hs"
PAGE_INDEX_GUARDS = {
    "page indices reject a missing padding step": """
proofGuard :: Folio origin page -> ChainIndex page -> PageElementIndex scope
proofGuard pages index = PageElementIndex (folioLength pages) pages 0 index
""",
    "page traces cannot discard the folio origin": """
{-@ proofGuard :: pages:Folio origin page -> page
      -> {positions:[Ordinal] | Trace.traceSuffix positions (folioOriginTrace pages)} @-}
proofGuard :: Folio origin page -> page -> [Ordinal]
proofGuard _ _ = []
""",
}


ATLAS_SOURCE = HASKELL / "src/DatraCore/Atlases/Core/Atlas/Internal.hs"
ATLAS_GUARDS = {
    "Atlas lookup requires the index's origin to match": """
{-@ proofGuard :: Atlas atlasScope scope cellData origin final
      -> PageElementIndex scope -> SomePageElement scope @-}
proofGuard :: Atlas atlasScope scope cellData origin final
  -> PageElementIndex scope -> SomePageElement scope
proofGuard = atlasPageCell
""",
}


def run(pattern=None):
    plan = json.loads((HASKELL / "dist-newstyle/cache/plan.json").read_text())
    library = next(unit for unit in plan["install-plan"]
                   if unit.get("pkg-name") == "datra-haskell"
                   and unit.get("component-name") == "lib")
    if not any(dep.startswith("liquidhaskell-") for dep in library["depends"]):
        raise SystemExit("Build the library with -fliquid before checking proof guards")
    project = os.environ.get("CABAL_PROJECT", "cabal.project")
    with tempfile.TemporaryDirectory(prefix="datra-proof-guards-") as directory:
        temporary = Path(directory)
        target = temporary / "LiquidInternal.hs"
        command = ["cabal", f"--project-file={project}", "exec", "-fliquid", "--", "ghc",
                   "-v0", "-c", "-fforce-recomp", "-DDATRA_LIQUID",
                   "-hide-all-packages",
                   "-this-unit-id", library["id"],
                   "-i" + str(Path(library["dist-dir"]) / "build")]
        for dependency in library["depends"]:
            command.extend(["-package-id", dependency])
        for source_path, guards in [(SOURCE, GUARDS), (STABLE_SOURCE, STABLE_GUARDS),
                                    (DOMINC_SOURCE, DOMINC_GUARDS),
                                    (TRANSVERSAL_SOURCE, TRANSVERSAL_GUARDS),
                                    (CHARTER_SOURCE, CHARTER_GUARDS),
                                    (RANK_IMAGE_SOURCE, RANK_IMAGE_GUARDS),
                                    (MERGE_SOURCE, MERGE_GUARDS),
                                    (SEQUENCE_SOURCE, SEQUENCE_GUARDS),
                                    (EXTENT_SOURCE, EXTENT_GUARDS),
                                    (FOLIO_SOURCE, FOLIO_GUARDS),
                                    (PAGE_INDEX_SOURCE, PAGE_INDEX_GUARDS),
                                    (ATLAS_SOURCE, ATLAS_GUARDS)]:
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source_path.read_text())
            for description, guard in guards.items():
                if pattern and not re.search(pattern, description):
                    continue
                target.write_text(source + "\n" + guard)
                result = subprocess.run(command + [str(target)], cwd=HASKELL,
                                        text=True, capture_output=True)
                output = result.stdout + result.stderr
                error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
                if (result.returncode == 0 or "Liquid Type Mismatch" not in output
                        or not any(int(line) > source.count("\n") for line in error_lines)):
                    raise SystemExit(f"Proof guard did not produce the required rejection: {description}\n{output}")
                print(f"Rejected false law: {description}")

        for source_path, datum_type, description in [
            (MERGE_SOURCE, "AtlasMergeDatum", "merge datums retain their cell identity"),
            (SEQUENCE_SOURCE, "AtlasSequenceDatum", "sequence datums retain their cell identity"),
        ]:
            if pattern and not re.search(pattern, description):
                continue
            source = re.sub(r'#include "[^"]*LiquidPlugin.h"',
                            f'#include "{HASKELL / "src/DatraCore/LiquidPlugin.h"}"',
                            source_path.read_text())
            source = source.replace("import Numeric.Natural", "import Data.Coerce (coerce)\nimport Numeric.Natural")
            target.write_text(source + f"\nproofGuard :: {datum_type} source -> {datum_type} target\n"
                              "proofGuard = coerce\n")
            result = subprocess.run(command + [str(target)], cwd=HASKELL, text=True, capture_output=True)
            output = result.stdout + result.stderr
            error_lines = re.findall(re.escape(str(target)) + r":(\d+):\d+: error:", output)
            if (result.returncode == 0 or "Couldn't match type" not in output or "coerce" not in output
                    or not any(int(line) > source.count("\n") for line in error_lines)):
                raise SystemExit(f"Cell-role guard did not produce the required rejection: {description}\n{output}")
            print(f"Rejected invalid coercion: {description}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--filter", help="Run only guard descriptions matching this regular expression")
    run(parser.parse_args().filter)
