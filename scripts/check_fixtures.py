#!/usr/bin/env python3
"""Run one set of computation vectors against both implementations.

Generated drivers and compiler outputs live in a TemporaryDirectory, removed on
success or failure. These fixtures supplement, rather than replace, the proofs.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run():
    vectors = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/ordinals.json").read_text())
    lean_lines = ["import datra", "open Datra.Executable.Ordinal"]
    manifest = json.loads((ROOT / "datra-haskell/docs/lean-correspondence.json").read_text())
    lean_lines.extend(f"#check {entry['lean_namespace']}.{entry['lean_declaration']}"
                      for entry in manifest["theorems"])
    haskell_lines = ["module Main where", "import DatraOrdinal", "import qualified PageElements.LiquidInternal as PE",
                     "import qualified DatraOrdinal.Internal as OI",
                     "import qualified DatraOrdinal.LiquidInternal as OL",
                     "import qualified Chain as Ch", "main :: IO ()", "main = do"]
    for i, vector in enumerate(vectors):
        left, right = vector["left"], vector["right"]
        checks = [
            (f"(ordinal {left}).coefficients", f"ordinalCoefficients (ordinal {left})", vector["canonical_left"]),
            (f"(ordinal {right}).coefficients", f"ordinalCoefficients (ordinal {right})", vector["canonical_right"]),
            (f"(addOrdinals (ordinal {left}) (ordinal {right})).coefficients",
             f"ordinalCoefficients (addOrdinals (ordinal {left}) (ordinal {right}))", vector["sum"]),
            (f"ordinalLT (ordinal {left}) (ordinal {right})",
             f"ordinalLT (ordinal {left}) (ordinal {right})", vector["lt"]),
        ]
        for j, (lean, haskell, expected) in enumerate(checks):
            lean_expected = str(expected).lower() if isinstance(expected, bool) else str(expected)
            lean_lines.append(f"#guard {lean} == {lean_expected}")
            haskell_lines.append(f'  if {haskell} == {expected} then pure () else fail "ordinal vector {i}, check {j}"')
    traces = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/traces.json").read_text())
    for i, vector in enumerate(traces):
        source, target, limit = vector["source"], vector["target"], vector["limit"]
        lean_source = f"({source} : List Nat).map finiteOrdinal"
        lean_target = f"({target} : List Nat).map finiteOrdinal"
        checks = [
            (f"Datra.Executable.Trace.traceSuffix ({lean_source}) ({lean_target})",
             f"PE.traceSuffix (map finiteOrdinal {source}) (map finiteOrdinal {target})", vector["suffix"]),
            (f"(Datra.Executable.Trace.trimTrace ({limit}) ({lean_source})).map (fun x => x.coefficients)",
             f"map ordinalCoefficients (PE.trimTrace ({limit}) (map finiteOrdinal {source}))",
             [[n] if n else [] for n in vector["trimmed_source"]]),
            (f"(Datra.Executable.Trace.trimTrace ({limit}) ({lean_target})).map (fun x => x.coefficients)",
             f"map ordinalCoefficients (PE.trimTrace ({limit}) (map finiteOrdinal {target}))",
             [[n] if n else [] for n in vector["trimmed_target"]]),
        ]
        for j, (lean, haskell, expected) in enumerate(checks):
            lean_expected = str(expected).lower() if isinstance(expected, bool) else str(expected)
            lean_lines.append(f"#guard {lean} == {lean_expected}")
            haskell_lines.append(f'  if {haskell} == {expected} then pure () else fail "trace vector {i}, check {j}"')
    subtraction = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/subtraction.json").read_text())
    for i, vector in enumerate(subtraction):
        initial, suffix, value, difference = (vector[key] for key in ("initial", "suffix", "value", "difference"))
        lean = f"ordinalSubtractBetween (ordinal {initial}) (ordinal {suffix}) (ordinal {value})"
        haskell = f"OL.ordinalSubtractBetween (OI.ordinal {initial}) (OI.ordinal {suffix}) (OI.ordinal {value})"
        lean_lines.extend([
            f"#guard !ordinalLT (ordinal {value}) (ordinal {initial})",
            f"#guard ordinalLT (ordinal {value}) (addOrdinals (ordinal {initial}) (ordinal {suffix}))",
            f"#guard ({lean}).coefficients == {difference}",
            f"#guard addOrdinals (ordinal {initial}) ({lean}) == ordinal {value}",
        ])
        haskell_lines.extend([
            f'  if OI.coefficients ({haskell}) == {difference} then pure () else fail "subtraction vector {i}"',
            f'  if OI.addOrdinals (OI.ordinal {initial}) ({haskell}) == OI.ordinal {value} then pure () else fail "subtraction reconstruction {i}"',
        ])
    chains = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/chains.json").read_text())
    lean_lines.append("def fixtureSum := Datra.Executable.Chain.sumChains Datra.Executable.Chain.spine Datra.Executable.Chain.spine")
    haskell_lines.append("  let fixtureSum = Ch.sumChains Ch.spine Ch.spine")
    for i, vector in enumerate(chains):
        position, side, value = (vector[key] for key in ("position", "side", "value"))
        lean_expected = "none" if side is None else f"some (Sum.{'inl' if side == 'left' else 'inr'} {value})"
        haskell_expected = "Nothing" if side is None else f"Just ({'Left' if side == 'left' else 'Right'} {value})"
        lean_lines.append(f"#guard ((fixtureSum.chainIndex (ordinal {position})).map Datra.Executable.ChainIndex.object) == {lean_expected}")
        haskell_lines.append(f'  if fmap Ch.chainObjectAt (Ch.chainIndex fixtureSum (ordinal {position})) == {haskell_expected} then pure () else fail "chain lookup {i}"')
        if side is not None:
            lean_lines.append(f"#guard fixtureSum.position (Sum.{'inl' if side == 'left' else 'inr'} {value}) == ordinal {position}")
            haskell_lines.append(f'  if Ch.chainPosition fixtureSum ({"Left" if side == "left" else "Right"} {value}) == ordinal {position} then pure () else fail "chain position {i}"')
    normalization = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/normalization.json").read_text())
    for i, vector in enumerate(normalization):
        page, final, limit, position, trace = (vector[key] for key in ("page", "final", "limit", "position", "trace"))
        expected_page = vector["normalized_page"]
        expected_trace = [[n] if n else [] for n in vector["normalized_trace"]]
        lean_lines.extend([
            f"def raw{i} : Datra.Executable.PageElement () := ⟨{page}, finiteOrdinal {position}, ({trace} : List Nat).map finiteOrdinal, ⟨Nat, Datra.Executable.Chain.spine, {position}⟩⟩",
            f"def normalized{i} := Datra.Executable.PageElement.normalize {final} ({limit}) raw{i}",
            f"#guard normalized{i}.page == {expected_page}",
            f"#guard normalized{i}.position == raw{i}.position",
            f"#guard normalized{i}.trace.map (fun x => x.coefficients) == {expected_trace}",
        ])
        haskell_lines.extend([
            f"  let raw{i} = PE.PageElement {page} (finiteOrdinal {position}) (map finiteOrdinal {trace}) (PE.PageElementCell Ch.spine {position}) :: PE.PageElement () ()",
            f"      normalized{i} = PE.normalizePageElementAt {final} ({limit}) raw{i}",
            f'  if PE.pageElementPage normalized{i} == {expected_page} && PE.pageElementPosition normalized{i} == PE.pageElementPosition raw{i} && map ordinalCoefficients (PE.pageElementTrace normalized{i}) == {expected_trace} then pure () else fail "normalization {i}"',
        ])
    enumeration = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/enumeration.json").read_text())
    for i, vector in enumerate(enumeration["decode"]):
        width, code, coefficients = (vector[key] for key in ("width", "code", "coefficients"))
        lean_expected = "none" if coefficients is None else f"some {coefficients}"
        haskell_expected = "Nothing" if coefficients is None else f"Just {coefficients}"
        lean_lines.append(f"#guard (ordinalAtNaturalRank {width} {code}).map (fun x => x.coefficients) == {lean_expected}")
        haskell_lines.append(f'  if fmap ordinalCoefficients (ordinalAtNaturalRank {width} {code}) == {haskell_expected} then pure () else fail "ordinal enumeration {i}"')
        if coefficients is not None:
            lean_lines.append(f"#guard naturalRankOfOrdinal {width} (ordinal {coefficients}) == some {code}")
            haskell_lines.append(f'  if naturalRankOfOrdinal {width} (ordinal {coefficients}) == Just {code} then pure () else fail "ordinal encoding {i}"')
    for i, vector in enumerate(enumeration["rejections"]):
        width, coefficients = vector["width"], vector["coefficients"]
        lean_lines.append(f"#guard naturalRankOfOrdinal {width} (ordinal {coefficients}) == none")
        haskell_lines.append(f'  if naturalRankOfOrdinal {width} (ordinal {coefficients}) == Nothing then pure () else fail "ordinal encoding bound {i}"')
    order = json.loads((ROOT / "datra-haskell/test/fixtures/alignment/order.json").read_text())
    haskell_lines[1:1] = [
        "import qualified Atlas as A", "import qualified AtlasTransposal as AT",
        "import qualified Folio as Fo", "import qualified Pagination as P",
        "import qualified PageElements as PubPE", "import qualified Consolidation as Co",
        "import qualified Dominion as D", "import qualified DomanialInsertion as DI",
        "import Data.Void (Void, absurd)", "import Numeric.Natural (Natural)",
    ]
    # This folio has a singleton origin, then two natural-number pages.
    # The last-to-middle consolidation is division by two.
    def order_trace(page, position):
        if page == 0:
            return [0]
        if page == 1:
            return [position, 0]
        return [position] * (page - 1) + [position // 2, 0]

    for i, vector in enumerate(order):
        lp, lv, rp, rv = (vector[key] for key in
                          ("left_page", "left_position", "right_page", "right_position"))
        for side, page, position in [("Left", lp, lv), ("Right", rp, rv)]:
            trace = order_trace(page, position)
            lean_lines.append(
                f"def order{side}{i} : Datra.Executable.PageElement () := "
                f"Datra.Executable.PageElement.normalize 2 3 "
                f"⟨{page}, finiteOrdinal {position}, ({trace} : List Nat).map finiteOrdinal, "
                f"⟨Nat, Datra.Executable.Chain.spine, {position}⟩⟩")
        lean_lines.append(
            f"#guard Datra.Executable.PageElement.elementLT orderLeft{i} orderRight{i} == "
            f"{str(vector['lt']).lower()}")
        haskell_lines.append(
            f'  if orderFixture {lp} {lv} {rp} {rv} == {vector["lt"]} '
            f'then pure () else fail "Atlas order {i}"')
    haskell_lines.append(r"""
newtype OrderDatum object = OrderDatum Void

orderFixture :: Natural -> Natural -> Natural -> Natural -> Bool
orderFixture leftPage leftPosition rightPage rightPosition =
  let unit = Ch.chain (finiteOrdinal 1) (const (finiteOrdinal 0))
        (\p -> if p == finiteOrdinal 0 then Just () else Nothing)
        (const ()) (\_ _ -> ()) (const ())
      collapse = Co.consolidation (const ()) (const 0) (\_ _ _ -> ()) (const ())
      halve = Co.consolidation (`div` 2) (* 2) (\_ _ r -> r `div` 2) (const ())
      folio = Fo.appendPage
        (Fo.appendPage (Fo.singletonFolio unit) Ch.spine (Co.op collapse))
        Ch.spine (Co.op halve)
      dataAt _ = D.dominion (\(OrderDatum v) -> absurd v) (const Nothing)
        (\(OrderDatum v) -> absurd v)
      mapData _ = DI.domanialInsertion (\(OrderDatum v) -> absurd v) (const Nothing)
        (\(OrderDatum v) -> absurd v)
  in P.pagination folio $ \pagination ->
    A.atlas pagination (A.atlasDataAction dataAt mapData)
      (\_ (OrderDatum v) -> absurd v)
      (\_ _ _ (OrderDatum v) -> absurd v)
      (\_ _ _ (OrderDatum v) -> absurd v)
      (\_ _ _ _ _ (OrderDatum v) _ -> absurd v) $ \atlas ->
        case ( PubPE.pageElementIndex (A.atlasPageElements atlas) leftPage (finiteOrdinal leftPosition)
             , PubPE.pageElementIndex (A.atlasPageElements atlas) rightPage (finiteOrdinal rightPosition)) of
          (Just left, Just right) ->
            PubPE.withPageElement (PubPE.pageElement left) $ \l ->
              PubPE.withPageElement (PubPE.pageElement right) $ \r ->
                AT.atlasTransposalElementLT
                  (AT.atlasTransposalElement (A.atlasWitness atlas) l)
                  (AT.atlasTransposalElement (A.atlasWitness atlas) r)
          _ -> error "invalid Atlas order fixture"
""")
    env = os.environ.copy()
    local_lake = ROOT / ".elan/bin/lake"
    if local_lake.exists():
        lake = str(local_lake)
        env["ELAN_HOME"] = str(ROOT / ".elan")
    else:
        lake = shutil.which("lake") or "lake"
    with tempfile.TemporaryDirectory(prefix="datra-alignment-") as temporary:
        tmp = Path(temporary)
        lean_file = tmp / "Fixtures.lean"
        haskell_file = tmp / "Fixtures.hs"
        lean_file.write_text("\n".join(lean_lines) + "\n")
        haskell_file.write_text("\n".join(haskell_lines) + "\n")
        subprocess.run([lake, "env", "lean", str(lean_file)], cwd=ROOT, env=env, check=True)
        project = os.environ.get("CABAL_PROJECT", "cabal.project")
        executable = tmp / "fixtures"
        subprocess.run(["cabal", f"--project-file={project}", "exec", "--", "ghc",
                        "-v0", "-XGADTs", "-package", "datra-haskell",
                        "-i" + str(ROOT / "datra-haskell/src/DatraCore/Atlases/Core"),
                        str(haskell_file),
                        "-outputdir", str(tmp), "-o", str(executable)], cwd=ROOT / "datra-haskell", check=True)
        subprocess.run([str(executable)], check=True)
    print(f"Cross-language fixtures passed: {len(vectors)} ordinal, {len(traces)} trace, "
          f"{len(subtraction)} subtraction, {len(chains)} chain, {len(normalization)} normalization, "
          f"{len(enumeration['decode']) + len(enumeration['rejections'])} enumeration, "
          f"{len(order)} Atlas order")


if __name__ == "__main__":
    run()
