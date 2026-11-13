#!/usr/bin/env python3
"""Check the correspondence manifest and reject unchecked core declarations."""
import argparse
import json
import re
from pathlib import Path

from lean_sources import lean_code, project_sources

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "datra-haskell/src/DatraCore"
MANIFEST = ROOT / "datra-haskell/docs/lean-correspondence.json"


def check(require_complete=False):
    manifest = json.loads(MANIFEST.read_text())
    sources = project_sources()
    lean = "\n".join(path.read_text() for path in sources)
    errors = []
    for source in (ROOT / "datra-haskell/src").rglob("*.hs"):
        text = source.read_text()
        module = re.search(r"^module\s+([\w.]+)", text, re.M)
        if module is None:
            continue
        for imported in re.findall(r"^import\s+(?:qualified\s+)?([\w.]+)", text, re.M):
            if imported.endswith(".LiquidInternal"):
                owner = imported.removesuffix(".LiquidInternal")
                if module[1] not in {owner, owner + ".Internal"}:
                    errors.append(f"{source.relative_to(ROOT)}: import {owner}'s exposed interface "
                                  f"instead of {imported}")
    unreachable = set((ROOT / "datra-lean").rglob("*.lean")) - set(sources)
    if unreachable:
        errors.append("Lean modules missing from datra.lean imports: " + ", ".join(
            str(path.relative_to(ROOT)) for path in sorted(unreachable)))
    if re.search(r"\b(?:sorry|admit|axiom)\b", lean_code(lean)):
        errors.append("Lean contains an unchecked proof or axiom")
    seen = set()
    for theorem in manifest["theorems"]:
        identifier = theorem["id"]
        if identifier in seen:
            errors.append(f"Duplicate theorem identifier: {identifier}")
        seen.add(identifier)
        marker = f"ALIGN: {identifier}."
        source = ROOT / theorem["haskell_file"]
        if marker not in source.read_text():
            errors.append(f"Missing {marker} in {source.relative_to(ROOT)}")
        if not re.search(r"^" + re.escape(theorem["haskell_declaration"]) + r"\s*::",
                         source.read_text(), re.M):
            errors.append(f"Missing Haskell declaration: {theorem['haskell_declaration']}")
        if marker not in lean:
            errors.append(f"Missing {marker} in project Lean sources")
        if not re.search(r"\b(?:theorem|def)\s+" + re.escape(theorem["lean_declaration"]) + r"\b", lean):
            errors.append(f"Missing Lean declaration: {theorem['lean_declaration']}")
    unregistered = set(re.findall(r"ALIGN: ([\w-]+)\.", lean)) - seen
    if unregistered:
        errors.append("Unregistered Lean correspondences: " + ", ".join(sorted(unregistered)))
    if require_complete:
        unfinished = [entry["module"] for entry in manifest["modules"]
                      if entry["coverage"] != "aligned"]
        if unfinished:
            errors.append("Unfinished representation bridges: " + ", ".join(unfinished))
    expected_modules = {entry["haskell_file"]: entry for entry in manifest["modules"]}
    escapes = []
    for source in sorted(CORE.rglob("*.hs")):
        text = source.read_text()
        unregistered = set(re.findall(r"ALIGN: ([\w-]+)\.", text)) - seen
        if unregistered:
            errors.append(f"{source.relative_to(ROOT)}: unregistered correspondences: "
                          + ", ".join(sorted(unregistered)))
        reflected = re.findall(r"\{-@\s*(?:reflect|inline)\s+(\w+)", text)
        types = re.findall(r"^(?:data|newtype)\s+(\w+)", text, re.M)
        aliases = re.findall(r"^type\s+(?!role\b|family\b|instance\b)(\w+)", text, re.M)
        predicates = re.findall(r"\{-@\s*predicate\s+(\w+)", text)
        refinement_aliases = re.findall(r"\{-@\s*type\s+(\w+)", text)
        embeddings = re.findall(r"\{-@\s*embed\s+([^\n]*?)\s*@-\}", text)
        variances = [" ".join(value.split()) for value in
                     re.findall(r"\{-@\s*data\s+variance\s+(.+?)\s*@-\}", text, re.S)]
        path = str(source.relative_to(ROOT))
        refinements = re.findall(r"\{-@\s*(?:assume\s+)?([a-z]\w*)\s*::", text)
        if reflected or types or aliases or predicates or refinement_aliases or refinements or variances:
            expected = expected_modules.pop(path, None)
            if (expected is None or expected["reflected"] != reflected
                    or expected["types"] != types or expected["aliases"] != aliases
                    or expected["predicates"] != predicates
                    or expected["refinement_aliases"] != refinement_aliases
                    or expected["embeddings"] != embeddings
                    or expected.get("variances", []) != variances
                    or expected["refinements"] != refinements):
                errors.append(f"Correspondence inventory drift: {path}")
        for match in re.finditer(r"\{-@\s*(assume|ignore)\s+(\w+)", text):
            escapes.append({"file": path, "directive": match[1], "declaration": match[2]})
        if re.search(r"\bunsafeCoerce\b", text):
            errors.append(f"{path}: unsafeCoerce is forbidden")
        if re.search(r"\{-@\s*fail\s", text):
            errors.append(f"{path}: expected-failure checks belong outside the library")
    if expected_modules:
        errors.append(f"Missing inventoried modules: {list(expected_modules)}")
    expected_escapes = [] if require_complete else manifest["trust_boundary"]
    key = lambda entry: (entry["file"], entry["directive"], entry["declaration"])
    if sorted(escapes, key=key) != sorted(expected_escapes, key=key):
        errors.append("Trust boundary differs from the required inventory: " + json.dumps(escapes))
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Alignment: {len(seen)} correspondences; {len(escapes)} inventoried trust directives")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    check(parser.parse_args().require_complete)
