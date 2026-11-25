#!/usr/bin/env python3
"""Check the correspondence manifest and reject unchecked core declarations."""
import argparse
import json
import re
from pathlib import Path

from lean_sources import lean_code, project_sources

ROOT = Path(__file__).resolve().parents[1]
CORE = ROOT / "datra-haskell/src/DatraCore"
MANIFEST = ROOT / "datra-lean/lean-correspondence.json"


def trust_directives(source):
    """Include trusted methods nested inside refined class/instance blocks."""
    return [(match[1], match[2])
            for annotation in re.finditer(r"\{-@(.*?)@-\}", source, re.S)
            for match in re.finditer(r"\b(assume|ignore)\s+([^\s:]+)", annotation[1])]


def private_liquid_imports(text):
    """Allow only an interface's own implementation to import its proof module."""
    declaration = re.search(r"^\s*module\s+([\w.]+)", text, re.M)
    module = declaration[1] if declaration else "Main"
    imports = re.findall(
        r'^\s*import\s+(?:\{-#\s*SOURCE\s*#-\}\s*)?(?:safe\s+)?'
        r'(?:qualified\s+)?(?:"[^"\n]+"\s+)?([A-Z][\w.]*)', text, re.M)
    return [imported for imported in imports
            if imported.endswith(".LiquidInternal")
            and module not in {imported.removesuffix(".LiquidInternal"),
                               imported.removesuffix(".LiquidInternal") + ".Internal"}]


def private_component_imports(text):
    """Private implementation modules stay within their owning component."""
    declaration = re.search(r"^\s*module\s+([\w.]+)", text, re.M)
    component = declaration[1].split(".")[0] if declaration else "Main"
    imports = re.findall(
        r'^\s*import\s+(?:\{-#\s*SOURCE\s*#-\}\s*)?(?:safe\s+)?'
        r'(?:qualified\s+)?(?:"[^"\n]+"\s+)?([A-Z][\w.]*)', text, re.M)
    return [imported for imported in imports
            if imported.endswith(".Internal") and imported.split(".")[0] != component]


def check(require_complete=False):
    manifest = json.loads(MANIFEST.read_text())
    sources = project_sources()
    lean = "\n".join(path.read_text() for path in sources)
    errors = []
    private_imports = []
    haskell_sources = (source for directory in ("src", "test", "app")
                       for source in (ROOT / "datra-haskell" / directory).rglob("*.hs"))
    for source in haskell_sources:
        text = source.read_text()
        for imported in private_liquid_imports(text):
            owner = imported.removesuffix(".LiquidInternal")
            errors.append(f"{source.relative_to(ROOT)}: import {owner}'s exposed interface "
                          f"instead of {imported}")
        for imported in private_component_imports(text):
            private_imports.append(f"{source.relative_to(ROOT)}: import an exposed interface "
                                   f"instead of {imported}")
    errors.extend(private_imports)
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
        reflected = re.findall(r"\{-@\s*(?:reflect|inline)\s+([\w.]+)", text)
        opaque_reflected = re.findall(r"\{-@\s*opaque-reflect\s+([\w.]+)", text)
        types = re.findall(r"^(?:data|newtype|class)\s+(\w+)", text, re.M)
        aliases = re.findall(r"^type\s+(?!role\b|family\b|instance\b)(\w+)", text, re.M)
        predicates = re.findall(r"\{-@\s*predicate\s+(\w+)", text)
        refinement_aliases = re.findall(r"\{-@\s*type\s+(\w+)", text)
        embeddings = re.findall(r"\{-@\s*embed\s+([^\n]*?)\s*@-\}", text)
        variances = [" ".join(value.split()) for value in
                     re.findall(r"\{-@\s*data\s+variance\s+(.+?)\s*@-\}", text, re.S)]
        path = str(source.relative_to(ROOT))
        refinements = re.findall(r"\{-@\s*(?:assume\s+)?([a-z]\w*)\s*::", text)
        refined_instances = [" ".join(value.split()) for value in
                             re.findall(r"\{-@\s*instance\s+(.*?)\s+where\b", text, re.S)]
        if reflected or opaque_reflected or types or aliases or predicates or refinement_aliases or refinements or variances or refined_instances:
            expected = expected_modules.pop(path, None)
            if (expected is None or expected["reflected"] != reflected
                    or expected.get("opaque_reflected", []) != opaque_reflected
                    or expected["types"] != types or expected["aliases"] != aliases
                    or expected["predicates"] != predicates
                    or expected["refinement_aliases"] != refinement_aliases
                    or expected["embeddings"] != embeddings
                    or expected.get("variances", []) != variances
                    or expected.get("refined_instances", []) != refined_instances
                    or expected["refinements"] != refinements):
                errors.append(f"Correspondence inventory drift: {path}")
        for directive, declaration in trust_directives(text):
            escapes.append({"file": path, "directive": directive, "declaration": declaration})
        if re.search(r"\bunsafeCoerce\b", text):
            errors.append(f"{path}: unsafeCoerce is forbidden")
        if re.search(r"\{-@\s*fail\s", text):
            errors.append(f"{path}: expected-failure checks belong outside the library")
    if expected_modules:
        errors.append(f"Missing inventoried modules: {list(expected_modules)}")
    expected_escapes = []
    if manifest["trust_boundary"]:
        errors.append("The trust boundary must remain empty")
    key = lambda entry: (entry["file"], entry["directive"], entry["declaration"])
    if sorted(escapes, key=key) != sorted(expected_escapes, key=key):
        errors.append("Trust boundary differs from the required inventory: " + json.dumps(escapes))
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Alignment: {len(seen)} correspondences; {len(escapes)} inventoried trust directives")
    if private_imports:
        print(f"Remaining private implementation imports: {len(private_imports)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    check(parser.parse_args().require_complete)
