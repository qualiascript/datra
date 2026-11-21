#!/usr/bin/env python3
"""Discover project Lean sources in dependency order, without external packages."""

from __future__ import annotations

import argparse
import re
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def lean_code(text: str) -> str:
    """Remove nested block comments and line comments, preserving line numbers."""
    depth = 0
    result = []
    index = 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif depth and pair == "-/":
            depth -= 1
            index += 2
        elif not depth and pair == "--":
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        else:
            result.append(text[index] if not depth or text[index] == "\n" else " ")
            index += 1
    return "".join(result)


def imports(source: str) -> list[str]:
    return [module for line in lean_code(source).splitlines()
            if re.match(r"^\s*import\s", line)
            for module in line.split()[1:]]


def local_module(module: str, root: Path = ROOT) -> Path | None:
    libraries = tomllib.loads((root / "lakefile.toml").read_text())["lean_lib"]
    for library in libraries:
        path = (root / library.get("srcDir", ".")).joinpath(*module.split(".")).with_suffix(".lean")
        if path.is_file():
            return path.resolve()
    for library in libraries:
        for glob in library.get("globs", library.get("roots", [library["name"]])):
            prefix = glob.removesuffix(".+").removesuffix(".*")
            if module == prefix or (glob != prefix and module.startswith(prefix + ".")):
                raise ValueError(f"Missing project Lean module: {module}")
    return None


def project_sources(entries: list[Path] | None = None, root: Path = ROOT) -> list[Path]:
    """Visit each local import once, before the source that imports it."""
    ordered: list[Path] = []
    visited: set[Path] = set()
    visiting: set[Path] = set()

    def visit(path: Path) -> None:
        path = path.resolve()
        if path in visiting:
            raise ValueError(f"Cyclic project Lean import: {path}")
        if path in visited:
            return
        visiting.add(path)
        for module in imports(path.read_text(encoding="utf-8")):
            dependency = local_module(module, root)
            if dependency is not None:
                visit(dependency)
        visiting.remove(path)
        visited.add(path)
        ordered.append(path)

    for entry in entries if entries is not None else [root / "datra.lean"]:
        visit(entry)
    return ordered


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", type=Path)
    args = parser.parse_args()
    try:
        print("\n".join(str(path) for path in project_sources(args.files or None)))
    except (OSError, ValueError) as error:
        parser.error(str(error))
