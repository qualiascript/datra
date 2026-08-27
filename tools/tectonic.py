#!/usr/bin/env python3
"""Install and run a pinned, project-local Tectonic TeX engine."""

from __future__ import annotations

import hashlib
import os
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile
from pathlib import Path


VERSION = "0.17.0"
RELEASE_ROOT = (
    "https://github.com/tectonic-typesetting/tectonic/releases/download/"
    f"tectonic%40{VERSION}"
)

# Checksums published with the official Tectonic 0.17.0 GitHub release.
ARTIFACTS = {
    ("Linux", "x86_64"): (
        f"tectonic-{VERSION}-x86_64-unknown-linux-musl.tar.gz",
        "8533d07f9ccbd7a65824b9e0459041bca34af1eb33daba48f59215593753a3b7",
    ),
    ("Darwin", "x86_64"): (
        f"tectonic-{VERSION}-x86_64-apple-darwin.tar.gz",
        "7c90ef5b6ddb1eb1937e4337add5237b79338e4b9676459fa91187d24d6cdf80",
    ),
    ("Darwin", "arm64"): (
        f"tectonic-{VERSION}-aarch64-apple-darwin.tar.gz",
        "a3f1cac7c5678f01661a92212f58480ae3b0634115d880dbc59e2953ded45667",
    ),
    ("Windows", "AMD64"): (
        f"tectonic-{VERSION}-x86_64-pc-windows-msvc.zip",
        "f61ce51f0b0ade1015b7de7ef368541c5424e9756ecbd0d7af97d6d48030845f",
    ),
}

PROJECT_ROOT = Path(__file__).resolve().parent.parent
INSTALL_ROOT = PROJECT_ROOT / ".tools" / "tectonic"
CACHE_ROOT = INSTALL_ROOT / "cache"
EXECUTABLE = INSTALL_ROOT / ("tectonic.exe" if os.name == "nt" else "tectonic")


def normalized_machine() -> str:
    machine = platform.machine()
    aliases = {"amd64": "x86_64", "AMD64": "AMD64", "aarch64": "arm64"}
    return aliases.get(machine, machine)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def install() -> None:
    if EXECUTABLE.is_file():
        return

    key = (platform.system(), normalized_machine())
    if key not in ARTIFACTS:
        supported = ", ".join(f"{system}/{machine}" for system, machine in ARTIFACTS)
        raise SystemExit(
            f"Unsupported platform {key[0]}/{key[1]}. Supported platforms: {supported}"
        )

    filename, expected_digest = ARTIFACTS[key]
    url = f"{RELEASE_ROOT}/{filename}"
    INSTALL_ROOT.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(dir=INSTALL_ROOT) as temporary_directory:
        temporary = Path(temporary_directory)
        archive = temporary / filename
        print(f"Downloading Tectonic {VERSION} for {key[0]}/{key[1]}...", flush=True)
        urllib.request.urlretrieve(url, archive)

        actual_digest = sha256(archive)
        if actual_digest != expected_digest:
            raise SystemExit(
                "Tectonic archive checksum mismatch:\n"
                f"  expected {expected_digest}\n"
                f"  received {actual_digest}"
            )

        extracted = temporary / "extracted"
        extracted.mkdir()
        if filename.endswith(".zip"):
            with zipfile.ZipFile(archive) as bundle:
                bundle.extractall(extracted)
        else:
            with tarfile.open(archive, "r:gz") as bundle:
                # The archive is safe to unpack after verification against the
                # checksum published with the pinned official release.
                bundle.extractall(extracted)

        executable_name = EXECUTABLE.name
        candidates = list(extracted.rglob(executable_name))
        if len(candidates) != 1:
            raise SystemExit(
                f"Expected one {executable_name!r} in the Tectonic archive; "
                f"found {len(candidates)}"
            )
        shutil.copy2(candidates[0], EXECUTABLE)
        EXECUTABLE.chmod(0o755)

    print(f"Installed {EXECUTABLE.relative_to(PROJECT_ROOT)}", flush=True)


def main() -> int:
    install()
    if sys.argv[1:] == ["--install-only"]:
        return 0

    CACHE_ROOT.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["TECTONIC_CACHE_DIR"] = str(CACHE_ROOT)
    completed = subprocess.run(
        [str(EXECUTABLE), *sys.argv[1:]],
        cwd=PROJECT_ROOT,
        env=environment,
        check=False,
    )
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
