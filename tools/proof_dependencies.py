"""Identify the exact upstream proof source that the acceptance gate rebuilds."""
import json
from pathlib import Path
import subprocess
import tomllib

from acceptance_utils import ROOT, digest, git_output

PACKAGE = "FiniteMathKernels"
URL = "https://github.com/larsbx/finite-math-kernels"
SUBDIR = "tests/lean"
MODULES = {"FiniteMathKernels.BinaryWeight": "FiniteMathKernels/BinaryWeight.lean"}


def binary_weight_sources(packages, *, root=ROOT):
    """Refuse a changed pin, dirty checkout, or source differing from its Git blob."""
    root, packages = Path(root), Path(packages)
    manifest = json.loads((root / "lake-manifest.json").read_text())
    requirements = tomllib.loads((root / "lakefile.toml").read_text())["require"]
    entries = [p for p in manifest["packages"] if p["name"] == PACKAGE]
    declarations = [p for p in requirements if p["name"] == PACKAGE]
    if len(entries) != 1 or len(declarations) != 1:
        raise RuntimeError("exactly one upstream binary-weight dependency is required")
    entry, declaration = entries[0], declarations[0]
    revision = entry.get("rev", "")
    if (len(revision) != 40 or any(c not in "0123456789abcdef" for c in revision)
            or entry.get("type") != "git" or entry.get("url") != URL
            or entry.get("subDir") != SUBDIR or entry.get("inputRev") != revision
            or declaration.get("git") != URL or declaration.get("rev") != revision
            or declaration.get("subDir") != SUBDIR):
        raise RuntimeError("binary-weight dependency must have matching exact Git pins and source root")
    checkout = packages / PACKAGE
    if git_output("rev-parse", "HEAD", cwd=checkout) != revision:
        raise RuntimeError("binary-weight dependency revision mismatch")
    if git_output("status", "--porcelain", "--untracked-files=no", cwd=checkout):
        raise RuntimeError("modified binary-weight dependency sources")
    sources, hashes = {}, {}
    for module, relative in MODULES.items():
        git_path = f"{SUBDIR}/{relative}"
        source = checkout / git_path
        blob = subprocess.check_output(["git", "show", f"{revision}:{git_path}"], cwd=checkout)
        if not source.is_file() or source.read_bytes() != blob:
            raise RuntimeError("binary-weight source differs from its pinned Git blob")
        sources[module] = source
        hashes[git_path] = digest(source)
    return sources, {"package": PACKAGE, "url": URL, "revision": revision,
                     "subdirectory": SUBDIR, "source_sha256": hashes,
                     "modules_rebuilt_and_audited": list(MODULES)}
