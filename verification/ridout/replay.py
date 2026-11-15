#!/usr/bin/env python3
"""Replay only the pinned Ridout/application import closure and audit its axioms."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = HERE / "build"
EXPECTED = {
    "mathlib": "5e0c4e5239cb0a2d86d68a884bf52cfd963fce22",
    "FiniteMathKernels": "8750345c496390a7ce4f6a80be331451aa999408",
    "SubspaceTheorems": "2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d",
}
COMMANDS = []

def run(args, *, cwd=HERE, capture=False):
    COMMANDS.append({"cwd": str(cwd.relative_to(ROOT)) if cwd.is_relative_to(ROOT) else str(cwd),
                     "argv": args})
    result = subprocess.run(args, cwd=cwd, text=True, check=True,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.STDOUT if capture else None)
    if capture:
        print(result.stdout, end="", flush=True)
        return result.stdout
    return ""

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def manifest_packages():
    manifest = json.loads((HERE / "lake-manifest.json").read_text())
    packages = {p["name"]: p for p in manifest["packages"]}
    for name, expected in EXPECTED.items():
        if packages[name]["rev"] != expected:
            raise RuntimeError("Unexpected dependency pin: " + name)
    return packages

def check_revisions(packages):
    checked = {}
    for name, package in packages.items():
        path = HERE / ".lake" / "packages" / name
        actual = run(["git", "rev-parse", "HEAD"], cwd=path, capture=True).strip()
        if actual != package["rev"]:
            raise RuntimeError("Dependency revision mismatch: " + name)
        dirty = run(["git", "status", "--porcelain", "--untracked-files=no"],
                    cwd=path, capture=True)
        if dirty:
            raise RuntimeError("Modified dependency source: " + name)
        checked[name] = actual
    return checked

def import_closure():
    roots = {
        "GoldenNormality": ROOT,
        "RidoutReplay": HERE,
        "RidoutBridge": HERE,
        "DiophantineApproximation": HERE / ".lake/packages/SubspaceTheorems",
        "ArithmeticHeights": HERE / ".lake/packages/SubspaceTheorems",
        "FiniteMathKernels": HERE / ".lake/packages/FiniteMathKernels/tests/lean",
    }
    visited = {}
    mathlib = set()
    pending = ["RidoutReplay"]
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        prefix = module.split(".")[0]
        if prefix == "Mathlib":
            mathlib.add(module)
            continue
        if prefix in {"Lean", "Std", "Init", "Aesop", "Batteries", "Qq"}:
            continue
        if prefix not in roots:
            raise RuntimeError("Unexpected import root: " + module)
        path = roots[prefix] / (module.replace(".", "/") + ".lean")
        data = path.read_text()
        visited[module] = {"path": str(path.relative_to(ROOT)), "sha256": sha(path)}
        for line in data.splitlines():
            match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*$", line)
            if match:
                pending.extend(match.group(1).split("--")[0].split())
    return visited, sorted(mathlib)

def main():
    OUT.mkdir(exist_ok=True)
    expected_head = os.environ.get("EXPECTED_HEAD")
    head = run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture=True).strip()
    if expected_head and head != expected_head:
        raise RuntimeError("Wrong checkout revision")
    if run(["git", "status", "--porcelain", "--untracked-files=no"],
           cwd=ROOT, capture=True):
        raise RuntimeError("Modified checked-out source")
    lock_hash = sha(HERE / "lake-manifest.json")
    packages = manifest_packages()
    version = run(["lake", "env", "lean", "--version"], capture=True)
    if "version 4.35.0-rc3" not in version:
        raise RuntimeError("Wrong Lean version")
    dependencies = check_revisions(packages)
    sources, mathlib_roots = import_closure()
    run(["lake", "exe", "cache", "get", *mathlib_roots])
    run(["lake", "build", "+RidoutReplay"])
    audit = run(["lake", "env", "lean", "Audit.lean"], capture=True)
    (OUT / "axioms.log").write_text(audit)
    if "RIDOUT_AUDIT_COMPLETE" not in audit:
        raise RuntimeError("Missing compiled audit completion")
    if sources != import_closure()[0]:
        raise RuntimeError("Sources changed during replay")
    if lock_hash != sha(HERE / "lake-manifest.json"):
        raise RuntimeError("Dependency manifest changed during replay")
    if dependencies != check_revisions(packages):
        raise RuntimeError("Dependencies changed during replay")
    evidence = {"status": "passed", "source_revision": head, "lean": version.strip(),
                "dependencies": dependencies, "manifest_sha256": lock_hash,
                "source_modules": sources, "mathlib_cache_roots": mathlib_roots,
                "commands": COMMANDS, "audit_sha256": sha(OUT / "axioms.log")}
    (OUT / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("RIDOUT_REPLAY_PASSED", flush=True)

if __name__ == "__main__":
    main()
