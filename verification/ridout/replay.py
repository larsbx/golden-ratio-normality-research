#!/usr/bin/env python3
"""Replay only the pinned Ridout/application import closure and audit its axioms."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

from claim_evidence import (CONFIG, LEAN_COMMIT, SCHEMA, audit_axioms,
                            registered_claims, validate_receipt)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
EXPECTED = {
    "mathlib": "5e0c4e5239cb0a2d86d68a884bf52cfd963fce22",
    "FiniteMathKernels": "8750345c496390a7ce4f6a80be331451aa999408",
    "SubspaceTheorems": "2fc7bea12d398fbc8ea758ecb8516efe8e3ef33d",
}
COMMANDS = []

def run(args, *, cwd=HERE, capture=False, quiet=False):
    COMMANDS.append({"cwd": str(cwd.relative_to(ROOT)) if cwd.is_relative_to(ROOT) else str(cwd),
                     "argv": args})
    result = subprocess.run(args, cwd=cwd, text=True, check=False,
                            stdout=subprocess.PIPE if capture else None,
                            stderr=subprocess.STDOUT if capture else None)
    if capture and not quiet:
        print(result.stdout, end="", flush=True)
    result.check_returncode()
    return result.stdout if capture else ""

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_root(expected_head=None):
    head = run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture=True).strip()
    if expected_head and head != expected_head:
        raise RuntimeError("Wrong or changed checkout revision")
    if run(["git", "status", "--porcelain", "--untracked-files=no"],
           cwd=ROOT, capture=True):
        raise RuntimeError("Modified checked-out source")
    return head

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
            match = re.match(r"^\s*(?:public\s+)?import\s+(?:all\s+)?(.+?)\s*$", line)
            if match:
                pending.extend(match.group(1).split("--")[0].split())
    return visited, sorted(mathlib)

def bind_sources(sources, head, dependencies):
    """Bind source bytes to committed blobs, including otherwise ignored files."""
    repositories = {ROOT: head, **{
        HERE / ".lake/packages" / name: revision
        for name, revision in dependencies.items()
    }}
    files = {ROOT / item["path"]: item["sha256"] for item in sources.values()}
    for name in sorted(CONFIG):
        files[ROOT / name] = None
    grouped = {}
    for path, expected_hash in files.items():
        owner = max((repo for repo in repositories if path.is_relative_to(repo)),
                    key=lambda repo: len(repo.parts))
        grouped.setdefault(owner, {})[path.relative_to(owner).as_posix()] = (
            path, expected_hash)
    bindings = {}
    for owner, owned in grouped.items():
        tree = run(["git", "ls-tree", "-r", "-z", repositories[owner], "--", *sorted(owned)],
                   cwd=owner, capture=True, quiet=True)
        blobs = {}
        for entry in tree.split("\0"):
            if entry:
                metadata, name = entry.split("\t", 1)
                mode, kind, oid = metadata.split()
                blobs[name] = (mode, kind, oid)
        for name, (path, expected_hash) in owned.items():
            if name not in blobs:
                raise RuntimeError("Untracked replay source: " + str(path))
            mode, kind, oid = blobs[name]
            if kind != "blob" or mode not in {"100644", "100755"} or path.is_symlink():
                raise RuntimeError("Replay source is not a regular Git blob: " + str(path))
            data = path.read_bytes()
            algorithm = {40: "sha1", 64: "sha256"}.get(len(oid))
            if algorithm is None:
                raise RuntimeError("Unsupported Git object identity")
            actual = hashlib.new(algorithm, b"blob " + str(len(data)).encode() + b"\0" + data)
            if actual.hexdigest() != oid:
                raise RuntimeError("Replay source differs from committed Git blob: " + str(path))
            digest = hashlib.sha256(data).hexdigest()
            if expected_hash is not None and digest != expected_hash:
                raise RuntimeError("Source changed during binding: " + str(path))
            bindings[str(path.relative_to(ROOT))] = {
                "repository": str(owner.relative_to(ROOT)), "revision": repositories[owner],
                "git_blob": oid, "sha256": digest,
            }
    return bindings

def main(output):
    output.mkdir(parents=True)
    expected_head = os.environ.get("EXPECTED_HEAD")
    head = check_root(expected_head)
    claims = registered_claims(head)
    lock_hash = sha(HERE / "lake-manifest.json")
    packages = manifest_packages()
    version_output = run(["lake", "env", "lean", "--version"], capture=True)
    version = version_output.strip().splitlines()[-1]
    if "version 4.35.0-rc3," not in version or "commit " + LEAN_COMMIT not in version:
        raise RuntimeError("Wrong Lean version")
    dependencies = check_revisions(packages)
    sources, mathlib_roots = import_closure()
    bindings = bind_sources(sources, head, dependencies)
    # Keep the pinned Mathlib cache, but rebuild the adapter and direct proof dependencies.
    for package in (HERE, HERE / ".lake/packages/SubspaceTheorems",
                    HERE / ".lake/packages/FiniteMathKernels/tests/lean"):
        build = package / ".lake/build"
        if build.exists():
            shutil.rmtree(build)
    run(["lake", "exe", "cache", "get", *mathlib_roots])
    run(["lake", "build", "+RidoutReplay"])
    audit = run(["lake", "env", "lean", "-DautoImplicit=false",
                 "-DwarningAsError=true", "Audit.lean"], capture=True).encode()
    (output / "axioms.log").write_bytes(audit)
    axioms = audit_axioms(audit)
    if sources != import_closure()[0]:
        raise RuntimeError("Sources changed during replay")
    if lock_hash != sha(HERE / "lake-manifest.json"):
        raise RuntimeError("Dependency manifest changed during replay")
    if bindings != bind_sources(sources, head, dependencies):
        raise RuntimeError("Source bindings changed during replay")
    if dependencies != check_revisions(packages):
        raise RuntimeError("Dependencies changed during replay")
    check_root(head)
    evidence = {"schema": SCHEMA, "status": "passed", "source_revision": head,
                "claims": claims, "lean": version.strip(), "axioms": axioms,
                "dependencies": dependencies, "manifest_sha256": lock_hash,
                "source_modules": sources, "mathlib_cache_roots": mathlib_roots,
                "source_bindings": bindings,
                "commands": COMMANDS, "audit_sha256": sha(output / "axioms.log")}
    validate_receipt(evidence, audit, head)
    (output / "evidence.json").write_text(json.dumps(evidence, indent=2) + "\n")
    print("RIDOUT_REPLAY_PASSED", flush=True)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=HERE / "build")
    main(parser.parse_args().output)
