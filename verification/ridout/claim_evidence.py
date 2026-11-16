#!/usr/bin/env python3
"""Verify a Ridout receipt locally or against an exact GitHub Actions attempt."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
REPO = "larsbx/golden-ratio-normality-research"
WORKFLOW = ".github/workflows/ridout-replay.yml"
SCHEMA = "golden-normality-ridout-evidence-v1"
LEAN_COMMIT = "470d5ce1400764999581fd26d5d72b00d990b0f4"
EXTERNAL_THEOREM = "Rat.finite_setOf_ridout"
BRIDGE = "GoldenNormality.RidoutBridge."
CARRY = "GoldenNormality.BinaryComplement."
CLAIMS = {
    "ridout_actual_dyadic_separation": BRIDGE + "alpha_eventualDyadicSeparation",
    "ridout_fixed_multiplier_separation": BRIDGE + "fixedMultiplier_eventualDyadicSeparation",
    "ridout_fixed_lag_separation": BRIDGE + "fixedLag_eventual_separation",
    "ridout_fixed_lag_repeated_block_width": BRIDGE + "fixedLag_repeatedBlock_mul_lt",
    "ridout_actual_zero_count_eventually_exceeds": BRIDGE + "zero_count_eventually_exceeds",
    "ridout_actual_zero_count_exceeds": BRIDGE + "zero_count_exceeds",
}
AUDITED = set(CLAIMS.values()) | {
    BRIDGE + "finite_dyadicCandidates",
    BRIDGE + "eventualDyadicSeparation_of_finite_candidates",
    BRIDGE + "algebraic_alpha",
    EXTERNAL_THEOREM,
    "GoldenNormality.BinaryDyadicOrbit.irrational_alpha",
    CARRY + "zero_count_eventually_exceeds_of_eventual_dyadic_separation",
    CARRY + "zero_count_exceeds_of_eventual_dyadic_separation",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONTROLS = ("RIDOUT_CONTROLS\tone_eventually,one_arbitrarily_late,rational_half,"
            "alpha_exponent_zero,negative_multiplier,lag_zero,overlapping_repeat_cutoff")
CONFIG = {
    "claims.json", WORKFLOW,
    *("verification/ridout/" + name for name in (
        "Audit.lean", "claim_evidence.py", "replay.py", "lakefile.toml",
        "lake-manifest.json", "lean-toolchain",
    )),
}
REQUIRED_MODULES = {
    "GoldenNormality.BinaryGapTransfer",
    "RidoutReplay",
    "RidoutBridge.FiniteToSeparation",
    "RidoutBridge.RidoutSpecialization",
    "DiophantineApproximation.Ridout",
}
PROOF_STEP = "Compile source closure and inspect axioms"
UPLOAD_STEP = "Retain exact-source proof evidence"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def committed(path, head):
    return git("show", f"{head}:{path}")


def registered_claims(head):
    ledger = json.loads(committed("claims.json", head))
    lane = ledger["acceptance_lanes"]["ridout"]
    require(lane == {
        "replay": "verification/ridout/replay.py",
        "audit": "verification/ridout/Audit.lean",
        "toolchain": "verification/ridout/lean-toolchain",
        "dependency_lock": "verification/ridout/lake-manifest.json",
        "external_declaration": EXTERNAL_THEOREM,
        "workflow": WORKFLOW,
        "hosted_verifier": "verification/ridout/claim_evidence.py",
    }, "Ridout acceptance lane differs from the verifier contract")
    claims = [row for row in ledger["claims"] if row.get("acceptance_lane") == "ridout"]
    require(len(claims) == len(CLAIMS) and all(
        row["kind"] == "universal_lean_theorem" for row in claims
    ) and {row["id"]: row["declaration"] for row in claims} == CLAIMS,
        "Ridout claim registrations differ from the compiled theorem contract")
    return claims


def audit_axioms(audit):
    lines = audit.decode().splitlines()
    require(lines.count(CONTROLS) == 1 and lines.count("RIDOUT_AUDIT_COMPLETE") == 1,
            "Missing or duplicate mathematical controls or audit completion")
    axioms = {}
    for line in lines:
        if not line.startswith("RIDOUT_AXIOMS\t"):
            continue
        _, declaration, printed = line.split("\t")
        require(declaration not in axioms and printed.startswith("#[") and printed.endswith("]"),
                "Duplicate or malformed axiom audit row")
        names = printed[2:-1].split(", ") if printed != "#[]" else []
        require(set(names) <= ALLOWED_AXIOMS, f"Unexpected transitive axiom for {declaration}")
        axioms[declaration] = sorted(names)
    require(axioms.keys() == AUDITED, "Incomplete transitive axiom audit")
    return axioms


def validate_receipt(receipt, audit, head):
    require(receipt["schema"] == SCHEMA and receipt["status"] == "passed"
            and receipt["source_revision"] == head, "Receipt does not pass at the requested revision")
    require(receipt["claims"] == registered_claims(head), "Receipt cites different registered claims")
    require(f"version 4.35.0-rc3," in receipt["lean"] and
            f"commit {LEAN_COMMIT}," in receipt["lean"], "Receipt uses the wrong Lean compiler")
    manifest = committed("verification/ridout/lake-manifest.json", head)
    dependencies = {row["name"]: row["rev"] for row in json.loads(manifest)["packages"]}
    require(receipt["manifest_sha256"] == digest(manifest)
            and receipt["dependencies"] == dependencies, "Missing or mismatched locked dependencies")
    require(receipt["audit_sha256"] == digest(audit) and receipt["axioms"] == audit_axioms(audit),
            "Audit log differs from the receipt")
    modules = receipt["source_modules"]
    bindings = receipt["source_bindings"]
    require(REQUIRED_MODULES <= modules.keys(), "Missing required application or Ridout proof modules")
    require(modules["DiophantineApproximation.Ridout"]["path"] ==
            "verification/ridout/.lake/packages/SubspaceTheorems/DiophantineApproximation/Ridout.lean",
            "Ridout theorem is not bound to the pinned Subspace-Theorems checkout")
    require(set(bindings) == CONFIG | {row["path"] for row in modules.values()},
            "Missing or extraneous source bindings")
    for module, row in modules.items():
        require(row["path"].endswith("/" + module.replace(".", "/") + ".lean")
                or row["path"] == module.replace(".", "/") + ".lean",
                f"Wrong source path for {module}")
        require(row["sha256"] == bindings[row["path"]]["sha256"], f"Inconsistent hash for {module}")
    for path, binding in bindings.items():
        owner = binding["repository"]
        if path.startswith("verification/ridout/.lake/packages/"):
            package = path.split("/")[4]
            require(owner == f"verification/ridout/.lake/packages/{package}"
                    and package in dependencies and binding["revision"] == dependencies[package]
                    and re.fullmatch(r"[0-9a-f]{40}", binding["git_blob"])
                    and re.fullmatch(r"[0-9a-f]{64}", binding["sha256"]),
                    f"Wrong external source binding for {path}")
        else:
            data = committed(path, head)
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            require(owner == "." and binding["revision"] == head
                    and binding["git_blob"] == blob and binding["sha256"] == digest(data),
                    f"Wrong committed source binding for {path}")


def github_api(path):
    return subprocess.check_output(["gh", "api", "--hostname", "github.com", path])


def hosted_archive(run_id, head, api=github_api):
    base = f"repos/{REPO}/actions"
    run_path = f"{base}/runs/{run_id}"
    run = json.loads(api(run_path))
    attempt = run["run_attempt"]
    require(run["id"] == run_id and type(attempt) is int and attempt > 0
            and run["repository"]["full_name"] == REPO
            and run["path"] == WORKFLOW and run["head_sha"] == head
            and run["event"] in {"pull_request", "push", "workflow_dispatch"}
            and run["status"] == "completed" and run["conclusion"] == "success",
            "No successful Ridout workflow for the requested revision")
    jobs = json.loads(api(f"{run_path}/attempts/{attempt}/jobs?per_page=100"))["jobs"]
    matches = [job for job in jobs if job["name"] == "ridout"]
    require(len(matches) == 1, "Missing or ambiguous Ridout job")
    job = matches[0]
    require(job["run_id"] == run_id and job["run_attempt"] == attempt
            and job["head_sha"] == head
            and job["status"] == "completed" and job["conclusion"] == "success",
            "Ridout job did not pass on this workflow attempt")
    for name in (PROOF_STEP, UPLOAD_STEP):
        steps = [step for step in job["steps"] if step["name"] == name]
        require(len(steps) == 1 and steps[0]["status"] == "completed"
                and steps[0]["conclusion"] == "success", f"Required step did not pass: {name}")
    name = f"ridout-{head}-{attempt}"
    artifacts = json.loads(api(f"{run_path}/artifacts?name={name}"))["artifacts"]
    require(len(artifacts) == 1 and artifacts[0]["name"] == name and not artifacts[0]["expired"],
            "Missing, expired or ambiguous exact-attempt proof artifact")
    artifact = artifacts[0]
    origin = artifact["workflow_run"]
    require(origin["id"] == run_id and origin["head_sha"] == head,
            "Artifact belongs to a different run or revision")
    archive = api(f'{base}/artifacts/{artifact["id"]}/zip')
    require(artifact["digest"] == "sha256:" + digest(archive), "Hosted artifact digest mismatch")
    return archive, attempt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("revision", help="Exact 40-character Git commit")
    modes = parser.add_mutually_exclusive_group(required=True)
    modes.add_argument("--local", type=Path, metavar="DIRECTORY")
    modes.add_argument("--run-id", type=int, help="GitHub Actions Ridout workflow run ID")
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{40}", args.revision), "Supply an exact 40-character revision")
    require(Path(__file__).read_bytes() == committed("verification/ridout/claim_evidence.py", args.revision),
            "Use the receipt verifier from the requested source revision")
    if args.local is not None:
        receipt = json.loads((args.local / "evidence.json").read_bytes())
        audit = (args.local / "axioms.log").read_bytes()
        evidence = {"scope": "local_receipt"}
    else:
        archive, attempt = hosted_archive(args.run_id, args.revision)
        with zipfile.ZipFile(io.BytesIO(archive)) as files:
            require(sorted(files.namelist()) == ["axioms.log", "evidence.json"],
                    "Unexpected hosted artifact contents")
            receipt = json.loads(files.read("evidence.json"))
            audit = files.read("axioms.log")
        evidence = {"scope": "hosted", "run_id": args.run_id, "attempt": attempt}
    validate_receipt(receipt, audit, args.revision)
    print(json.dumps({**evidence, "source_revision": args.revision, "ridout_claims": list(CLAIMS)}))


if __name__ == "__main__":
    main()
