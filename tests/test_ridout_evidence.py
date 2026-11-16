"""Acceptance controls for revision-bound Ridout receipts and GitHub run metadata."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "ridout_evidence", ROOT / "verification/ridout/claim_evidence.py")
EVIDENCE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EVIDENCE)


class RidoutReceiptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.head = EVIDENCE.git("rev-parse", "HEAD").decode().strip()
        # Build a verifier fixture from archived module inventory. The fixture is not a replay.
        archive = ROOT / "evidence/ridout/2ba20e1c"
        axioms = "#[propext, Classical.choice, Quot.sound]"
        rows = [f"RIDOUT_AXIOMS\t{name}\t{axioms}" for name in sorted(EVIDENCE.AUDITED)]
        cls.audit = "\n".join([*rows, EVIDENCE.CONTROLS, "RIDOUT_AUDIT_COMPLETE"]).encode()
        cls.receipt = json.loads((archive / "evidence.json").read_bytes())
        cls.receipt.update(schema=EVIDENCE.SCHEMA, source_revision=cls.head,
                           claims=EVIDENCE.registered_claims(cls.head),
                           audit_sha256=EVIDENCE.digest(cls.audit),
                           axioms=EVIDENCE.audit_axioms(cls.audit))
        bindings = cls.receipt["source_bindings"]
        paths = EVIDENCE.CONFIG | {path for path, row in bindings.items()
                                   if row["repository"] == "."}
        for path in paths:
            data = EVIDENCE.committed(path, cls.head)
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            bindings[path] = {"repository": ".", "revision": cls.head,
                              "git_blob": blob, "sha256": EVIDENCE.digest(data)}
        for module in cls.receipt["source_modules"].values():
            module["sha256"] = bindings[module["path"]]["sha256"]

    def test_exact_revision_receipt(self):
        EVIDENCE.validate_receipt(self.receipt, self.audit, self.head)

    def test_stale_revision(self):
        with self.assertRaisesRegex(ValueError, "requested revision"):
            EVIDENCE.validate_receipt(self.receipt, self.audit, "0" * 40)

    def test_claim_change(self):
        receipt = copy.deepcopy(self.receipt)
        receipt["claims"][0]["conclusion"] = "An unregistered statement"
        with self.assertRaisesRegex(ValueError, "different registered claims"):
            EVIDENCE.validate_receipt(receipt, self.audit, self.head)

    def test_missing_external_dependency(self):
        receipt = copy.deepcopy(self.receipt)
        del receipt["dependencies"]["SubspaceTheorems"]
        with self.assertRaisesRegex(ValueError, "Missing or mismatched locked dependencies"):
            EVIDENCE.validate_receipt(receipt, self.audit, self.head)

    def test_wrong_external_source_revision(self):
        receipt = copy.deepcopy(self.receipt)
        ridout = receipt["source_modules"]["DiophantineApproximation.Ridout"]["path"]
        receipt["source_bindings"][ridout]["revision"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "Wrong external source binding"):
            EVIDENCE.validate_receipt(receipt, self.audit, self.head)

    def test_wrong_committed_source_blob(self):
        receipt = copy.deepcopy(self.receipt)
        receipt["source_bindings"]["claims.json"]["git_blob"] = "0" * 40
        with self.assertRaisesRegex(ValueError, "Wrong committed source binding"):
            EVIDENCE.validate_receipt(receipt, self.audit, self.head)

    def test_missing_mathematical_control(self):
        with self.assertRaisesRegex(ValueError, "mathematical controls"):
            EVIDENCE.audit_axioms(self.audit.replace(EVIDENCE.CONTROLS.encode(), b""))

    def test_unexpected_transitive_axiom(self):
        with self.assertRaisesRegex(ValueError, "Unexpected transitive axiom"):
            EVIDENCE.audit_axioms(self.audit.replace(b"Quot.sound", b"sorryAx"))

    def test_missing_fixed_lag_theorem(self):
        theorem = b".fixedLag_repeatedBlock_mul_lt\t"
        audit = b"\n".join(line for line in self.audit.splitlines() if theorem not in line)
        with self.assertRaisesRegex(ValueError, "Incomplete transitive axiom audit"):
            EVIDENCE.audit_axioms(audit)

    def test_replay_refuses_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            stale = Path(directory) / "evidence.json"
            stale.write_text("old")
            run = subprocess.run(
                [sys.executable, str(ROOT / "verification/ridout/replay.py"),
                 "--output", directory], text=True, capture_output=True)
            self.assertNotEqual(run.returncode, 0)
            self.assertIn("FileExistsError", run.stderr)
            self.assertEqual(stale.read_text(), "old")


class RidoutHostedTests(unittest.TestCase):
    def setUp(self):
        self.head = "1" * 40
        archive = b"test archive"
        base = f"repos/{EVIDENCE.REPO}/actions"
        run = f"{base}/runs/17"
        self.run = {"id": 17, "run_attempt": 2, "repository": {"full_name": EVIDENCE.REPO},
                    "path": EVIDENCE.WORKFLOW, "head_sha": self.head, "event": "pull_request",
                    "status": "completed", "conclusion": "success"}
        self.job = {"run_id": 17, "name": "ridout", "run_attempt": 2, "head_sha": self.head,
                    "status": "completed", "conclusion": "success", "steps": [
                        {"name": name, "status": "completed", "conclusion": "success"}
                        for name in (EVIDENCE.PROOF_STEP, EVIDENCE.UPLOAD_STEP)]}
        name = f"ridout-{self.head}-2"
        self.artifact = {"id": 24, "name": name, "expired": False,
                         "workflow_run": {"id": 17, "head_sha": self.head},
                         "digest": "sha256:" + EVIDENCE.digest(archive)}
        self.responses = {run: self.run,
                          f"{run}/attempts/2/jobs?per_page=100": {"jobs": [self.job]},
                          f"{run}/artifacts?name={name}": {"artifacts": [self.artifact]},
                          f"{base}/artifacts/24/zip": archive}

    def api(self, path):
        value = self.responses[path]
        return value if isinstance(value, bytes) else json.dumps(value).encode()

    def test_successful_exact_attempt(self):
        self.assertEqual(EVIDENCE.hosted_archive(17, self.head, self.api), (b"test archive", 2))

    def test_unexecuted_workflow(self):
        self.run.update(status="queued", conclusion=None)
        with self.assertRaisesRegex(ValueError, "No successful Ridout workflow"):
            EVIDENCE.hosted_archive(17, self.head, self.api)

    def test_skipped_proof_step(self):
        self.job["steps"][0]["conclusion"] = "skipped"
        with self.assertRaisesRegex(ValueError, "Required step did not pass"):
            EVIDENCE.hosted_archive(17, self.head, self.api)

    def test_wrong_attempt(self):
        self.job["run_attempt"] = 1
        with self.assertRaisesRegex(ValueError, "did not pass on this workflow attempt"):
            EVIDENCE.hosted_archive(17, self.head, self.api)

    def test_wrong_artifact_digest(self):
        self.artifact["digest"] = "sha256:" + "0" * 64
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            EVIDENCE.hosted_archive(17, self.head, self.api)


if __name__ == "__main__":
    unittest.main()
