"""Admission tests for the separately pinned upstream Lean source."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import proof_dependencies as dependency
from acceptance_utils import digest, verify_revision_sources


class ProofDependencyAdmission(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.packages = self.root / "packages"
        self.checkout = self.packages / dependency.PACKAGE
        self.checkout.mkdir(parents=True)
        self.git("init", "-q")
        self.source = self.checkout / dependency.SUBDIR / next(iter(dependency.MODULES.values()))
        self.source.parent.mkdir(parents=True)
        self.source.write_text("def fixture : Nat := 0\n")
        self.git("add", ".")
        self.git("-c", "user.name=Admission Test", "-c", "user.email=test@example.invalid",
                 "commit", "-q", "-m", "Fixture")
        self.revision = self.git("rev-parse", "HEAD").strip()
        self.entry = {"name": dependency.PACKAGE, "url": dependency.URL,
                      "type": "git", "rev": self.revision, "inputRev": self.revision,
                      "subDir": dependency.SUBDIR}
        self.write_manifest()
        (self.root / "lakefile.toml").write_text(
            f'[[require]]\nname = "{dependency.PACKAGE}"\ngit = "{dependency.URL}"\n'
            f'rev = "{self.revision}"\nsubDir = "{dependency.SUBDIR}"\n')

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.checkout, text=True,
                                       stderr=subprocess.STDOUT)

    def write_manifest(self, entries=None):
        (self.root / "lake-manifest.json").write_text(
            json.dumps({"packages": entries if entries is not None else [self.entry]}))

    def admit(self):
        return dependency.binary_weight_sources(self.packages, root=self.root)

    def test_exact_checkout_binds_source_and_revision(self):
        sources, identity = self.admit()
        self.assertEqual(list(sources.values()), [self.source])
        self.assertEqual(identity["revision"], self.revision)
        self.assertEqual(identity["modules_rebuilt_and_audited"], ["FiniteMathKernels.BinaryWeight"])

    def test_dirty_upstream_source_is_rejected(self):
        self.source.write_text("def fixture : Nat := 1\n")
        with self.assertRaisesRegex(RuntimeError, "modified"):
            self.admit()

    def test_git_status_suppression_does_not_hide_modified_source(self):
        # Even an assume-unchanged index bit cannot replace the pinned proof bytes.
        self.git("update-index", "--assume-unchanged", str(self.source.relative_to(self.checkout)))
        self.source.write_text("def fixture : Nat := 1\n")
        self.assertEqual(self.git("status", "--porcelain"), "")
        with self.assertRaisesRegex(RuntimeError, "pinned Git blob"):
            self.admit()

    def test_moving_branch_selector_is_rejected(self):
        self.entry["inputRev"] = "main"
        self.write_manifest()
        with self.assertRaisesRegex(RuntimeError, "exact Git pins"):
            self.admit()

    def test_configuration_and_manifest_must_agree(self):
        config = self.root / "lakefile.toml"
        config.write_text(config.read_text().replace(self.revision, "0" * 40))
        with self.assertRaisesRegex(RuntimeError, "matching exact Git pins"):
            self.admit()

    def test_wrong_source_root_is_rejected(self):
        self.entry["subDir"] = "../elsewhere"
        self.write_manifest()
        with self.assertRaisesRegex(RuntimeError, "source root"):
            self.admit()

    def test_missing_or_duplicate_dependency_is_rejected(self):
        for entries in ([], [self.entry, self.entry]):
            with self.subTest(entries=len(entries)):
                self.write_manifest(entries)
                with self.assertRaisesRegex(RuntimeError, "exactly one"):
                    self.admit()

    def test_clean_wrong_revision_is_rejected(self):
        self.source.write_text("def fixture : Nat := 1\n")
        self.git("add", ".")
        self.git("-c", "user.name=Admission Test", "-c", "user.email=test@example.invalid",
                 "commit", "-q", "-m", "Changed fixture")
        with self.assertRaisesRegex(RuntimeError, "revision mismatch"):
            self.admit()

    def test_project_source_identity_binds_exact_git_blob(self):
        hashes = {self.source.relative_to(self.checkout).as_posix(): digest(self.source)}
        verify_revision_sources(self.revision, hashes, root=self.checkout)

    def test_project_source_hidden_change_is_rejected(self):
        relative = self.source.relative_to(self.checkout).as_posix()
        self.git("update-index", "--assume-unchanged", relative)
        self.source.write_text("def fixture : Nat := 1\n")
        hashes = {relative: digest(self.source)}
        with self.assertRaisesRegex(RuntimeError, "pinned Git blob"):
            verify_revision_sources(self.revision, hashes, root=self.checkout)

    def test_project_dirty_checkout_is_rejected(self):
        hashes = {self.source.relative_to(self.checkout).as_posix(): digest(self.source)}
        (self.checkout / "unexpected.txt").write_text("uncommitted input\n")
        with self.assertRaisesRegex(RuntimeError, "clean source checkout"):
            verify_revision_sources(self.revision, hashes, root=self.checkout)

    def test_project_omitted_input_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "committed file set"):
            verify_revision_sources(self.revision, {}, root=self.checkout)


if __name__ == "__main__":
    unittest.main()
