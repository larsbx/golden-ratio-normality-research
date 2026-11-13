#!/usr/bin/env python3
"""Full first-milestone acceptance, with no optional proof or native stages."""
import argparse
import json
import os
from pathlib import Path
import platform
import re
import sys

from acceptance_utils import (CONTRACT, ROOT, command, digest, git_output,
                              locate_program, source_hashes, utc_now, verify_submodule, write_json)
import native_conformance

MODULES = ["GoldenNormality.Blocks", "GoldenNormality.Prefix",
           "GoldenNormality.Automaton", "GoldenNormality.Certificates",
           "GoldenNormality.Normality", "GoldenNormality", "GoldenNormality.Contracts"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONTRACT_NAMES = ["root", "adjacentPrefixes", "blockSemantics", "consecutiveCount",
                  "chunkBoundary", "automatonLanguage", "automatonAllInputs", "automatonPowerInput"]


def audit_source(modules, *, print_contracts=False):
    imports = "\n".join(f"import {module}" for module in modules)
    targets = ", ".join(f"(`{module}, {0 if module == 'GoldenNormality' else 1})"
                        for module in modules)
    text = imports + f'''
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array (Name × Nat) := #[{targets}]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (moduleName, minimumProofs) in targets do
    let some idx := env.getModuleIdx? moduleName | throwError "Missing audited module"
    let data := env.header.moduleData[idx.toNat]!
    let mut count := 0
    let mut proofs := 0
    for info in data.constants do
      let name := info.name
      if info.isAxiom then throwError "Local audited axiom"
      let axs ← collectAxioms name
      for ax in axs do
        if !allowed.contains ax then throwError "Nonstandard transitive axiom"
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let names := String.intercalate "," (axs.toList.map toString)
      liftIO <| IO.println s!"GNR_AXIOMS\t{{moduleName}}\t{{name}}\t{{names}}"
    if proofs < minimumProofs then throwError "Missing compiled proofs"
    liftIO <| IO.println s!"GNR_COMPLETE\t{{moduleName}}\t{{count}}\t{{proofs}}"
'''
    if print_contracts:
        for name in CONTRACT_NAMES:
            text += f"\n#check GoldenNormality.Contracts.{name}"
    return text + "\n"


def parse_audit(output, modules):
    declarations = {module: {} for module in modules}
    completed = {}
    for line in output.splitlines():
        if line.startswith("GNR_AXIOMS\t"):
            _, module, name, axes = line.split("\t")
            if module not in declarations or module in completed or name in declarations[module]:
                raise RuntimeError("duplicate or unexpected compiled audit declaration")
            axioms = set(filter(None, axes.split(",")))
            if axioms - ALLOWED_AXIOMS:
                raise RuntimeError("unexpected axiom in audit receipt")
            declarations[module][name] = sorted(axioms)
        elif line.startswith("GNR_COMPLETE\t"):
            _, module, count, proofs = line.split("\t")
            if module not in declarations or module in completed:
                raise RuntimeError("duplicate or unexpected audit completion")
            if int(count) != len(declarations[module]) or not 0 <= int(proofs) <= int(count):
                raise RuntimeError("incomplete audit receipt")
            completed[module] = {"declarations": int(count), "theorems": int(proofs)}
    if set(completed) != set(modules):
        raise RuntimeError("missing compiled module audit")
    names = declarations["GoldenNormality.Contracts"]
    if any(f"GoldenNormality.Contracts.{name}" not in names for name in CONTRACT_NAMES):
        raise RuntimeError("missing public contract declaration")
    expected_receipts = set()
    for i, (base, length, width) in enumerate(CONTRACT["prefix_cases"]):
        expected_receipts.update(f"prefix_{i}_{n}" for n in range(length + 1))
        expected_receipts.update(f"digit_{i}_{n}" for n in range(length))
        expected_receipts.add(f"digits_{i}")
        for value in range(base ** width):
            expected_receipts.update((f"count_{i}_{value}", f"actualCount_{i}_{value}"))
    for q in range(CONTRACT["automaton_values"]):
        expected_receipts.update((f"input_{q}", f"output_{q}", f"predicate_{q}"))
        if q and q & (q - 1) == 0:
            expected_receipts.add(f"powerDigit_{q.bit_length()-1}")
    missing = {f"GoldenNormality.Receipts.{name}" for name in expected_receipts} - declarations["Receipts"].keys()
    if missing:
        raise RuntimeError(f"missing compiled finite receipt declarations: {sorted(missing)[:5]}")
    if completed["Receipts"]["theorems"] < len(expected_receipts):
        raise RuntimeError("finite receipt declarations did not compile as proofs")
    completed["Receipts"]["required_receipt_theorems"] = len(expected_receipts)
    return completed, declarations


def dependency_paths(packages):
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    paths, revisions = [], {}
    for package in manifest["packages"]:
        path = packages / package["name"]
        revision = git_output("rev-parse", "HEAD", cwd=path)
        if revision != package["rev"]:
            raise RuntimeError(f"dependency pin mismatch: {package['name']}")
        if git_output("status", "--porcelain", "--untracked-files=no", cwd=path):
            raise RuntimeError(f"modified dependency sources: {package['name']}")
        compiled = path / ".lake/build/lib/lean"
        if compiled.is_dir():
            paths.append(str(compiled))
        revisions[package["name"]] = revision
    if not (packages / "mathlib/.lake/build/lib/lean/Mathlib/Analysis/Real/Sqrt.olean").is_file():
        raise RuntimeError("missing mathlib compiled cache; run lake exe cache get")
    return paths, revisions


def run(output):
    output = Path(output)
    output = (output if output.is_absolute() else ROOT / output).resolve()
    if output.exists() and any(output.iterdir()):
        raise RuntimeError(f"acceptance output must be empty: {output}")
    output.mkdir(parents=True, exist_ok=True)
    report = {"schema": "golden-normality-acceptance-v1", "accepted": False,
              "started_utc": utc_now(), "source_commit": git_output("rev-parse", "HEAD"),
              "source_tree_dirty": bool(git_output("status", "--porcelain")),
              "python": {"version": sys.version, "executable": sys.executable},
              "platform": platform.platform(),
              "source_sha256": source_hashes()}
    write_json(output / "report.json", report)
    try:
        sources = [ROOT / (module.replace(".", "/") + ".lean") for module in MODULES]
        discovered = {ROOT / "GoldenNormality.lean", *(ROOT / "GoldenNormality").rglob("*.lean")}
        if set(sources) != discovered:
            raise RuntimeError("every project Lean module must appear in the audited build list")
        for source in sources:
            # Additional text hygiene only; compiled closure audit is authoritative.
            if re.search(r"\b(sorry|admit|native_decide|axiom)\b", source.read_text()):
                raise RuntimeError(f"forbidden proof escape in project source: {source}")
        command([sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"],
                output / "oracle-tests.json", timeout=120)
        report["native"], generated = native_conformance.run(output / "native")
        lean = locate_program("LEAN_BIN", "lean")
        version = command([lean, "--version"], output / "lean-version.json", timeout=30)
        detected = re.search(r"\bversion ([^,\s)]+)", version.stdout)
        if detected is None or detected.group(1) != CONTRACT["lean_version"]:
            raise RuntimeError("Lean version differs from pinned contract")
        packages = Path(os.environ.get("GNR_MATHLIB_PACKAGES", ROOT / ".lake/packages")).resolve()
        paths, report["dependency_revisions"] = dependency_paths(packages)
        compiled = output / "lib"
        compiled.mkdir()
        env = os.environ.copy()
        # Never reuse project oleans: only this fresh output and pinned dependencies.
        env["LEAN_PATH"] = os.pathsep.join([str(compiled), *paths])
        env["LEAN_NUM_THREADS"] = "1"
        report["lean"] = {"version": version.stdout.strip(), "invocation": lean,
                          "invocation_file_sha256": digest(lean),
                          "package_cache": str(packages),
                          "LD_PRELOAD": env.get("LD_PRELOAD", "")}

        def compile_file(source, name, *, expect_success=True, emit=True):
            target = compiled / (name.replace(".", "/") + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            module_root = Path(source).parents[len(name.split(".")) - 1]
            args = [lean, "-j", "1", f"--root={module_root}",
                    "-DautoImplicit=false", "-DwarningAsError=true"]
            if emit:
                args += ["-o", target]
            args.append(source)
            print(f"Lean: {name}", flush=True)
            result = command(args, output / f"lean-{name}.json", env=env,
                             expect_success=expect_success, timeout=900)
            if expect_success and emit and not target.is_file():
                raise RuntimeError(f"compiler did not emit {name}")
            return result

        for module, source in zip(MODULES, sources):
            compile_file(source, module)
        compile_file(generated, "Receipts")
        audit = output / "Audit.lean"
        audit.write_text(audit_source([*MODULES, "Receipts"], print_contracts=True))
        result = compile_file(audit, "Audit", emit=False)
        report["compiled_modules"], declaration_axioms = parse_audit(result.stdout, [*MODULES, "Receipts"])
        write_json(output / "declaration-axioms.json", declaration_axioms)
        report["allowed_axioms"] = sorted(ALLOWED_AXIOMS)

        # Three known-false claims must fail for the intended logical reason.
        false_source = output / "FalseClaims.lean"
        false_source.write_text('''import GoldenNormality
example : GoldenNormality.checkPrefix 10 7 = true := by decide
example : GoldenNormality.Blocks.count [0, 1] [0, 0, 1] = 2 := by decide
example : GoldenNormality.BinaryAutomaton.classify [true, true] = some 1 := by decide
namespace Weakened
theorem root (B q : ℕ) (_hB : 0 < B) : q = q := rfl
end Weakened
example (B q : ℕ) (hB : 0 < B) :
    GoldenNormality.PrefixCertificate B q ↔
      Int.floor ((B : ℝ) * GoldenNormality.alpha) = (q : ℤ) := Weakened.root B q hB
''')
        false_result = compile_file(false_source, "FalseClaims", expect_success=False, emit=False)
        false_text = false_result.stdout + false_result.stderr
        if (false_result.returncode != 1
                or len(re.findall(r"(?i)decide.*proved", false_text)) != 3
                or "type mismatch" not in false_text.lower()):
            raise RuntimeError("false-claim controls did not fail for the expected decide reason")

        # This deliberately compiles with an added axiom; the actual compiled
        # audit, not the source hygiene check, must reject it.
        poison = output / "UntrustedAxiom.lean"
        poison.write_text("axiom injectedAssumption : False\ntheorem injectedClaim : False := injectedAssumption\n")
        compile_file(poison, "UntrustedAxiom")
        poison_audit = output / "AuditUntrusted.lean"
        poison_audit.write_text(audit_source(["UntrustedAxiom"]))
        rejected = compile_file(poison_audit, "AuditUntrusted", expect_success=False, emit=False)
        if rejected.returncode != 1 or "Local audited axiom" not in rejected.stdout + rejected.stderr:
            raise RuntimeError("compiled axiom injection was not rejected by the audit")
        inherited = output / "TransitiveAxiom.lean"
        inherited.write_text("import UntrustedAxiom\ntheorem inheritedPoison : False := injectedClaim\n")
        compile_file(inherited, "TransitiveAxiom")
        inherited_audit = output / "AuditTransitive.lean"
        inherited_audit.write_text(audit_source(["TransitiveAxiom"]))
        rejected = compile_file(inherited_audit, "AuditTransitive", expect_success=False, emit=False)
        if (rejected.returncode != 1
                or "Nonstandard transitive axiom" not in rejected.stdout + rejected.stderr):
            raise RuntimeError("transitive axiom injection was not rejected by the audit")
        report["lean_negative_controls"] = {
            "false_root": "rejected", "scattered_count": "rejected",
            "invalid_fibonacci_word": "rejected", "weakened_theorem_type": "rejected",
            "compiled_axiom_injection": "rejected", "transitive_axiom_injection": "rejected"}
        if source_hashes() != report["source_sha256"]:
            raise RuntimeError("repository sources changed during acceptance")
        if verify_submodule() != report["native"]["finite_math_kernels_revision"]:
            raise RuntimeError("native dependency changed during acceptance")
        _, final_revisions = dependency_paths(packages)
        if final_revisions != report["dependency_revisions"]:
            raise RuntimeError("proof dependency changed during acceptance")
        report["accepted"] = True
        report["scope"] = "universal Lean foundation and checked finite native receipts; no normality theorem"
    except Exception as error:
        report["error"] = str(error)
        raise
    finally:
        report["finished_utc"] = utc_now()
        report["artifact_sha256"] = {
            str(path.relative_to(output)): digest(path)
            for path in sorted(output.rglob("*")) if path.is_file()
            and path.name != "report.json" and path.suffix not in (".olean", ".private", ".server", ".ir")
            and path.name not in ("foundation", "automaton_probe")}
        write_json(output / "report.json", report)
    print(json.dumps({"accepted": report["accepted"], "compiled_modules": report["compiled_modules"],
                      "report": str(output / "report.json")}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="build/acceptance")
    args = parser.parse_args()
    run(args.output)
