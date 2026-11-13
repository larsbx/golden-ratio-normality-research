#!/usr/bin/env python3
"""Compile the actual Mojo producers, check receipts, and emit Lean obligations.

This command alone establishes finite differential evidence, not Lean acceptance.
tools/verify.py compiles the obligations and audits their compiled dependencies.
"""
import argparse
import json
import os
from pathlib import Path
import re
import sys

from acceptance_utils import (CONTRACT, ROOT, command, digest, locate_program,
                              verify_submodule, write_json)
sys.path.insert(0, str(ROOT))
from oracles.reference import check_record, check_automaton_record, word


def lean_list(values):
    return "[" + ", ".join(str(value).lower() for value in values) + "]"


def certificate_source(prefixes, automaton):
    lines = ["import GoldenNormality", "", "set_option maxRecDepth 10000",
             "set_option maxHeartbeats 4000000", "", "namespace GoldenNormality.Receipts"]
    for i, record in enumerate(prefixes):
        b, k = record["base"], record["width"]
        digits = [int(c) for c in record["digits"]]
        lines += [f"def word_{i} : List ℕ := {lean_list(digits)}"]
        value = 0
        for n in range(len(digits) + 1):
            lines += [f"theorem prefix_{i}_{n} : PrefixCertificate ({b}^{n}) {value} := by decide"]
            if n < len(digits):
                value = value * b + digits[n]
        for n, digit in enumerate(digits):
            lines += [f"theorem digit_{i}_{n} : digit {b} {n} = ({digit} : ℤ) := by",
                      f"  exact digit_of_certificates (by decide) prefix_{i}_{n} prefix_{i}_{n+1}"]
        conjunction = "True.intro"
        for n in reversed(range(len(digits))):
            conjunction = f"And.intro digit_{i}_{n} ({conjunction})"
        lines += [f"theorem digits_{i} : DigitsAt {b} 0 word_{i} := {conjunction}"]
        starts = max(0, len(digits) + 1 - k)
        for j, count in enumerate(record["counts"]):
            pattern = lean_list(word(b, k, j))
            discrepancy = abs((b ** k) * count - starts)
            lines += [f"theorem count_{i}_{j} : Blocks.count {pattern} word_{i} = {count} := by decide",
                      f"theorem actualCount_{i}_{j} : Blocks.enumeratedCount {pattern}",
                      f"    (actualDigits {b} 0 word_{i}.length) = {count} :=",
                      f"  certified_count_sound digits_{i} count_{i}_{j}",
                      f"theorem occurrence_{i}_{j} : occurrences {b} {k} {j} {starts} = {count} :=",
                      f"  certified_occurrences_sound (b := {b}) (value := {count})",
                      f"    (text := word_{i}) (pattern := {pattern})",
                      f"    (by decide) (by decide) (by decide) digits_{i} count_{i}_{j}",
                      f"theorem discrepancy_{i}_{j} :",
                      f"    Nat.dist ({b}^{k} * occurrences {b} {k} {j} {starts}) {starts} = {discrepancy} := by",
                      f"  rw [occurrence_{i}_{j}]",
                      f"  decide"]
        lines.append("")
    for i, record in enumerate(automaton):
        # This runs only after strict nonbinary-symbol rejection in the oracle.
        bits = lean_list([c == "1" for c in record["digits"]])
        q, d = record["value"], record["output"]
        lines += [f"def fibonacciWord_{i} : List Bool := {bits}",
                  f"theorem input_{i} : BinaryAutomaton.fibonacciSum fibonacciWord_{i} 2 = {q} := by decide",
                  f"theorem output_{i} : BinaryAutomaton.classify fibonacciWord_{i} = some {d} := by decide",
                  f"theorem predicate_{i} : BinaryAutomaton.binaryDifference {q} = ({d} : ℤ) := by",
                  f"  simpa only [input_{i}, Nat.cast_zero, Nat.cast_one] using BinaryAutomaton.classify_correct output_{i}"]
        if q and q & (q - 1) == 0:
            n = q.bit_length() - 1
            lines += [f"theorem powerDigit_{n} : digit 2 {n} = ({d} : ℤ) :=",
                      f"  BinaryAutomaton.power_input_digit input_{i} output_{i}"]
    lines += ["end GoldenNormality.Receipts", ""]
    return "\n".join(lines)


def run(output):
    output = Path(output)
    output = (output if output.is_absolute() else ROOT / output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    submodule = verify_submodule()
    mojo = locate_program("MOJO_BIN", "mojo", ROOT / "kernel/.pixi/envs/default/bin/mojo")
    env = os.environ.copy()
    # Supported SDK controls; set before even the version query. Calling the
    # installed binaries directly also avoids the package's activation hook.
    env["MODULAR_TELEMETRY_ENABLED"] = "false"
    env["MODULAR_CRASH_REPORTING_ENABLED"] = "false"
    prefix = Path(mojo).parent.parent
    if (prefix / "share/max").is_dir():
        env.setdefault("MODULAR_HOME", str(prefix / "share/max"))
    version = command([mojo, "--version"], output / "mojo-version.json", env=env, timeout=30)
    detected = re.search(r"(?m)^Mojo (\S+) ", version.stdout + version.stderr)
    if detected is None or detected.group(1) != CONTRACT["mojo_version"]:
        raise RuntimeError("Mojo version differs from pinned contract")
    include = ["-I", ROOT / "kernel", "-I", ROOT / "vendor/finite-math-kernels/kernel"]
    if (prefix / "lib/mojo").is_dir():
        include = ["-I", prefix / "lib/mojo", *include]
    executables = {}
    for name in ("foundation", "automaton_probe"):
        exe = output / name
        command([mojo, "build", *include, ROOT / f"kernel/{name}.mojo", "-o", exe],
                output / f"build-{name}.json", env=env)
        executables[name] = exe
    prefixes = []
    for index, (b, n, k) in enumerate(CONTRACT["prefix_cases"]):
        result = command([executables["foundation"], b, n, k], output / f"prefix-{index}.json", env=env)
        record = json.loads(result.stdout)
        check_record(record)
        if (record["base"], record["length"], record["width"]) != (b, n, k):
            raise RuntimeError("native receipt is not bound to requested case")
        prefixes.append(record)
    rejected = []
    bad_requests = [((1, 4, 1), "prefix outside"), ((11, 4, 1), "prefix outside"),
                    ((2, -1, 1), "prefix outside"), ((2, 4097, 1), "prefix outside"),
                    ((2, 4, 0), "block count outside"), ((2, 4, 5), "block count outside"),
                    (("x", 4, 1), "not convertible to integer"), ((2, 4), "usage: golden-normality")]
    for index, (args, diagnostic) in enumerate(bad_requests):
        result = command([executables["foundation"], *args], output / f"bad-native-{index}.json",
                         env=env, timeout=30, expect_success=False)
        if result.returncode != 1 or result.stdout.strip() or diagnostic not in result.stderr:
            raise RuntimeError(f"native invalid request was not rejected: {args}")
        rejected.append(list(args))
    result = command([executables["automaton_probe"]], output / "automaton.json", env=env)
    automaton = [json.loads(line) for line in result.stdout.splitlines()]
    if len(automaton) != CONTRACT["automaton_values"]:
        raise RuntimeError("unexpected automaton receipt count")
    for i, record in enumerate(automaton):
        check_automaton_record(record)
        if record["value"] != i:
            raise RuntimeError("automaton receipts must cover the exact requested input range")
    write_json(output / "receipts.json", {"prefixes": prefixes, "automaton": automaton})
    source = output / "Receipts.lean"
    source.write_text(certificate_source(prefixes, automaton))
    summary = {
        "scope": "finite native/oracle conformance; Lean obligations emitted, not yet compiled",
        "mojo_version": (version.stdout + version.stderr).strip(),
        "mojo_compiler_sha256": digest(mojo),
        "telemetry_environment": {
            "MODULAR_TELEMETRY_ENABLED": env["MODULAR_TELEMETRY_ENABLED"],
            "MODULAR_CRASH_REPORTING_ENABLED": env["MODULAR_CRASH_REPORTING_ENABLED"],
        },
        "finite_math_kernels_revision": submodule,
        "prefix_cases": [{"base": r["base"], "length": r["length"], "width": r["width"],
                          "windows": sum(r["counts"])} for r in prefixes],
        "automaton_values": len(automaton), "native_invalid_requests_rejected": rejected,
        "executables_sha256": {name: digest(exe) for name, exe in executables.items()},
        "receipts_sha256": digest(output / "receipts.json"),
        "lean_obligations_sha256": digest(source),
    }
    write_json(output / "summary.json", summary)
    return summary, source


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="build/native")
    args = parser.parse_args()
    summary, _ = run(args.output)
    print(json.dumps(summary, indent=2))
