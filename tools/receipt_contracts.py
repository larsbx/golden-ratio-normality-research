"""Independent exact-type obligations for finite occurrence receipts.

The expected words and counts come from the fixed research contract and the
sqrt/slice oracle, without reading native receipts or their Lean translator.
Each wrapper requires its named receipt to prove the full expected proposition.
Starts and absolute discrepancies are evaluated as closed expressions by Lean.
"""
import sys

from acceptance_utils import CONTRACT, ROOT, validated_intervals

sys.path.insert(0, str(ROOT))
from oracles.reference import block_counts, prefix_value, word
import power_receipt_contracts


def expected_names() -> set[str]:
    """Fully qualified wrapper names required by the compiled module audit."""
    names = {
        f"GoldenNormality.ReceiptContracts.{kind}_{i}_{value}"
        for i, (base, _length, width) in enumerate(CONTRACT["prefix_cases"])
        for value in range(base ** width)
        for kind in ("occurrence", "discrepancy")
    }
    names.update(f"GoldenNormality.ReceiptContracts.interval_{i}_{value}"
                 for i, case in enumerate(validated_intervals())
                 for value in range(case["base"] ** case["width"]))
    names.update(power_receipt_contracts.expected_names())
    return names


def certificate_source() -> str:
    """Generate ReceiptContracts.lean from contract cases and the oracle only."""
    lines = ["import GoldenNormality", "import Receipts", "",
             "namespace GoldenNormality.ReceiptContracts", ""]
    for i, (base, length, width) in enumerate(CONTRACT["prefix_cases"]):
        digits = word(base, length, prefix_value(base, length))
        counts = block_counts(digits, base, width)
        starts = f"({length} + 1 - {width})"
        scale = f"{base}^{width}"
        for value, count in enumerate(counts):
            occurrence = f"occurrences {base} {width} {value} {starts}"
            lines += [
                f"theorem occurrence_{i}_{value} : {occurrence} = {count} :=",
                f"  GoldenNormality.Receipts.occurrence_{i}_{value}",
                f"theorem discrepancy_{i}_{value} :",
                f"    Nat.dist ({scale} * {occurrence}) {starts} =",
                f"      Nat.dist ({scale} * {count}) {starts} :=",
                f"  GoldenNormality.Receipts.discrepancy_{i}_{value}",
            ]
        lines.append("")
    for i, case in enumerate(validated_intervals()):
        b, k, tolerance = case["base"], case["width"], case["tolerance"]
        left = f"({case['lower_length']} + 1 - {k})"
        right = f"({case['upper_length']} + 1 - {k})"
        for value in range(b ** k):
            lines += [f"theorem interval_{i}_{value} (N : ℕ) (hLN : {left} ≤ N) (hNR : N ≤ {right}) :",
                      f"    Nat.dist ({b}^{k} * occurrences {b} {k} {value} N) N * {tolerance} ≤ N :=",
                      f"  GoldenNormality.Receipts.interval_{i}_{value} N hLN hNR"]
        lines.append("")
    lines += power_receipt_contracts.certificate_lines()
    lines += ["end GoldenNormality.ReceiptContracts", ""]
    return "\n".join(lines)
