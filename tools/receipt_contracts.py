"""Independent exact-type obligations for finite occurrence receipts.

The expected words and counts come from the fixed research contract and the
sqrt/slice oracle, without reading native receipts or their Lean translator.
Each wrapper requires its named receipt to prove the full expected proposition.
Starts and absolute discrepancies are evaluated as closed expressions by Lean.
"""
import sys

from acceptance_utils import CONTRACT, ROOT

sys.path.insert(0, str(ROOT))
from oracles.reference import block_counts, prefix_value, word


def expected_names() -> set[str]:
    """Fully qualified wrapper names required by the compiled module audit."""
    return {
        f"GoldenNormality.ReceiptContracts.{kind}_{i}_{value}"
        for i, (base, _length, width) in enumerate(CONTRACT["prefix_cases"])
        for value in range(base ** width)
        for kind in ("occurrence", "discrepancy")
    }


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
    lines += ["end GoldenNormality.ReceiptContracts", ""]
    return "\n".join(lines)
