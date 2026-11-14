"""Independent expected types for every finite power-orbit theorem.

Only the fixed contract and root/slice oracle supply expected exponents, digits,
counts, and complete starts. No native record or receipt translator is read.
"""
from acceptance_utils import validated_power_orbits
from oracles.reference import block_counts, prefix_value, word


def expected_names():
    names = set()
    for i, case in enumerate(validated_power_orbits()):
        for offset in range(case["length"]):
            names.update(f"GoldenNormality.ReceiptContracts.{kind}_{i}_{offset}"
                         for kind in ("powerValue", "powerOutput", "powerDigit"))
        names.update(f"GoldenNormality.ReceiptContracts.{kind}_{i}"
                     for kind in ("powerBinding", "powerDigits", "powerCanonical"))
        for value in range(2 ** case["width"]):
            kinds = ["powerCount", "powerActualCount", "powerCanonicalCount"]
            if case["start"] == 0:
                kinds += ["powerOccurrence", "powerDiscrepancy"]
            names.update(f"GoldenNormality.ReceiptContracts.{kind}_{i}_{value}" for kind in kinds)
    return names


def certificate_lines():
    lines = []

    def check(name, proposition):
        lines.extend([f"theorem {name} : {proposition} :=",
                      f"  GoldenNormality.Receipts.{name}"])

    for i, case in enumerate(validated_power_orbits()):
        start, length, width = case["start"], case["length"], case["width"]
        total = start + length
        digits = word(2, total, prefix_value(2, total))[start:]
        counts = block_counts(digits, 2, width)
        native_word = f"GoldenNormality.Receipts.powerWord_{i}"
        for offset, output in enumerate(digits):
            position = start + offset
            input_word = f"GoldenNormality.Receipts.powerInput_{i}_{offset}"
            check(f"powerValue_{i}_{offset}",
                  f"BinaryAutomaton.fibonacciSum {input_word} 2 = 2^{position}")
            check(f"powerOutput_{i}_{offset}",
                  f"BinaryAutomaton.classify {input_word} = some {output}")
            check(f"powerDigit_{i}_{offset}", f"digit 2 {position} = ({output} : ℤ)")
        check(f"powerBinding_{i}",
              f"BinaryAutomaton.PowerOrbitAt {start} GoldenNormality.Receipts.powerInputs_{i} {native_word}")
        check(f"powerDigits_{i}", f"DigitsAt 2 {start} {native_word}")
        check(f"powerCanonical_{i}", f"{native_word} = BinaryAutomaton.powerDigits {start} {length}")
        starts = f"({length} + 1 - {width})"
        for value, count in enumerate(counts):
            pattern = "[" + ", ".join(map(str, word(2, width, value))) + "]"
            check(f"powerCount_{i}_{value}", f"Blocks.count {pattern} {native_word} = {count}")
            check(f"powerActualCount_{i}_{value}",
                  f"Blocks.enumeratedCount {pattern} (actualDigits 2 {start} {length}) = {count}")
            check(f"powerCanonicalCount_{i}_{value}",
                  f"Blocks.count {pattern} (BinaryAutomaton.powerDigits {start} {length}) = {count}")
            if start == 0:
                occurrence = f"occurrences 2 {width} {value} {starts}"
                check(f"powerOccurrence_{i}_{value}", f"{occurrence} = {count}")
                check(f"powerDiscrepancy_{i}_{value}",
                      f"Nat.dist (2^{width} * {occurrence}) {starts} = Nat.dist (2^{width} * {count}) {starts}")
        lines.append("")
    return lines
