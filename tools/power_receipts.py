"""Translate checked native power-orbit witnesses into closed Lean obligations."""
from oracles.reference import word


def lean_list(values):
    return "[" + ", ".join(str(value).lower() for value in values) + "]"


def certificate_lines(records):
    lines = []
    for i, record in enumerate(records):
        start, length, width = record["start"], record["length"], record["width"]
        digits = [int(c) for c in record["digits"]]
        lines.append(f"def powerWord_{i} : List ℕ := {lean_list(digits)}")
        for offset, entry in enumerate(record["inputs"]):
            position = start + offset
            bits = lean_list([c == "1" for c in entry["fibonacci_digits"]])
            output = entry["output"]
            lines += [
                f"def powerInput_{i}_{offset} : List Bool := {bits}",
                f"theorem powerValue_{i}_{offset} :",
                f"    BinaryAutomaton.fibonacciSum powerInput_{i}_{offset} 2 = 2^{position} := by decide",
                f"theorem powerOutput_{i}_{offset} :",
                f"    BinaryAutomaton.classify powerInput_{i}_{offset} = some {output} := by decide",
                f"theorem powerDigit_{i}_{offset} : digit 2 {position} = ({output} : ℤ) :=",
                f"  BinaryAutomaton.power_input_digit powerValue_{i}_{offset} powerOutput_{i}_{offset}",
            ]
        inputs = "[" + ", ".join(f"powerInput_{i}_{n}" for n in range(length)) + "]"
        proof = "True.intro"
        for offset in reversed(range(length)):
            proof = f"And.intro powerValue_{i}_{offset} (And.intro powerOutput_{i}_{offset} ({proof}))"
        lines += [
            f"def powerInputs_{i} : List (List Bool) := {inputs}",
            f"theorem powerBinding_{i} :",
            f"    BinaryAutomaton.PowerOrbitAt {start} powerInputs_{i} powerWord_{i} := {proof}",
            f"theorem powerDigits_{i} : DigitsAt 2 {start} powerWord_{i} :=",
            f"  BinaryAutomaton.powerOrbitAt_digitsAt powerBinding_{i}",
            f"theorem powerCanonical_{i} :",
            f"    powerWord_{i} = BinaryAutomaton.powerDigits {start} {length} :=",
            f"  BinaryAutomaton.powerOrbitAt_eq_powerDigits powerBinding_{i}",
        ]
        starts = max(0, length + 1 - width)
        for value, count in enumerate(record["counts"]):
            pattern = lean_list(word(2, width, value))
            lines += [
                f"theorem powerCount_{i}_{value} : Blocks.count {pattern} powerWord_{i} = {count} := by decide",
                f"theorem powerActualCount_{i}_{value} :",
                f"    Blocks.enumeratedCount {pattern} (actualDigits 2 {start} {length}) = {count} :=",
                f"  certified_count_sound powerDigits_{i} powerCount_{i}_{value}",
                f"theorem powerCanonicalCount_{i}_{value} :",
                f"    Blocks.count {pattern} (BinaryAutomaton.powerDigits {start} {length}) = {count} := by",
                f"  rw [← powerCanonical_{i}]",
                f"  exact powerCount_{i}_{value}",
            ]
            if start == 0:
                discrepancy = abs(2 ** width * count - starts)
                lines += [
                    f"theorem powerOccurrence_{i}_{value} : occurrences 2 {width} {value} {starts} = {count} :=",
                    f"  certified_occurrences_sound (b := 2) (value := {count})",
                    f"    (text := powerWord_{i}) (pattern := {pattern})",
                    f"    (by decide) (by decide) (by decide) powerDigits_{i} powerCount_{i}_{value}",
                    f"theorem powerDiscrepancy_{i}_{value} :",
                    f"    Nat.dist (2^{width} * occurrences 2 {width} {value} {starts}) {starts} = {discrepancy} := by",
                    f"  rw [powerOccurrence_{i}_{value}]",
                    f"  decide",
                ]
        lines.append("")
    return lines
