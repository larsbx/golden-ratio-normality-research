"""Adversarial finite controls for the actual power-orbit record boundary.

The fixed eight-digit fixture includes overlapping 111 blocks and the leading
zero block 001. Its Fibonacci words are explicit data, not another encoder.
Native production and Lean acceptance are separate required gate stages.
"""

from copy import deepcopy
import unittest
from unittest.mock import patch

from oracles.power_orbit import check_power_orbit_record
from oracles.reference import block_counts, check_automaton_record, fibonacci_value


def orbit_fixture():
    entries = [
        (0, "1", "1", 1),
        (1, "2", "10", 0),
        (2, "4", "101", 0),
        (3, "8", "10000", 1),
        (4, "16", "100100", 1),
        (5, "32", "1010100", 1),
        (6, "64", "100010001", 1),
        (7, "128", "1010001000", 0),
    ]
    return {
        "schema": "golden-normality-power-orbit-v1",
        "base": 2,
        "start": 0,
        "length": 8,
        "width": 3,
        "digits": "10011110",
        "counts": [0, 1, 0, 1, 1, 0, 1, 2],
        "inputs": [dict(zip(("exponent", "value", "fibonacci_digits", "output"), entry))
                   for entry in entries],
    }


def sliced_fixture(start, length, width, counts):
    record = orbit_fixture()
    record.update(start=start, length=length, width=width, counts=counts,
                  digits=record["digits"][start:start + length],
                  inputs=record["inputs"][start:start + length])
    return record


class PowerOrbitTests(unittest.TestCase):
    def test_known_power_orbit_and_overlapping_counts(self):
        record = orbit_fixture()
        check_power_orbit_record(record)
        self.assertEqual(record["counts"][7], 2)
        self.assertEqual(record["counts"][1], 1)

    def test_empty_short_complete_and_nonzero_start_segments(self):
        records = [
            sliced_fixture(0, 0, 3, [0] * 8),
            sliced_fixture(0, 1, 3, [0] * 8),
            sliced_fixture(0, 3, 3, [0, 0, 0, 0, 1, 0, 0, 0]),
            sliced_fixture(2, 3, 2, [0, 1, 0, 1]),
            sliced_fixture(4096, 0, 3, [0] * 8),
        ]
        for record in records:
            with self.subTest(start=record["start"], length=record["length"]):
                check_power_orbit_record(record)
        self.assertEqual(records[3]["digits"], "011")

    def test_power_beyond_unsigned_machine_integer(self):
        record = {
            "schema": "golden-normality-power-orbit-v1",
            "base": 2, "start": 64, "length": 1, "width": 1,
            "digits": "1", "counts": [0, 1],
            "inputs": [{
                "exponent": 64,
                "value": "18446744073709551616",
                "fibonacci_digits":
                    "10100101000100000101000100010010001001000000001001000100100010101000100000101000101000010000",
                "output": 1,
            }],
        }
        self.assertGreater(int(record["inputs"][0]["value"]), 2**64 - 1)
        check_power_orbit_record(record)

    def test_wrong_power_rejected_even_with_valid_classifier_record(self):
        # q=3 has a valid word and the same output as q=1, but is not 2^0.
        entry = {"exponent": 0, "value": "3", "fibonacci_digits": "100", "output": 1}
        check_automaton_record({"value": 3, "digits": "100", "output": 1})
        record = orbit_fixture()
        record["inputs"][0] = entry
        with self.assertRaisesRegex(ValueError, r"not 2\^exponent"):
            check_power_orbit_record(record)

    def test_reordered_shifted_missing_and_duplicated_exponents(self):
        reordered = orbit_fixture()
        reordered["inputs"][0], reordered["inputs"][1] = reordered["inputs"][1], reordered["inputs"][0]
        shifted = orbit_fixture()
        for entry in shifted["inputs"]:
            entry["exponent"] += 1
        missing = orbit_fixture()
        missing["inputs"].pop(3)
        duplicated = orbit_fixture()
        duplicated["inputs"][4] = deepcopy(duplicated["inputs"][3])
        extra = orbit_fixture()
        extra["inputs"].append(deepcopy(extra["inputs"][-1]))
        for record in (reordered, shifted, missing, duplicated, extra):
            with self.subTest(inputs=record["inputs"]):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_changed_source_start_and_length(self):
        for key, value in (("start", 1), ("start", 17), ("length", 7), ("length", 9)):
            record = orbit_fixture()
            record[key] = value
            with self.subTest(key=key, value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_exact_top_level_schema_and_keys(self):
        for schema in ("golden-normality-power-orbit-v2", "", 1, True, None):
            record = orbit_fixture()
            record["schema"] = schema
            with self.subTest(schema=schema):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)
        missing = orbit_fixture()
        del missing["start"]
        extra = orbit_fixture()
        extra["normality_proved"] = True
        for record in (missing, extra, [], None):
            with self.subTest(record=record):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_metadata_requires_integers_and_bounded_resources(self):
        for key in ("base", "start", "length", "width"):
            for value in (True, False, 2.0, "2", None):
                record = orbit_fixture()
                record[key] = value
                with self.subTest(key=key, value=value):
                    with self.assertRaises(ValueError):
                        check_power_orbit_record(record)
        for key, value in (("base", 1), ("base", 3), ("start", -1), ("start", 4097),
                           ("start", 4096), ("length", -1), ("length", 257),
                           ("width", 0), ("width", 5)):
            record = orbit_fixture()
            record[key] = value
            with self.subTest(key=key, value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_input_sequence_and_exact_entry_keys(self):
        for inputs in ((), {}, None, ""):
            record = orbit_fixture()
            record["inputs"] = inputs
            with self.subTest(inputs=inputs):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)
        missing = orbit_fixture()["inputs"][0]
        del missing["exponent"]
        extra = {**orbit_fixture()["inputs"][0], "accepted": True}
        for entry in (missing, extra, [], None):
            record = orbit_fixture()
            record["inputs"][0] = entry
            with self.subTest(entry=entry):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_exponent_rejects_boolean_and_numeric_aliases(self):
        for value in (False, True, 0.0, "0", -1, None):
            record = orbit_fixture()
            record["inputs"][0]["exponent"] = value
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_power_values_are_canonical_ascii_decimal_strings(self):
        for value in ("01", "+1", "-1", " 1", "1 ", "", "00", "1_0", "１", "١",
                      1, 1.0, True, False, None):
            record = orbit_fixture()
            record["inputs"][0]["value"] = value
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_leading_zero_fibonacci_representations_remain_valid(self):
        record = orbit_fixture()
        for entry in record["inputs"]:
            entry["fibonacci_digits"] = "000" + entry["fibonacci_digits"]
        check_power_orbit_record(record)

    def test_fibonacci_budget_bounds_otherwise_valid_zero_padding(self):
        record = orbit_fixture()
        record["inputs"][0]["fibonacci_digits"] = "0" * 9999 + "1"
        check_power_orbit_record(record)
        record["inputs"][0]["fibonacci_digits"] = "0" + record["inputs"][0]["fibonacci_digits"]
        with patch("oracles.power_orbit.check_automaton_record") as classifier:
            with self.assertRaisesRegex(ValueError, "Fibonacci word resource contract"):
                check_power_orbit_record(record)
            classifier.assert_not_called()

    def test_fibonacci_syntax_value_and_admissibility(self):
        for value in ("", "2", "１", "10", "11", [1], True, None):
            record = orbit_fixture()
            record["inputs"][0]["fibonacci_digits"] = value
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)
        # 5+3=8 is the right power, but the adjacent ones are inadmissible.
        self.assertEqual(fibonacci_value([1, 1, 0, 0]), 8)
        record = orbit_fixture()
        record["inputs"][3]["fibonacci_digits"] = "1100"
        with self.assertRaisesRegex(ValueError, "Fibonacci word"):
            check_power_orbit_record(record)

    def test_wrong_output_and_boolean_numeric_alias_are_rejected(self):
        for output in (0, 2, -1, True, False, 1.0, "1", None):
            record = orbit_fixture()
            record["inputs"][0]["output"] = output
            with self.subTest(output=output):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_digit_concatenation_and_binary_word_types(self):
        for text in ("00011110", "1001111", "100111100", "10011112", "１００１１１１０",
                     [1, 0, 0, 1, 1, 1, 1, 0], None):
            record = orbit_fixture()
            record["digits"] = text
            with self.subTest(text=text):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)

    def test_root_segment_check_is_independent_of_classifier_check(self):
        record = orbit_fixture()
        record["inputs"][0]["output"] = 0
        record["digits"] = "00011110"
        record["counts"] = block_counts([int(c) for c in record["digits"]], 2, 3)
        # Removing the classifier check must not remove the independent source binding.
        with patch("oracles.power_orbit.check_automaton_record"):
            with self.assertRaisesRegex(ValueError, "actual digit segment"):
                check_power_orbit_record(record)

    def test_count_redistribution_cannot_hide_behind_correct_total(self):
        record = orbit_fixture()
        record["counts"][7] -= 1
        record["counts"][0] += 1
        self.assertEqual(sum(record["counts"]), 6)
        with self.assertRaisesRegex(ValueError, "contiguous counts"):
            check_power_orbit_record(record)

    def test_count_encoding_and_capacity(self):
        for value in (True, False, 0.0, -1, "0", None):
            record = orbit_fixture()
            record["counts"][0] = value
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)
        for counts in ([0] * 7, [0] * 9, tuple(orbit_fixture()["counts"]), {}, None):
            record = orbit_fixture()
            record["counts"] = counts
            with self.subTest(counts=counts):
                with self.assertRaises(ValueError):
                    check_power_orbit_record(record)


if __name__ == "__main__":
    unittest.main()
