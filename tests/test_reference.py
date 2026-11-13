"""Adversarial controls for the independent finite-record checker.

These tests exercise the Python oracle and record boundary. They do not claim
native Mojo conformance, universal implementation refinement, or normality.
The main fixture is a fixed known prefix; its expected two-digit windows are
listed independently of the counting implementation.
"""

from copy import deepcopy
import unittest

from oracles.reference import (
    block_counts,
    check_automaton_record,
    check_record,
    encode,
    fibonacci_value,
    polynomial_certificate,
    prefix_value,
    word,
)


def decimal_fixture():
    counts = [0] * 100
    for pair in (61, 18, 80, 3, 33, 39, 98, 88, 87, 74, 49, 98, 89, 94, 48):
        counts[pair] += 1
    return {
        "schema": "golden-normality-prefix-v1",
        "base": 10,
        "length": 16,
        "scale": "10000000000000000",
        "value": "6180339887498948",
        "digits": "6180339887498948",
        "width": 2,
        "counts": counts,
    }


def binary_fixture():
    return {
        "schema": "golden-normality-prefix-v1",
        "base": 2,
        "length": 4,
        "scale": "16",
        "value": "9",
        "digits": "1001",
        "width": 2,
        "counts": [1, 1, 1, 0],
    }


class PrefixOracleTests(unittest.TestCase):
    def test_fixed_known_prefixes(self):
        for base, length, expected in (
            (10, 0, 0), (10, 1, 6), (10, 2, 61), (10, 3, 618),
            (10, 16, 6180339887498948), (2, 4, 9), (2, 8, 158),
        ):
            with self.subTest(base=base, length=length):
                self.assertEqual(prefix_value(base, length), expected)
                self.assertTrue(polynomial_certificate(base**length, expected))

    def test_neighbor_values_and_wrong_scales_fail(self):
        scale, value = 10000000000000000, 6180339887498948
        for changed_scale, changed_value in (
            (scale, value - 1), (scale, value + 1),
            (scale // 10, value), (scale * 10, value),
            (0, 0), (1, -1),
        ):
            with self.subTest(scale=changed_scale, value=changed_value):
                self.assertFalse(polynomial_certificate(changed_scale, changed_value))

    def test_prefix_metadata_requires_actual_integers(self):
        for base, length in ((True, 4), (2, False), (2.0, 4), (2, 4.0), (1, 4), (2, -1)):
            with self.subTest(base=base, length=length):
                with self.assertRaises(ValueError):
                    prefix_value(base, length)

    def test_word_retains_fixed_width_and_checks_capacity(self):
        self.assertEqual(word(10, 3, 7), [0, 0, 7])
        self.assertEqual(encode(10, [0, 0, 7]), 7)
        with self.assertRaises(ValueError):
            word(10, 2, 100)
        for digits in ([True], [1.0], [-1], [2]):
            with self.subTest(digits=digits):
                with self.assertRaises(ValueError):
                    encode(2, digits)


class PrefixRecordTests(unittest.TestCase):
    def assert_bad_field(self, field, value, fixture=None):
        record = deepcopy(decimal_fixture() if fixture is None else fixture)
        record[field] = value
        with self.assertRaises(ValueError):
            check_record(record)

    def test_fixed_valid_records(self):
        check_record(decimal_fixture())
        check_record(binary_fixture())

    def test_zero_length_prefix_is_explicit(self):
        record = binary_fixture()
        record.update(length=0, scale="1", value="0", digits="", counts=[0, 0, 0, 0])
        check_record(record)

    def test_schema_and_exact_key_set(self):
        for schema in ("golden-normality-prefix-v2", "", 1, True, None):
            with self.subTest(schema=schema):
                self.assert_bad_field("schema", schema)
        missing = decimal_fixture()
        del missing["value"]
        extra = decimal_fixture()
        extra["normality_proved"] = True
        for record in (missing, extra, [], None):
            with self.subTest(record_type=type(record).__name__):
                with self.assertRaises(ValueError):
                    check_record(record)

    def test_metadata_bool_int_confusion_and_resource_limits(self):
        for field in ("base", "length", "width"):
            for value in (True, False, 2.0, "2", None):
                with self.subTest(field=field, value=value):
                    self.assert_bad_field(field, value)
        for field, value in (
            ("base", 1), ("base", 11), ("length", -1), ("length", 4097),
            ("width", 0), ("width", 5),
        ):
            with self.subTest(field=field, value=value):
                self.assert_bad_field(field, value)

    def test_boolean_metadata_rejected_when_numeric_value_would_be_valid(self):
        empty = binary_fixture()
        empty.update(length=0, scale="1", value="0", digits="", counts=[0, 0, 0, 0])
        check_record(empty)
        self.assert_bad_field("length", False, empty)
        singles = binary_fixture()
        singles.update(width=1, counts=[2, 2])
        check_record(singles)
        self.assert_bad_field("width", True, singles)

    def test_decimal_integer_fields_are_canonical(self):
        for field in ("scale", "value"):
            original = decimal_fixture()[field]
            for value in (
                "0" + original, "+" + original, "-" + original,
                " " + original, original + " ", "", "00", "1_000", "１",
                int(original), True, False,
            ):
                with self.subTest(field=field, value=value):
                    self.assert_bad_field(field, value)

    def test_changed_root_candidate_scale_base_and_length(self):
        for field, value in (
            ("value", "6180339887498947"), ("value", "6180339887498949"),
            ("scale", "1000000000000000"), ("scale", "100000000000000000"),
            ("base", 9), ("length", 15), ("length", 17),
        ):
            with self.subTest(field=field, value=value):
                self.assert_bad_field(field, value)

    def test_changed_digit_word_and_alphabet(self):
        original = decimal_fixture()["digits"]
        for text in ("7" + original[1:], original[:-1], original + "0", "0" + original[1:],
                     original[:-1] + "x", original[:-1] + "８", list(original), None):
            with self.subTest(text=text):
                self.assert_bad_field("digits", text)
        self.assert_bad_field("digits", "2001", binary_fixture())
        self.assert_bad_field("digits", "1101", binary_fixture())

    def test_changed_counts_and_correct_total_wrong_distribution(self):
        original = decimal_fixture()["counts"]
        extra = original.copy()
        extra[98] += 1
        redistributed = original.copy()
        redistributed[98] -= 1
        redistributed[0] += 1
        self.assertEqual(sum(redistributed), sum(original))
        for counts in (extra, redistributed, original[:-1], original + [0]):
            with self.subTest(count_length=len(counts)):
                self.assert_bad_field("counts", counts)

    def test_count_encoding_rejects_bool_float_negative_and_nonlist(self):
        for value in (True, False, 0.0, -1, "0", None):
            counts = decimal_fixture()["counts"]
            counts[0] = value
            with self.subTest(value=value):
                self.assert_bad_field("counts", counts)
        for counts in (tuple(decimal_fixture()["counts"]), {}, None):
            with self.subTest(count_type=type(counts).__name__):
                self.assert_bad_field("counts", counts)
        numeric_alias = decimal_fixture()["counts"]
        self.assertEqual(numeric_alias[61], 1)
        numeric_alias[61] = True
        self.assert_bad_field("counts", numeric_alias)


class ContiguousWindowTests(unittest.TestCase):
    def test_scattered_pairs_are_not_contiguous_windows(self):
        # Two scattered 01 pairs, but only one consecutive 01 block.
        self.assertEqual(block_counts([0, 0, 1], 2, 2), [1, 1, 0, 0])

    def test_overlapping_windows_are_retained(self):
        self.assertEqual(block_counts([0, 0, 0], 2, 2), [2, 0, 0, 0])

    def test_short_word_empty_word_and_empty_block(self):
        self.assertEqual(block_counts([1], 2, 2), [0, 0, 0, 0])
        self.assertEqual(block_counts([], 2, 1), [0, 0])
        with self.assertRaises(ValueError):
            block_counts([0, 1], 2, 0)

    def test_chunk_boundary_window_cannot_be_dropped(self):
        left = block_counts([0], 2, 2)
        right = block_counts([1], 2, 2)
        full = block_counts([0, 1], 2, 2)
        self.assertEqual(left[1] + right[1], 0)
        self.assertEqual(full[1], 1)

    def test_length_three_boundaries_and_leading_zero_block(self):
        full = block_counts([9, 0, 1, 2, 8], 10, 3)
        left = block_counts([9, 0], 10, 3)
        right = block_counts([1, 2, 8], 10, 3)
        self.assertEqual({i: n for i, n in enumerate(full) if n}, {12: 1, 128: 1, 901: 1})
        self.assertEqual(sum(full) - sum(left) - sum(right), 2)


class FibonacciRecordTests(unittest.TestCase):
    def test_fixed_known_fibonacci_inputs_and_outputs(self):
        for value, digits, output in (
            (0, "0", 0), (1, "1", 1), (2, "10", 0), (3, "100", 1),
            (4, "101", 0), (5, "1000", 0), (6, "1001", 1),
            (8, "10000", 1), (16, "100100", 1), (32, "1010100", 1),
        ):
            with self.subTest(value=value):
                self.assertEqual(fibonacci_value([int(c) for c in digits]), value)
                check_automaton_record({"value": value, "digits": digits, "output": output})

    def test_fibonacci_zero_padding_is_allowed(self):
        check_automaton_record({"value": 16, "digits": "000100100", "output": 1})
        check_automaton_record({"value": 0, "digits": "000", "output": 0})

    def test_changed_input_output_and_representation(self):
        baseline = {"value": 16, "digits": "100100", "output": 1}
        check_automaton_record(baseline)
        for field, value in (("value", 17), ("output", 0), ("digits", "100101")):
            record = {**baseline, field: value}
            with self.subTest(field=field):
                with self.assertRaises(ValueError):
                    check_automaton_record(record)

    def test_inadmissible_consecutive_ones_are_rejected_even_at_right_value(self):
        self.assertEqual(fibonacci_value([1, 1]), 3)
        with self.assertRaises(ValueError):
            check_automaton_record({"value": 3, "digits": "11", "output": 1})

    def test_automaton_metadata_and_word_encoding(self):
        baseline = {"value": 16, "digits": "100100", "output": 1}
        for field, values in (
            ("value", (True, False, 16.0, "16", -1)),
            ("output", (True, False, 1.0, "1", -1, 2)),
            ("digits", ("", "10200", "１０", [1, 0], None)),
        ):
            for value in values:
                with self.subTest(field=field, value=value):
                    with self.assertRaises(ValueError):
                        check_automaton_record({**baseline, field: value})
        for record in ({"value": 16, "digits": "100100"}, {**baseline, "schema": 1}, [], None):
            with self.subTest(record_type=type(record).__name__):
                with self.assertRaises(ValueError):
                    check_automaton_record(record)

    def test_boolean_automaton_input_rejected_at_matching_numeric_value(self):
        for value, digits, output in ((False, "0", 0), (True, "1", 1)):
            check_automaton_record({"value": int(value), "digits": digits, "output": output})
            with self.subTest(value=value):
                with self.assertRaises(ValueError):
                    check_automaton_record({"value": value, "digits": digits, "output": output})


if __name__ == "__main__":
    unittest.main()
