"""Independent checks of the modular phase residues of actual prefixes."""

import unittest
from collections import Counter

from oracles.reference import prefix_value


class DyadicModularTests(unittest.TestCase):
    @staticmethod
    def cyclotomic_remainder(length, numerator):
        modulus = 1 << length
        half = modulus // 2
        coefficients = Counter()
        for start in range(length):
            residue = (numerator << start) % modulus
            coefficients[residue % half] += 1 if residue < half else -1
        return {power: multiplicity for power, multiplicity in coefficients.items() if multiplicity}

    def test_exact_nonvanishing_at_every_residue(self):
        for length in range(3, 11):
            for numerator in range(1 << length):
                self.assertTrue(self.cyclotomic_remainder(length, numerator), (length, numerator))

    def test_actual_length_two_exception_for_all_odd_modes(self):
        numerator = prefix_value(2, 2)
        self.assertEqual(numerator, 2)
        for mode in range(-7, 8, 2):
            self.assertEqual(self.cyclotomic_remainder(2, mode * numerator), {})

    def test_doubling_residues_match_suffixes(self):
        for length in range(1, 97):
            modulus = 1 << length
            numerator = prefix_value(2, length)
            binary = f"{numerator:0{length}b}"
            for start in range(length):
                suffix = int(binary[start:] + "0" * start, 2)
                for mode in (-7, -1, 1, 3):
                    self.assertEqual(
                        (mode * numerator * 2**start) % modulus,
                        (mode * suffix) % modulus,
                    )

    def test_complete_frequency_collision_count(self):
        for length in range(1, 65):
            modulus = 1 << length
            numerator = prefix_value(2, length)
            residues = [(numerator << start) % modulus for start in range(length)]
            if numerator % 2:
                self.assertEqual(len(set(residues)), length)
                self.assertEqual(
                    sum(left == right for left in residues for right in residues), length,
                )

        for length in range(1, 7):
            modulus = 1 << length
            for numerator in range(1, modulus, 2):
                self.assertEqual(
                    {frequency * numerator % modulus for frequency in range(modulus)},
                    set(range(modulus)),
                )

    def test_balanced_digit_count_does_not_cancel_first_mode(self):
        length = 10
        modulus = 1 << length
        numerator = prefix_value(2, length)
        residues = [(numerator << start) % modulus for start in range(length)]
        self.assertEqual(sum(r < modulus // 2 for r in residues), length // 2)
        # In the polynomial representing the phase sum, reduce x^1024 to 1
        # and x^512 to -1. The latter is the minimal polynomial relation.
        reduced_at_zero = residues.count(0) - residues.count(modulus // 2)
        self.assertEqual(reduced_at_zero, 2)


if __name__ == "__main__":
    unittest.main()
