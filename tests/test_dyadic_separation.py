"""Exact finite controls for actual binary returns and repeated blocks."""

import unittest

from oracles.reference import polynomial_certificate, prefix_value


class DyadicSeparationTests(unittest.TestCase):
    def test_overlapping_nonconstant_repeat(self):
        digits = f"{prefix_value(2, 20):020b}"
        self.assertEqual(digits[10:16], "110111")
        self.assertEqual(digits[14:20], "110111")
        self.assertLess(14 - 10, len(digits[10:16]))

    def test_repeated_block_width_bound(self):
        end = 192
        digits = f"{prefix_value(2, end):0{end}b}"
        floors = [prefix_value(2, n) for n in range(end)]
        for n, floor in enumerate(floors):
            self.assertTrue(polynomial_certificate(1 << n, floor))
        for m in range(1, end):
            for n in range(m):
                q = (1 << m) - (1 << n)
                p = floors[m] - floors[n]
                self.assertNotEqual(p * p + p * q - q * q, 0)
                k = 0
                while m + k < end and digits[m + k] == digits[n + k]:
                    k += 1
                # Both sides of 2**k - 1 < sqrt(5) * q are nonnegative.
                self.assertLess(((1 << k) - 1) ** 2, 5 * q * q)
                self.assertLessEqual(k, m + 1)


if __name__ == "__main__":
    unittest.main()
