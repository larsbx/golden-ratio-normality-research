"""Exact finite controls using integer square roots and direct floor products."""

from math import isqrt
import unittest


class AggregateCarryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        end = 256
        floors = []
        for n in range(end + 1):
            scale = 1 << n
            original = (isqrt(5 * scale**2) - scale) // 2
            assert original**2 + scale * original < scale**2
            assert (original + 1)**2 + scale * (original + 1) > scale**2
            floors.append(scale - 1 - original)
        cls.digits = [b - 2 * a for a, b in zip(floors, floors[1:])]
        cls.coefficients = []
        cls.carries = []
        for n, floor in enumerate(floors):
            cls.carries.append(3 * floor - (1 << n) - sum(
                cls.digits[i] * floors[n - 1 - i] for i in range(n)
            ))
            cls.coefficients.append(sum(
                cls.digits[i] * cls.digits[n - 1 - i] for i in range(n)
            ))

    def test_prefix_bounds(self):
        for n in range(len(self.carries)):
            with self.subTest(n=n):
                prefix = self.carries[:n]
                positive = sum(t > 0 for t in prefix)
                mass = sum(max(t, 0) for t in prefix)
                zeros = sum(self.digits[:n])
                pairs = sum(self.coefficients[:n])
                self.assertLessEqual(positive, mass)
                self.assertLessEqual(mass, pairs + max(self.carries[n], 0))
                upper_zeros = sum(self.digits[n // 2:n])
                self.assertLessEqual(pairs + upper_zeros**2, zeros**2)
                self.assertLessEqual(n, 2 * positive + 4 * zeros + 1)
                if n >= 2:
                    self.assertLessEqual(n + 2 * upper_zeros**2,
                                         2 * zeros**2 + 6 * zeros - 1)

    def test_shifted_aggregate_and_zero_gaps(self):
        for start in range(len(self.carries)):
            carry_mass = coefficient_mass = positive = 0
            gap = start > 0 and self.digits[start - 1] == 1
            for end in range(start, len(self.carries)):
                self.assertLessEqual(
                    carry_mass + max(self.carries[start], 0),
                    coefficient_mass + max(self.carries[end], 0),
                )
                if gap:
                    self.assertLessEqual(end - start, 2 * positive + 3)
                if end < len(self.digits):
                    gap = gap and self.digits[end] == 0
                carry_mass += max(self.carries[end], 0)
                coefficient_mass += self.coefficients[end]
                positive += self.carries[end] > 0

    def test_invalid_strengthenings(self):
        # Both mixed pairs survive at N=5, but the upper-half square does not.
        self.assertEqual(self.digits[:5], [0, 1, 1, 0, 0])
        self.assertEqual(sum(self.coefficients[:5]), 3)
        # The actual interval [13,14) refutes deleting the right boundary.
        self.assertEqual((self.carries[13], self.coefficients[13], self.carries[14]),
                         (1, 0, 2))
        # Positive coefficient and two following zero digits do not suffice.
        self.assertEqual((self.coefficients[5], self.digits[5:7], self.carries[5]),
                         (1, [0, 0], 0))
        # The gap [3,7) is tight for a zero-loss estimate.
        self.assertEqual(self.digits[2:7], [1, 0, 0, 0, 0])
        self.assertEqual(self.carries[3:7], [1, 1, 0, -1])
        # The origin prefix [0,8) has fewer than half positive carries.
        self.assertEqual(sum(t > 0 for t in self.carries[:8]), 2)
