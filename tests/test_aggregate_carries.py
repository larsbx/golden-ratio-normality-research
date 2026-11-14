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
                overlap = sum(t > 0 and d == 1 for t, d in zip(prefix, self.digits))
                mass = sum(max(t, 0) for t in prefix)
                support = [i for i, digit in enumerate(self.digits[:n]) if digit]
                zeros = len(support)
                omitted = sum(i + j + 1 >= n for i in support for j in support)
                pairs = sum(self.coefficients[:n])
                self.assertLessEqual(positive, mass)
                self.assertLessEqual(mass + 3 * overlap, pairs + max(self.carries[n], 0))
                self.assertEqual(pairs + omitted, zeros**2)
                for blocks in range(1, min(n, 16) + 1):
                    width, remainder = divmod(n, blocks)
                    if remainder == 0:
                        partition = sum(
                            sum(self.digits[i * width:(i + 1) * width]) *
                            sum(self.digits[:(blocks - i) * width])
                            for i in range(blocks)
                        )
                        self.assertLessEqual(pairs, partition)
                upper_zeros = sum(self.digits[n // 2:n])
                self.assertLessEqual(pairs + upper_zeros**2, zeros**2)
                if n % 4 == 0:
                    quarter = n // 4
                    second = sum(self.digits[quarter:2 * quarter])
                    fourth = sum(self.digits[3 * quarter:n])
                    self.assertLessEqual(upper_zeros**2 + 2 * second * fourth, omitted)
                self.assertLessEqual(n, 2 * positive + 4 * zeros + 1)
                if n >= 2:
                    self.assertLessEqual(n + 2 * omitted + 6 * overlap,
                                         2 * zeros**2 + 6 * zeros - 1)

    def test_constant_error_checkpoint_parameters(self):
        blocks, radius, threshold_root = 16_384, 128, 256
        numerator, denominator = 3_989, 5_000
        pi_numerator, pi_denominator = 31_416, 10_000
        self.assertEqual(radius**2, blocks)
        # Clear denominators in the margin K - c² (K + 1) π / 2.
        margin = (2 * blocks * denominator**2 * pi_denominator
                  - numerator**2 * (blocks + 1) * pi_numerator)
        self.assertGreater(margin, 0)
        self.assertGreaterEqual(margin * threshold_root,
                                12 * numerator * radius * denominator * pi_denominator)

    def test_root_checkpoint_certificate(self):
        scale, blocks, threshold_root = 10_000, 64, 256
        caps = [0] + [isqrt(scale**2 * i) + 1 for i in range(1, blocks + 1)]
        self.assertEqual(caps, sorted(caps))
        self.assertTrue(all(cap**2 >= scale**2 * i for i, cap in enumerate(caps)))
        budget = sum((caps[i + 1] - caps[i]) * caps[blocks - i]
                     for i in range(blocks))
        self.assertEqual((budget, caps[-1]), (5_063_329_433, 80_001))
        # Clear denominators for c = 397/500 and sqrt(n) >= 256.
        denominator = 500 * scale
        margin = blocks * denominator**2 - 2 * 397**2 * budget
        self.assertGreater(margin, 0)
        self.assertGreaterEqual(margin * threshold_root,
                                6 * 397 * caps[-1] * denominator)

    def test_shifted_aggregate_and_zero_gaps(self):
        for start in range(len(self.carries)):
            carry_mass = coefficient_mass = positive = overlap = 0
            gap = start > 0 and self.digits[start - 1] == 1
            for end in range(start, len(self.carries)):
                self.assertLessEqual(
                    carry_mass + max(self.carries[start], 0) + 3 * overlap,
                    coefficient_mass + max(self.carries[end], 0),
                )
                if gap:
                    self.assertLessEqual(end - start, 2 * positive + 3)
                if end < len(self.digits):
                    gap = gap and self.digits[end] == 0
                    overlap += self.digits[end] == 1 and self.carries[end] > 0
                carry_mass += max(self.carries[end], 0)
                coefficient_mass += self.coefficients[end]
                positive += self.carries[end] > 0

    def test_invalid_strengthenings(self):
        # Position 9 is the first positive carry on a complementary one.
        self.assertEqual((self.digits[9], self.carries[9], self.carries[10],
                          self.coefficients[9]), (1, 1, 3, 2))
        # At N=4 the two mixed pairs lie exactly on the cutoff and are omitted.
        self.assertEqual(self.digits[:4], [0, 1, 1, 0])
        self.assertEqual(sum(self.coefficients[:4]), 1)
        # At N=8, each new rectangle contributes one ordered pair.
        self.assertEqual((sum(self.digits[2:4]), sum(self.digits[6:8])), (1, 1))
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
