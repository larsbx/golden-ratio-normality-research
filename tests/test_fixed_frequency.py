"""Exact prefix and outward-rounded half-angle checks for the first mode."""

from math import isqrt
import unittest

from oracles.reference import polynomial_certificate, prefix_value


SCALE = 10**32


def sqrt_half_box(lower, upper):
    """Enclose sqrt(x/2) when lower <= SCALE*x <= upper."""
    lo = isqrt(SCALE * lower // 2)
    hi = isqrt(SCALE * upper // 2)
    return lo, hi + (2 * hi**2 < SCALE * upper)


def phase_sum_box(numerator, length):
    """Enclose the real and imaginary parts in units of 1/SCALE."""
    cosine = (SCALE, SCALE)
    re_lo = re_hi = im_lo = im_hi = 0
    for width in range(1, length + 1):
        # This width picks one of the ordered suffixes, from shortest
        # to longest. The cosine at the previous width has twice the angle.
        modulus = 1 << width
        residue = numerator & (modulus - 1)
        lo, hi = cosine
        cosine = sqrt_half_box(SCALE + lo, SCALE + hi)
        sine = sqrt_half_box(SCALE - hi, SCALE - lo)
        if modulus < 4 * residue < 3 * modulus:
            cosine = (-cosine[1], -cosine[0])
        if modulus < 2 * residue:
            sine = (-sine[1], -sine[0])
        re_lo += cosine[0]
        re_hi += cosine[1]
        im_lo += sine[0]
        im_hi += sine[1]
    return (re_lo, re_hi), (im_lo, im_hi)


def norm_squared_box(a, length):
    lower = upper = 0
    for lo, hi in phase_sum_box(a, length):
        if not lo <= 0 <= hi:
            lower += min(lo**2, hi**2)
        upper += max(lo**2, hi**2)
    return lower, upper


def transition_count(a, length):
    bits = f"{a:0{length}b}"
    return sum(left != right for left, right in zip(bits, bits[1:]))


class FixedFrequencyTests(unittest.TestCase):
    def test_residual_selects_the_actual_digit_and_brackets_the_point(self):
        scale, a, residual = 1, 0, 1
        for n in range(513):
            self.assertEqual(a, prefix_value(2, n))
            self.assertTrue(polynomial_certificate(scale, a))
            self.assertEqual(residual, scale**2 - a**2 - scale * a)
            derivative = 2 * a + scale
            # A second exact floor encloses x_n without using the recurrence.
            tail_scale = 1 << 16
            tail = prefix_value(2, n + 16) - tail_scale * a
            self.assertTrue(0 <= tail < tail_scale)
            self.assertLessEqual(tail * (derivative * tail_scale + tail),
                                 residual * tail_scale**2)
            self.assertLess(residual * tail_scale**2,
                            (tail + 1) * (derivative * tail_scale + tail + 1))
            if n:
                self.assertGreaterEqual(transition_count(a, n), n.bit_length() - 1)
            gap = 2 * derivative + 1
            digit = int(4 * residual >= gap)
            scale, a, residual = 2 * scale, 2 * a + digit, 4 * residual - digit * gap

    def test_transition_bound_for_exact_sums(self):
        cases = [(n, a) for n in range(2, 8) for a in range(1 << n)]
        cases += [(n, prefix_value(2, n)) for n in (8, 10, 20, 32, 64, 128, 256, 512)]
        twice_loss = 2 * SCALE - isqrt(2 * SCALE**2)
        for n, a in cases:
            # Round the loss upward to test a slightly stronger inequality.
            cap = 2 * SCALE * n - twice_loss * transition_count(a, n)
            self.assertGreaterEqual(cap, 0, (n, a))
            self.assertLessEqual(4 * norm_squared_box(a, n)[1], cap**2, (n, a))

    def test_actual_square_root_cap_and_one_digit_sign_fail(self):
        a20 = prefix_value(2, 20)
        self.assertEqual(a20, 648055)
        lo, hi = norm_squared_box(a20, 20)
        self.assertGreater(lo, 24 * SCALE**2)
        self.assertLess(hi, 25 * SCALE**2)
        self.assertEqual((prefix_value(2, 5), prefix_value(2, 6)), (19, 39))
        lo5, hi5 = phase_sum_box(19, 5)[0]
        lo6, hi6 = phase_sum_box(39, 6)[0]
        self.assertGreater(1000 * (lo6 - hi5), 361 * SCALE)
        self.assertLess(1000 * (hi6 - lo5), 362 * SCALE)

    def test_dense_transitions_and_balanced_runs_allow_large_sums(self):
        n = 100
        alternating = ((1 << n) - 1) // 3
        self.assertEqual(transition_count(alternating, n), n - 1)
        self.assertLess(phase_sum_box(alternating, n)[0][1], -48 * SCALE)
        bits = "".join("0" * k + "1" * k for k in range(1, 33))
        self.assertEqual(bits.count("1"), len(bits) // 2)
        runs = int(bits, 2)
        self.assertEqual(transition_count(runs, len(bits)), 63)
        self.assertGreater(4 * phase_sum_box(runs, len(bits))[0][0], 3 * SCALE * len(bits))


if __name__ == "__main__":
    unittest.main()
