"""Independent finite checks for the spaced real-lag criterion."""

from fractions import Fraction
import unittest

from oracles.reference import polynomial_certificate, prefix_value
from test_fixed_frequency import SCALE, norm_squared_box, phase_sum_box


def lag_mode(h, spacing, lag):
    return h * ((1 << (spacing * lag)) - 1)


class LagCriterionTests(unittest.TestCase):
    def test_exact_16384_bit_certificate_uses_only_lag_upper_bounds(self):
        length, spacing, window = 16384, 2, 32
        numerator = prefix_value(2, length)
        self.assertTrue(polynomial_certificate(1 << length, numerator))
        tolerance = Fraction(3, 250)
        for lag in range(1, window):
            frequency = lag_mode(1, spacing, lag)
            real_upper = phase_sum_box(frequency * numerator, length)[0][1]
            self.assertLess(real_upper, tolerance * SCALE * length, lag)

        edge = Fraction(2 * spacing * window, length)
        bound = Fraction(117, 500)
        self.assertGreater(bound, edge)
        self.assertLess(Fraction(1, window) + tolerance + edge, (bound - edge)**2)
        # Independently enclose the target as well as the enabling correlations.
        self.assertLess(norm_squared_box(numerator, length)[1], (bound*SCALE*length)**2)

    def test_frequency_one_zero_does_not_control_the_scheduled_lags(self):
        period = [pow(2, start, 9) for start in range(6)]
        # Sum of the six phases is (X + X²)(1 + X³ + X⁶) at a primitive
        # ninth root. The second factor vanishes exactly.
        self.assertEqual(sorted(period), [r + 3*k for k in range(3) for r in (1, 2)])
        self.assertEqual(pow(2, 6, 9), 1)
        self.assertTrue(all(r * lag_mode(1, 2, 3) % 9 == 0 for r in period))

    def test_one_negative_lag_does_not_cover_all_pair_differences(self):
        # For source 1/3 and spacing 1, lag 1 is real part -1/2 at each
        # start. Lag 2 is exactly 1 at each start.
        period = (1, 2)
        self.assertEqual({r * lag_mode(1, 1, 1) % 3 for r in period}, {1, 2})
        self.assertEqual({r * lag_mode(1, 1, 2) % 3 for r in period}, {0})

    def test_sparse_schedule_cutoff_includes_all_eligible_positive_modes(self):
        for cutoff in (1, 2, 3, 15, 63, 511, 512, 10**6, 10**50):
            log_limit = (cutoff + 1).bit_length() - 1
            modes = set()
            for h in range(1, log_limit + 2, 2):
                spacing = 1 << h
                for lag in range(1, log_limit // spacing + 1):
                    mode = lag_mode(h, spacing, lag)
                    if mode <= cutoff:
                        modes.add(mode)
            self.assertLessEqual(len(modes), log_limit)
            if cutoff == 63:
                self.assertEqual(modes, {3, 15, 63})


if __name__ == "__main__":
    unittest.main()
