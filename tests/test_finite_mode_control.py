"""Exact residue controls for the rational doubling orbits."""

from collections import Counter
import unittest


class FiniteModeControlTests(unittest.TestCase):
    def test_complete_period_histograms(self):
        for k in range(1, 6):
            step = 3**k
            modulus = 3 * step
            residues = []
            residue = 1
            for _ in range(2 * step):
                residues.append(residue)
                residue = 2 * residue % modulus
            self.assertEqual(residue, 1)
            self.assertEqual(set(residues), {r for r in range(modulus) if r % 3})

            for frequency in range(1 - step, step):
                if frequency == 0:
                    continue
                histogram = Counter(frequency * residue % modulus for residue in residues)
                # In each class the three phases differ by primitive cube
                # roots of unity. Equal multiplicities give an exact zero sum.
                self.assertTrue(all(
                    histogram[r] == histogram[r + step] == histogram[r + 2 * step]
                    for r in range(step)
                ))

            self.assertEqual(
                Counter(modulus * residue % modulus for residue in residues),
                Counter({0: 2 * step}),
            )


if __name__ == "__main__":
    unittest.main()
