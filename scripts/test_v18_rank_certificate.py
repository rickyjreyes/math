"""Regression checks for the real-input enclosures used by the v18 certificate."""
from fractions import Fraction
import unittest

from mpmath.libmp import to_rational

import v18_analytic_rank_certificate as certificate


def endpoints(interval):
    return tuple(Fraction(*to_rational(x)) for x in interval._mpi_)


class SourceEnclosures(unittest.TestCase):
    def test_all_stored_coefficients_and_nominal_decimals_are_enclosed(self):
        for text in certificate.LIGHT + certificate.MIDDLE + certificate.HEAVY:
            with self.subTest(coefficient=text):
                lo, hi = endpoints(certificate.coefficient(text))
                for value in (Fraction(text), Fraction.from_float(float(text))):
                    self.assertLessEqual(lo, value)
                    self.assertLessEqual(value, hi)

    def test_source_ratios_and_exact_rational_interpretation_are_enclosed(self):
        for n, d in [(95, 100), (96, 100), (123, 100), (123, 124)]:
            with self.subTest(n=n, d=d):
                lo, hi = endpoints(certificate.source_ratio(n, d))
                for value in (Fraction(n, d), Fraction.from_float(n / d)):
                    self.assertLessEqual(lo, value)
                    self.assertLessEqual(value, hi)


if __name__ == "__main__":
    unittest.main()
