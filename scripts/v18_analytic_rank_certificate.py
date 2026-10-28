#!/usr/bin/env python3
"""Analytic 11x11 rank certificate for the *frozen* v18 31-to-11 observation map.

This proves the exact Jacobian has row rank 11 on the explicitly verified
non-clamped parameter neighborhood, by finding a nonzero analytic 11x11 minor.
It does not infer global parameter identifiability or certify the physics.

Dependency: pip install mpmath==1.3.0
To bind to the actual frozen source file (including optimized live values):
  python scripts/v18_analytic_rank_certificate.py --source PATH/TO/_terms_perfection_v18.py
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
from fractions import Fraction
from pathlib import Path

from mpmath import iv

iv.dps = 60
v = iv.mpf


def enclose_nominal_and_binary64(nominal, stored):
    """Enclose the exact rational input and its source binary64 value.

    The source's coefficient arrays initially have dtype float64. Their
    printed decimals are not the exact stored numbers. Rational endpoints
    followed by outward-rounded interval division cover both interpretations.
    This certifies the analytic real model, not floating execution derivatives.
    """
    a, b = Fraction(nominal), Fraction.from_float(float(stored))
    lo, hi = min(a, b), max(a, b)
    lower = v(lo.numerator) / v(lo.denominator)
    upper = v(hi.numerator) / v(hi.denominator)
    return v([lower.a, upper.b])


def coefficient(text):
    return enclose_nominal_and_binary64(Fraction(text), float(text))


def source_ratio(n, d):
    # Heavy-sector ratios are computed by Python float division in the source.
    return enclose_nominal_and_binary64(Fraction(n, d), n / d)


TINY = coefficient("0.000000000001")
SOURCE_GIT_BLOB = "d98cfe243c5a90c332c80ca88618b2343e0698f4"
LIGHT = [".3877", "-2.3676", "-8.2963", "6.8830", "-1.7948",
         "-8.6415", "-6.1744", ".9981", ".0048"]
MIDDLE = ["2241.1", "5.0632", "9.4062", "1.6469", ".2092", "998.7", ".2427"]
HEAVY = ["98949", "12795", "-3.301", "9.039", "61635", "-1.189",
         "17770", "5.615", "8624", "-1.264", "4.685", "896077", "-952363"]
LIGHT_N = (1, 2, 3)
MIDDLE_N = (12, 19, 53, 73, 91)
HEAVY_N = (95, 96, 123)
ALPHA = v(["5.172", "5.173"])  # verified against the pinned source when --source is used
EPSILON = v(5)


def det(a):
    """Leibniz determinant with outward-rounded interval operations."""
    n = len(a)
    ans = v(0)
    for p in itertools.permutations(range(n)):
        inversions = sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
        term = v(-1 if inversions % 2 else 1)
        for i, j in enumerate(p):
            term *= a[i][j]
        ans += term
    return ans


def light_raw(n):
    m0, beta, sigma, theta, gamma, amp, lamb, chi, _ = map(coefficient, LIGHT)
    c = (n % 3 - 1) * (-1) ** n
    arg = lamb * n
    if arg < -50:
        arg = v(-50)
    elif arg > 50:
        arg = v(50)
    else:
        assert arg > -50 and arg < 50, "uncertified exponential clipping boundary"
    return (m0 * (v(n) / (n + 1)) + beta * c + sigma * iv.log(v(n + 1))
            + theta * n ** 2 + gamma * n ** 3 + amp * iv.exp(arg)
            + chi / n ** 2)


def suppression(n):
    return 1 / (1 + iv.exp(ALPHA * (n - EPSILON)))


def middle_rows():
    amp, scale1, scale2, phase, harmonic, offset, quad = map(coefficient, MIDDLE)
    rows = []
    for n in MIDDLE_N:
        x = scale1 * n + phase
        pred = amp * iv.sin(x) + harmonic * iv.sin(scale2 * n) + offset + quad * n * n
        assert pred > TINY, f"middle output n={n} is clamped or uncertified: {pred}"
        # Columns: offset, quad, amp, phase, harmonic.
        rows.append([v(1), v(n * n), iv.sin(x), amp * iv.cos(x),
                     iv.sin(scale2 * n)])
    return rows


def heavy_rows():
    (_, boson, _, boson_power, nonlin1, power1, nonlin2, power2,
     wz, angle, phase, higgs, offset) = map(coefficient, HEAVY)
    assert boson_power > -10 and boson_power < 10, "uncertified power clipping boundary"
    rows = []
    for n in HEAVY_N:
        z = source_ratio(n, 100)
        assert z > coefficient(".000001") and z < 1000000
        power1_value = iv.power(z, power1)
        x = angle * n + phase
        correction = (boson * iv.power(z, boson_power)
                      + nonlin1 * power1_value + nonlin2 * iv.power(z, power2))
        if n in (95, 96):
            correction += wz * iv.sin(x)
        if n == 123:
            correction += higgs * source_ratio(n, n + 1) + offset
        baseline_raw = light_raw(n) * suppression(n)
        assert baseline_raw < TINY, f"heavy light-baseline floor is not strictly active: {n}"
        assert correction > TINY, f"heavy n={n} correction is not positive: {correction}"
        # Actual heavy baseline is max(light_mass, 1e-12) >= 1e-12, hence
        # the outer max cannot be active and these derivatives are exact.
        # Columns: boson_nonlin1_scale, wz_break_scale, higgs_offset.
        rows.append([power1_value, iv.sin(x) if n in (95, 96) else v(0),
                     v(1) if n == 123 else v(0)])
    return rows


def validate_source(path):
    """Bind the certificate to the unchanged physical-model implementation."""
    import contextlib
    import io
    import runpy

    data = Path(path).read_bytes()
    git_hash = hashlib.sha1(b"blob " + str(len(data)).encode() + bytes([0]) + data).hexdigest()
    assert git_hash == SOURCE_GIT_BLOB, (
        f"Source revision changed ({git_hash}); regenerate and re-audit the certificate")
    with contextlib.redirect_stdout(io.StringIO()):
        ns = runpy.run_path(str(path), run_name="__certify_v18_rank__")
    for key, expected in (("light_params_best", LIGHT),
                          ("middle_params_best", MIDDLE),
                          ("heavy_params_best", HEAVY)):
        assert list(map(float, ns[key])) == list(map(float, expected)), key
    assert bool(ns["result"].success), "Historical optimizer did not converge"
    a, e = map(float, ns["result"].x)
    assert 5.172 <= a <= 5.173 and e == 5.0, f"Live values out of certified interval: {a}, {e}"
    keys = [int(n) for n, target in ns["all_targets"].items() if target > 0]
    assert keys == list(LIGHT_N + MIDDLE_N + HEAVY_N), keys
    for n in keys:
        predicted = float(ns["total_mass"](n, a, e))
        assert predicted > 1e-8, (n, predicted)
    print(f"Pinned historical source validated; alpha={a:.10f}, epsilon={e:.10f}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path,
                        help="Optional original frozen _terms_perfection_v18.py; validates source hash, optimizer and branch conditions")
    args = parser.parse_args()
    if args.source:
        validate_source(args.source)
    else:
        print("Source binding NOT checked: supply --source to validate the historical optimizer.")

    for n in LIGHT_N:
        mass = light_raw(n) * suppression(n) * (coefficient(LIGHT[8]) if n == 3 else v(1))
        assert mass > TINY, f"light n={n} max branch is active or uncertified"

    # Rational determinant of rows (n/(n+1), n², n³) for n=1,2,3:
    rational = [[Fraction(n, n + 1), Fraction(n * n), Fraction(n ** 3)] for n in LIGHT_N]
    det_rational = sum(
        Fraction(-1 if sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3)) % 2 else 1)
        * rational[0][p[0]] * rational[1][p[1]] * rational[2][p[2]]
        for p in itertools.permutations(range(3)))
    assert det_rational == 9
    det_light = v(9) * coefficient(LIGHT[8])
    for n in LIGHT_N:
        det_light *= suppression(n)

    det_middle = det(middle_rows())
    det_heavy = det(heavy_rows())
    assert det_middle > v("20000000")
    assert det_heavy > v("1.2")
    det_selected = det_light * det_middle * det_heavy
    assert det_selected > v("1000000")
    print("Minor columns: light(m0,theta,gamma), middle(offset,quad,amp,phase,harmonic),")
    print("               heavy(boson_nonlin1_scale,wz_break_scale,higgs_offset)")
    print("Exact rational light base determinant:", det_rational)
    print("Middle determinant interval:", det_middle)
    print("Heavy determinant interval:", det_heavy)
    print("Full analytic 11x11 determinant interval:", det_selected)
    print("VERIFIED: Jacobian rank 11; kernel dimension 31 - 11 = 20 (on certified source/parameter branch).")


if __name__ == "__main__":
    main()
