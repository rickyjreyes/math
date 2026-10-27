#!/usr/bin/env python3
"""Exact-rational, dependency-free outer bound for the frozen F09 5x5 minor.

Uses ONLY integer/Fraction arithmetic, Mathlib's published rational
bounds 3.14159265358979323846 < pi < 3.14159265358979323847, and
the analytic estimates (for |t|<=1):
  |sin(t) - (t-t**3/6)| <= 5|t|**4/96
  |cos(t) - (1-t**2/2)| <= 5|t|**4/96.
Those are provided in Mathlib v4.23.0 as Real.sin_bound and Real.cos_bound.

Exact interval four-corner multiplication and the 120-term Leibniz
formula yield a positive determinant interval. This is a rigorously
checkable *mathematical certificate implemented in Python*, NOT a Lean
proof of the transcendental determinant. Porting the interval arithmetic
into the Lean kernel remains the F09 closure task.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import permutations

PI_LO = F(314159265358979323846, 10**20)
PI_HI = F(314159265358979323847, 10**20)
NS = (12, 19, 53, 73, 91)
ROT1 = (40, 62, 172, 236, 294)
ROT2 = (72, 114, 317, 437, 545)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __post_init__(self):
        assert self.lo <= self.hi

    @classmethod
    def point(cls, x: F | int | str) -> "I":
        q = F(x)
        return cls(q, q)

    def __add__(self, other: "I") -> "I":
        return I(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> "I":
        return I(-self.hi, -self.lo)

    def __sub__(self, other: "I") -> "I":
        return self + -other

    def __mul__(self, other: "I") -> "I":
        corners = tuple(a*b for a in (self.lo, self.hi)
                        for b in (other.lo, other.hi))
        return I(min(corners), max(corners))

    def scale(self, q: F | int | str) -> "I":
        return self * I.point(q)

    def power(self, n: int) -> "I":
        assert n >= 0
        result = I.point(1)
        for _ in range(n):
            result = result * self
        return result


def taylor_interval(t: I, is_cos: bool) -> I:
    R = max(abs(t.lo), abs(t.hi))
    assert R <= 1
    t2 = t.power(2)
    approximation = (I.point(1) - t2.scale(F(1, 2))) if is_cos else (
        t - t.power(3).scale(F(1, 6)))
    error = F(5, 96) * R**4
    return approximation + I(-error, error)


def frozen_trig(x: F, quarters: int) -> tuple[I, I]:
    """sin(x),cos(x) using x = remainder + quarters*pi/2."""
    pi = I(PI_LO, PI_HI)
    remainder = I.point(x) - pi.scale(F(quarters, 2))
    s, c = taylor_interval(remainder, False), taylor_interval(remainder, True)
    return ((s, c), (c, -s), (-s, -c), (-c, s))[quarters % 4]


def frozen_middle_intervals() -> list[list[I]]:
    M = []
    for n, k1, k2 in zip(NS, ROT1, ROT2):
        s, c = frozen_trig(F("5.0632") * n + F("1.6469"), k1)
        t, _ = frozen_trig(F("9.4062") * n, k2)
        M.append([I.point(1), I.point(n*n), s,
                  c.scale(F("2241.1")), t])
    return M


def det5_interval(A: list[list[I]]) -> I:
    result = I.point(0)
    for perm in permutations(range(5)):
        inversions = sum(perm[i] > perm[j]
                         for i in range(5) for j in range(i+1, 5))
        term = I.point(-1 if inversions % 2 else 1)
        for j in range(5):
            term = term * A[perm[j]][j]
        result = result + term
    return result


def main():
    matrix = frozen_middle_intervals()
    bound = det5_interval(matrix)
    assert bound.lo > F(18_000_000), f"Unexpected lower bound: {bound.lo}"
    assert bound.hi < F(24_000_000), f"Unexpected upper bound: {bound.hi}"
    print("Mathlib-compatible input: pi_gt_d20 / pi_lt_d20, sin_bound, cos_bound")
    for n, row in zip(NS, matrix):
        print("n =", n, "three trigonometric entries:")
        for cell in (row[2], row[3], row[4]):
            print("  approximate endpoints:", float(cell.lo), float(cell.hi))
    print("det(M) rational lower:", bound.lo)
    print("det(M) rational upper:", bound.hi)
    print("CONCLUSION: 18,000,000 < det(M) < 24,000,000")
    print("LEAN STATUS: bounds not yet encoded as Lean theorems")


if __name__ == "__main__":
    main()
