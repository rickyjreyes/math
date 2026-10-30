#!/usr/bin/env python3
"""Exact finite witnesses for GC167/278/233, not a global theorem prover.

The script checks each explicitly recorded counterexample or truth table
using Gaussian-integer and rational arithmetic without floating point.
Analytical Hopf and topology arguments require separate review.
"""
from fractions import Fraction

def add(x, y):
    return (x[0] + y[0], x[1] + y[1])

def imul(x):
    return (-x[1], x[0])

def norm2(x):
    return x[0] ** 2 + x[1] ** 2

def observations(z):
    a, b = z
    return (norm2(a), norm2(b), norm2(add(a, b)), norm2(add(a, imul(b))))

def phase_retrieval_witnesses():
    # (missing-index, candidate-1, candidate-2), 0-based indices
    cases = [
        (3, ((1, 0), (0, 1)), ((1, 0), (0, -1))),
        (2, ((1, 0), (1, 0)), ((1, 0), (-1, 0))),
        (1, ((1, 0), (0, 0)), ((1, 0), (-1, 1))),
        (0, ((0, 0), (1, 0)), ((-1, -1), (1, 0))),
    ]
    for omit, z, w in cases:
        a, b = observations(z), observations(w)
        assert all(a[j] == b[j] for j in range(4) if j != omit), (omit, a, b)
        assert a != b, "Omitted measurement should detect collision"
        # Not phase equivalent because at least one component modulus differs,
        # or one component is equal nonzero while the other differs.
        assert z[0] != w[0] or z[1] != w[1]
        if z[0] == w[0] and z[0] != (0, 0):
            assert z[1] != w[1]
        elif z[1] == w[1] and z[1] != (0, 0):
            assert z[0] != w[0]
    return len(cases)

def nand_truth_table():
    threshold = Fraction(1, 12)
    for a in (0, 1):
        for b in (0, 1):
            intensity = Fraction((2 - a - b) ** 2, 6)
            decoded = int(intensity > threshold)
            assert decoded == int(not (a and b)), (a, b, intensity)
            assert (a, b) != (0, 0) or (intensity > threshold)
    # No-reference passive optics maps zero input to zero output.
    assert not (Fraction(0) > threshold)
    # The first row (2,-1,-1)/sqrt(6) has unit squared norm.
    assert sum(Fraction(x*x, 6) for x in (2, -1, -1)) == 1
    return 4

def graph_promise_nonvacuity():
    # P5: lambda_2=(3-sqrt(5))/2 < 20/25
    # This comparison is equivalent to sqrt(5)>7/5.
    assert Fraction(5) > Fraction(49, 25)
    # K5: lambda_2=5 >= 80/25.
    assert Fraction(5) >= Fraction(80, 25)
    return 2

if __name__ == "__main__":
    print(f"PASS GC167: {phase_retrieval_witnesses()} exact collision pairs")
    print(f"PASS GC278: {nand_truth_table()} exact NAND cases")
    print(f"PASS GC233: {graph_promise_nonvacuity()} graph endpoint witnesses")
    print("Boundary: finite witnesses only, no 236-problem proof or novelty certification.")
