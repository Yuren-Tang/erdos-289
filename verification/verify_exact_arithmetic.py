#!/usr/bin/env python3
"""Exact arithmetic checks used in Appendix C and Equation (3.1).

Uses only the Python standard library.
"""
from fractions import Fraction as F
from math import lcm

ROWS = [
    [35, 56, 90, 119, 152, 170, 455, 494, 714],
    [17, 35, 44, 84, 104, 119, 132, 170, 272, 285, 455, 494, 560, 714, 935],
    [9, 17, 34, 44, 77, 84, 90],
    [7, 16, 34, 44, 51, 65, 77, 119, 132, 153, 170, 272, 285, 455, 494],
    [2],
]
CERT = [
    (116396280, 19399380),
    (232792560, 77597520),
    (3063060, 1531530),
    (232792560, 155195040),
    (6, 5),
]
BASES = [12, 20, 30, 60, 140, 210, 420, 840, 1260, 2520]
EXPECTED_START_GAPS = [18, 9, 6, 7]
EXPECTED_SEED_BRIDGE_GAPS = [2, 1, 1, 1, 8]


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def unused(a, b):
    """Number of integers strictly between two closed integer intervals."""
    a, b = sorted((a, b))
    return b[0] - a[1] - 1


# Exact finite initialization from Appendix C.
require(len(ROWS) == len(CERT) == 5, "expected five nonzero residue rows")
require(
    [len(row) for row in ROWS] == [9, 15, 7, 15, 1],
    "component-count data do not match Appendix C",
)
require(
    [min(b - a for a, b in zip(row, row[1:])) for row in ROWS[:-1]]
    == EXPECTED_START_GAPS,
    "displayed minimum start gaps do not match Appendix C",
)

for j in range(1, 6):
    row = ROWS[j - 1]
    cert = CERT[j - 1]
    require(
        sum((F(1, m) + F(1, m + 1) for m in row), F()) == F(j, 6),
        f"seed identity {j}/6 failed",
    )
    den = lcm(*(m * (m + 1) for m in row))
    num = sum((2 * m + 1) * (den // (m * (m + 1))) for m in row)
    require(
        (den, num) == cert,
        f"common-denominator certificate for row {j} failed",
    )
    require(
        all(unused((a, a + 1), (b, b + 1)) >= 1 for a, b in zip(row, row[1:])),
        f"seed row {j} is not a separated configuration",
    )
    gap = min(unused((m, m + 1), (a, a + 2)) for m in row for a in BASES)
    require(
        gap == EXPECTED_SEED_BRIDGE_GAPS[j - 1],
        f"seed-to-bridge gap for row {j} failed",
    )

require(
    min(unused((a, a + 2), (b, b + 2)) for a, b in zip(BASES, BASES[1:])) == 5,
    "bridge-to-bridge gap failed",
)
print("PASS: finite initialization identities, counts, denominators and gaps")

# Reconstruct the exceptional bridges from the lcm filtration itself.
previous = 6
reconstructed = []
for n in range(4, 10):
    upper = lcm(previous, n)
    if upper == previous:
        continue
    p = upper // previous
    k = 1
    while k * (k + 1) // 2 < p - 1:
        k += 1
    residues = {0}
    for r in range(1, k + 1):
        require(upper % r == 0, f"nonintegral bridge base at n={n}, r={r}")
        a = upper // r
        reconstructed.append(a)
        require(
            sum(F(1, x) for x in range(a, a + 3))
            - sum(F(1, x) for x in range(a + 1, a + 3))
            == F(r, upper),
            f"bridge switch identity failed at n={n}, r={r}",
        )
        residues |= {(s + r) % p for s in residues}
    require(residues == set(range(p)), f"quotient coverage failed at n={n}")
    previous = upper

require(sorted(reconstructed) == BASES, "exceptional bridge bases do not match")
require(previous == 2520, "lcm filtration endpoint is not 2520")
require(
    F(5, 6) + sum(F(3, a) for a in [12, 20, 30, 60]) == F(83, 60) < F(3, 2),
    "finite bridge mass bound failed",
)
require(F(6, 60) * 2 == F(1, 5) < F(1, 4), "future bridge mass bound failed")
require(F(83, 60) + F(1, 5) < F(7, 4), "combined mass bound failed")
print("PASS: exceptional bridges, quotient coverage and rational mass bounds")


# Polynomial arithmetic in Q[a], coefficients in ascending degree.
def add(a, b):
    c = [F(0)] * max(len(a), len(b))
    for i, x in enumerate(a):
        c[i] += x
    for i, x in enumerate(b):
        c[i] += x
    return c


def mul(a, b):
    c = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return c


# P(a)+P(a^2+3a+1)-P(a+2)-P(a(a+3)/2)-P(a(a+3)).
starts = [
    (1, [0, 1]),
    (1, [1, 3, 1]),
    (-1, [2, 1]),
    (-1, [0, F(3, 2), F(1, 2)]),
    (-1, [0, 3, 1]),
]
terms = [
    (sign, add(poly, [offset]))
    for sign, poly in starts
    for offset in [0, 1]
]
numerator = [F(0)]
for i, (sign, _) in enumerate(terms):
    term = [F(sign)]
    for j, (_, den) in enumerate(terms):
        if i != j:
            term = mul(term, den)
    numerator = add(numerator, term)

require(all(c == 0 for c in numerator), "neutral identity failed")
require(
    all(all(c >= 0 for c in den) and any(c > 0 for c in den) for _, den in terms),
    "a denominator polynomial is not positive for a > 0",
)
print("PASS: reciprocal-neutral identity as an exact polynomial identity over Q")
print("All exact arithmetic checks passed.")
