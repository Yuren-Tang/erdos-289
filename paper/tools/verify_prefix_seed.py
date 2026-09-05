#!/usr/bin/env python3
"""Exact replay of the finite certificate in Appendix C.

This script is ancillary verification only: it checks the displayed rational
identities and finite separation assertions.  The manuscript contains the proof.
"""

from fractions import Fraction
from itertools import combinations


def P(m: int) -> Fraction:
    return Fraction(1, m) + Fraction(1, m + 1)


ROWS = {
    1: [35, 56, 90, 119, 152, 170, 455, 494, 714],
    2: [17, 35, 44, 84, 104, 119, 132, 170, 272, 285, 455, 494, 560, 714, 935],
    3: [9, 17, 34, 44, 77, 84, 90],
    4: [7, 16, 34, 44, 51, 65, 77, 119, 132, 153, 170, 272, 285, 455, 494],
    5: [2],
}

# Successive exceptional bridge stages following the H_6 seed.
BRIDGE_STAGES = [
    [12],
    [20, 30, 60],
    [140, 210, 420],
    [840],
    [1260, 2520],
]


def compatible(i: tuple[int, int], j: tuple[int, int]) -> bool:
    """Two path intervals are disjoint and nonadjacent."""
    if i[0] > j[0]:
        i, j = j, i
    return j[0] - i[1] >= 2


# PS1: exact residues and internal separation of every seed row.
for residue, starts in ROWS.items():
    assert sum((P(m) for m in starts), Fraction(0)) == Fraction(residue, 6)
    seed_components = [(m, m + 1) for m in starts]
    assert all(compatible(a, b) for a, b in combinations(seed_components, 2))

# The displayed coefficient sets cover the two early quotient groups.
assert {sum(s) % 2 for r in range(2) for s in combinations([1], r)} == {0, 1}
assert {
    sum(s) % 5
    for r in range(4)
    for s in combinations([1, 2, 3], r)
} == set(range(5))

# A bridge at base a has alternatives supported in [a+1,a+2] and [a,a+2];
# the larger interval [a,a+2] is therefore a sufficient envelope for both.
bridge_envelopes: list[tuple[int, int]] = []
for stage in BRIDGE_STAGES:
    current = [(a, a + 2) for a in stage]

    # Each exceptional bridge is compatible with every displayed seed branch.
    for starts in ROWS.values():
        for seed in ((m, m + 1) for m in starts):
            assert all(compatible(seed, bridge) for bridge in current)

    # Simultaneously occurring bridges are mutually compatible, both within
    # the current stage and with all preceding stages.
    assert all(compatible(a, b) for a, b in combinations(current, 2))
    for bridge in current:
        assert all(compatible(bridge, old) for old in bridge_envelopes)
    bridge_envelopes.extend(current)

# Bridge reciprocal differences used in Appendix C.
for p, D, coefficients in [(2, 6, [1]), (5, 12, [1, 2, 3])]:
    for r in coefficients:
        a = p * D // r
        left = P(a + 1)
        right = Fraction(1, a) + Fraction(1, a + 1) + Fraction(1, a + 2)
        assert right - left == Fraction(r, p * D)

# PS4 and PS6 leave a strict margin below 2.
finite_bound = Fraction(5, 6) + sum(Fraction(3, a) for a in [12, 20, 30, 60])
assert finite_bound == Fraction(83, 60)
assert finite_bound < Fraction(3, 2)
future_bound = sum(Fraction(6, 60 * 2**j) for j in range(64))
assert future_bound < Fraction(1, 5)  # finite partial sum; the infinite sum is 1/5
assert finite_bound + Fraction(1, 5) < 2

print("Appendix C finite initialization: exact replay PASS")
