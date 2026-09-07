#!/usr/bin/env python3
"""Exact checks for the finite certificate in Appendix C and identity (3.1).

Uses only the Python standard library. This does not verify the infinite
construction, asymptotic estimates, or categorical arguments.
"""
from fractions import Fraction as F
from math import lcm

ROWS = [
    [35,56,90,119,152,170,455,494,714],
    [17,35,44,84,104,119,132,170,272,285,455,494,560,714,935],
    [9,17,34,44,77,84,90],
    [7,16,34,44,51,65,77,119,132,153,170,272,285,455,494],
    [2],
]
CERT = [(116396280,19399380),(232792560,77597520),
        (3063060,1531530),(232792560,155195040),(6,5)]
BASES = [12,20,30,60,140,210,420,840,1260,2520]


def unused(a, b):
    """Number of integers strictly between two closed integer intervals."""
    a, b = sorted((a, b))
    return b[0] - a[1] - 1


for j, (row, cert) in enumerate(zip(ROWS, CERT), 1):
    assert sum((F(1,m)+F(1,m+1) for m in row), F()) == F(j,6)
    den = lcm(*(m*(m+1) for m in row))
    num = sum((2*m+1)*(den//(m*(m+1))) for m in row)
    assert (den,num) == cert
    assert all(unused((a,a+1),(b,b+1)) >= 1 for a,b in zip(row,row[1:]))
    gap = min(unused((m,m+1),(a,a+2)) for m in row for a in BASES)
    assert gap == [2,1,1,1,8][j-1]
assert min(unused((a,a+2),(b,b+2)) for a,b in zip(BASES,BASES[1:])) == 5
assert [len(row) for row in ROWS] == [9,15,7,15,1]
print('PASS: all five rational seed identities, counts, denominators and gaps')

# Reconstruct the exceptional bridges from the lcm filtration itself.
previous = 6
reconstructed = []
for n in range(4,10):
    upper = lcm(previous,n)
    if upper == previous:
        continue
    p = upper//previous
    k = 1
    while k*(k+1)//2 < p-1:
        k += 1
    residues = {0}
    for r in range(1,k+1):
        assert upper % r == 0
        a = upper//r
        reconstructed.append(a)
        assert sum(F(1,x) for x in range(a,a+3)) - sum(F(1,x) for x in range(a+1,a+3)) == F(r,upper)
        residues |= {(s+r)%p for s in residues}
    assert residues == set(range(p))
    previous = upper
assert sorted(reconstructed) == BASES
assert previous == 2520
assert F(5,6)+sum(F(3,a) for a in [12,20,30,60]) == F(83,60) < F(3,2)
assert F(6,60)*2 == F(1,5) < F(1,4)
assert F(83,60)+F(1,5) < F(7,4)
print('PASS: exceptional lcm bridges, quotient coverage and rational mass bounds')

# Polynomial arithmetic in Q[a], coefficients in ascending degree.
def add(a,b):
    c = [F(0)]*max(len(a),len(b))
    for i,x in enumerate(a): c[i] += x
    for i,x in enumerate(b): c[i] += x
    return c


def mul(a,b):
    c = [F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j] += x*y
    return c


# P(a)+P(a^2+3a+1)-P(a+2)-P(a(a+3)/2)-P(a(a+3)).
starts = [(1,[0,1]), (1,[1,3,1]), (-1,[2,1]),
          (-1,[0,F(3,2),F(1,2)]), (-1,[0,3,1])]
terms = [(sign, add(poly,[offset])) for sign,poly in starts for offset in [0,1]]
numerator = [F(0)]
for i,(sign,_) in enumerate(terms):
    term = [F(sign)]
    for j,(_,den) in enumerate(terms):
        if i != j: term = mul(term,den)
    numerator = add(numerator,term)
assert all(c == 0 for c in numerator)
# All denominator polynomials are positive for a > 0.
assert all(all(c >= 0 for c in den) and any(c > 0 for c in den) for _,den in terms)
print('PASS: neutral identity as an exact polynomial identity over Q')
print('All finite-certificate checks passed.')
