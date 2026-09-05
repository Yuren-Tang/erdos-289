# E3 — total signed-inverse current provider

This file proves the five capabilities of E3 from E1 and G2.  All construction coordinates die at the end of this file.

Fix the comparable-prime constants `(Λ,c_Π,C_Π)` of G2 and put the proof-local constant
\[
B_{car}=\Lambda+1.
\]
Let the current rank be
\[
Q=p^e.
\]

# 1. Carrier set and deterministic signed inverse

Define
\[
Car(Q)=\left\{b\text{ prime}:Q/B_{car}<b\le\Lambda Q/B_{car},\ b<Q,\gcd(b,Q)=1\right\}.
\]
For sufficiently large `Q`, G2 gives
\[
|Car(Q)|\asymp Q/\log Q.
\tag{1.1}
\]
The carrier prime differs from `p`: if `e=1`, then `b<Q=p`; if `e≥2`, then eventually `p=Q^{1/e}<Q/B_{car}`.

For each carrier `b`, let `c_+∈{1,…,Q-1}` be the inverse of `b mod Q`, put `c_-=Q-c_+`, and write
\[
bc_+=Qk_++1,
\qquad
bc_-=Qk_--1.
\tag{1.2}
\]
Then
\[
1\le k_\pm<b<Q,
\qquad
k_++k_-=b.
\tag{1.3}
\]
Since `p∤b`, the two coefficients cannot both be divisible by `p`.

Use the following deterministic sign rule.

- If `e=1`, choose the larger of `k_+,k_-` (break a tie in favour of `+`).
- If `e≥2`, choose `+` if `p∤k_+`, otherwise choose `-`.

Write the selected coefficient as `k(Q,b)`.  The selected binary atom is the interval
\[
a(Q,b)=
\begin{cases}
[Qk_+,Qk_++1],&+,\\
[Qk_--1,Qk_-],&-.
\end{cases}
\tag{1.4}
\]
For a prime current `Q=p`, (1.3) gives the stronger bound
\[
k(Q,b)\ge b/2>Q/(2B_{car}).
\tag{1.5}
\]

# 2. Intrinsic transversality and bounded exceptional set

The distinguished denominator is `Qk`.  Because `p∤k`, its `p`-primary current is exactly `Q=p^e`, and every prime-power current contributed by `k` has rank `<Q` because `k<Q`.

The companion denominator can have a current of rank `Q` only in the exceptional situation that the carrier `b` divides the inverse residue `c_+` or `c_-`.  Write then
\[
c_\pm=\ell b.
\]
Since `c_±<Q` and `b>Q/B_{car}`,
\[
1\le\ell<B_{car}.
\]
Substitution into (1.2) gives
\[
\ell b^2\equiv\pm1\pmod Q.
\tag{2.1}
\]
For fixed `(\ell,±)`, if `p|\ell` there is no solution.  If `p∤\ell`, (2.1) is a unit square-root equation modulo the prime power `p^e`: it has at most two roots for odd `p` and at most four in the `2`-primary case.  The carrier interval has length `<Q`, so each residue root contributes at most one carrier integer.  Since `1≤\ell<B_{car}`, only
\[
O_{B_{car}}(1)
\tag{2.2}
\]
carrier candidates fail transversality.

Delete these candidates.  Every retained atom has residue in
\[
F_Q\setminus F_{<Q}.
\tag{2.3}
\]

# 3. Coefficient deduplication and row size

For a fixed coefficient `k`, every carrier producing it divides one of
\[
Qk-1,\quad Qk+1<Q^2+1,
\]
while every carrier exceeds `Q/B_{car}`.  Therefore only `O_{B_{car}}(1)` carriers can produce the same coefficient: otherwise their product would exceed `Q^2+1`.

For each coefficient fibre retain the atom corresponding to its **least carrier**.  This makes deduplication deterministic.

By (1.1), (2.2), and bounded coefficient multiplicity, the number `N_Q` of distinct retained coefficients before the final rank thinning satisfies
\[
N_Q\asymp Q/\log Q.
\tag{3.1}
\]
For non-prime currents, order the coefficients
\[
k_1<\cdots<k_{N_Q}
\]
and retain the upper half.  Then every retained coefficient satisfies
\[
k\ge \lceil N_Q/2\rceil\gg Q/\log Q,
\qquad k<Q.
\tag{3.2}
\]
For prime currents retain all coefficients; the stronger bound (1.5) holds.

Let `A_Q` be the resulting finite family.  From (3.1),
\[
\boxed{|A_Q|\asymp Q/\log Q}
\tag{3.3}
\]
on one cofinal late locus.

# 4. Simple-value channel and exact fibre bound

Modulo `F_{<Q}`, the companion reciprocal vanishes and the distinguished term determines the simple value.  In any proof-local cyclic coordinate on the prime-order simple factor `S_Q`, the value is
\[
sv_Q(a)=k^{-1}\pmod p,
\tag{4.1}
\]
which is nonzero because `p∤k`.

The atom itself recovers `Q` and `k`: exactly one support denominator has maximal current rank `Q`, namely `Qk`; divide this distinguished endpoint by `Q` to recover `k`.

If two retained atoms have the same simple value, inversion in `F_p^×` gives the same residue class of `k mod p`.  For a fixed nonzero residue `r`, the integers
\[
1\le k<Q=p^e,\qquad k\equiv r\pmod p
\]
are exactly
\[
r,r+p,\ldots,r+(Q/p-1)p.
\]
Hence every simple-value fibre satisfies the exact threshold-free bound
\[
\boxed{|sv_Q^{-1}(s)|\le Q/p.}
\tag{4.2}
\]

# 5. Global centre injectivity and bounded conflicts

Associate to an atom its distinguished centre
\[
z=Qk.
\]
As noted above, the unordered atom recovers the unique maximal current `Q` and then `k`; coefficient deduplication keeps at most one atom for each `(Q,k)`.  Thus
\[
\boxed{a\mapsto Qk\text{ is globally injective across all current rows}.}
\tag{5.1}
\]

Each atom occupies two adjacent integers around its centre.  If a bounded physical envelope `E` (of the fixed complexity occurring in the proof) conflicts with the atom, its centre lies in a fixed finite enlargement `E^{+2}`.  Since centres are injective, every such envelope conflicts with only an absolute bounded number of retained atoms.  Consequently the global rowed conflict graph has uniformly bounded degree after any finite family of bounded-complexity roles is installed.

This proves the conflict capability independently of the row-cardinality and resource arguments.

# 6. Support scale

For non-prime currents, (3.2) gives
\[
Qk\gg Q^2/\log Q.
\]
For prime currents, (1.5) gives the stronger
\[
Qk\gg Q^2.
\]
Since the second atom vertex differs by `1`, there is a fixed `c_s>0` such that every sufficiently late retained atom has each support vertex `z` in
\[
\boxed{c_sQ^2/\log Q\le z\le2Q^2.}
\tag{6.1}
\]
For prime currents one may strengthen the lower bound to `c_aQ^2`.

The general scale (6.1) is consumed only by the preparatory future-footprint estimate; the prime strengthening is consumed only by the resource estimate.

# 7. Summable resource majorant

A local response at current `Q=p^e` never needs more than `p` atoms.  Define `roleMass(Q)` by the corresponding worst-case reciprocal mass.

## Prime currents
For `Q=p`, support is `\gg p^2`, so one atom has mass `O(p^{-2})`.  The row upper bound is `O(p/log p)`, hence
\[
roleMass(p)=O(1/(p\log p)).
\tag{7.1}
\]
Group primes into the geometric bands `(X,ΛX]`.  G2 gives `O(X/log X)` primes in one band, and every summand is `O(1/(X\log X))`; the band mass is therefore
\[
O(1/(\log X)^2).
\]
Along geometric bands this is `O(j^{-2})`, hence
\[
\sum_{p\ prime}roleMass(p)<\infty.
\tag{7.2}
\]

## Composite currents
For `Q=p^e`, `e≥2`, (3.2) gives one atom mass
\[
O(\log Q/Q^2).
\]
Using at most `p` atoms,
\[
roleMass(p^e)
=O\!\left(\frac{p\log Q}{Q^2}\right)
=O\!\left(\frac{e\log p}{p^{2e-1}}\right).
\tag{7.3}
\]
For fixed `p`, summing `e≥2` gives
\[
O(\log p/p^3)=O(p^{-2}),
\]
and then
\[
\sum_p\sum_{e\ge2}roleMass(p^e)<\infty.
\tag{7.4}
\]
Combining (7.2) and (7.4),
\[
\boxed{\sum_Q roleMass(Q)<\infty.}
\tag{7.5}
\]

# 8. Exported information and information death

The theorem exports exactly:

1. row scale `|A_Q|\asymp Q/log Q` on the late locus;
2. transverse nonzero simple values and fibre bound (4.2);
3. globally bounded conflict incidence;
4. support estimate (6.1) for the preparatory footprint;
5. the summable majorant (7.5).

Carrier primes, sign choices, inverse residues, duplicate occurrences, ordering positions and proof-local cyclic coordinates have no downstream consumer.