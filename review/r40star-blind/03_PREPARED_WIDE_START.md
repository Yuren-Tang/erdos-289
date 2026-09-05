# E4 — prepared wide affine start

This file proves the preparatory theorem without using E5, E6, or any actual Haxell packing.

Put
\[
L_n=\operatorname{lcm}(1,\ldots,n).
\]
At a prime-power jump `n=p^e`, let
\[
D=L_{n-1},\qquad L_n=pD.
\]
By E1, the quotient jump is the simple factor of order `p`.

# 1. Universal fixed-grade bridge at one jump

Let `k` be the least positive integer with
\[
T_k=\frac{k(k+1)}2\ge p-1
\]
and set
\[
R_p=\{1,2,\ldots,k\}.
\]
The subset sums of `R_p` fill every integer in `[0,T_k]`: inductively, after adjoining `j`, the old interval `[0,T_{j-1}]` and its translate `[j,j+T_{j-1}]` overlap or are adjacent.  Hence reduction modulo `p` is surjective.

Minimality gives `k≤p-1`, so every `r∈R_p` divides `D`.  Define
\[
a_r=\frac{pD}{r}
\]
and the two alternatives
\[
[a_r+1,a_r+2]
\quad\longleftrightarrow\quad
[a_r,a_r+2].
\tag{1.1}
\]
The first is a length-2 component and the second a length-3 component; both have grade `1`.  Their reciprocal difference is exactly
\[
\frac r{pD}.
\tag{1.2}
\]
Therefore the full finite-subset selector on `R_p` maps surjectively to
\[
L_n^{-1}\mathbf Z/L_{n-1}^{-1}\mathbf Z\cong\mathbf Z/p\mathbf Z.
\]
Every selector branch has the same total grade `k`.  Thus the bridge is a fixed-grade regular-epi response to the next simple quotient.  No subset section is chosen.

## 1.1 Absolute row resource bound

Since `T_{k-1}<p-1`,
\[
T_k=T_{k-1}+k<(p-1)+k\le2p-2<2p.
\tag{1.3}
\]
For either alternative at base `a_r`, the reciprocal mass is less than `3/a_r=3r/(pD)`.  Hence every bridge selector branch has mass
\[
<\frac3{pD}\sum_{r=1}^k r
=\frac{3T_k}{pD}
<\frac6D.
\tag{1.4}
\]

## 1.2 Exact structural separation after the finite boundary

Minimality also gives `k(k-1)<2p`.  For `k≥2`, `k≤2(k-1)`, so `k^2<4p`.  If `r<s≤k`,
\[
a_r-a_s
=\frac{pD(s-r)}{rs}
\ge\frac{pD}{k^2}
>D/4.
\tag{1.5}
\]
Thus once `D≥60`, intervals within one bridge row are separated by far more than the physical interaction radius.

Now compare different rows.  At a later prime-power jump `n=p^e` with lower modulus `D`, every earlier bridge base is at most the endpoint modulus reached before this jump, hence every earlier bridge support ends by `D+2`.  The smallest new base is
\[
a_k=\frac{pD}{k}\ge\frac{pD}{p-1}=D+\frac{D}{p-1}.
\tag{1.6}
\]
From the jump `n≥11` onward,
\[
D/(p-1)>3.
\tag{1.7}
\]
Indeed, if `e=1`, the integers `p-1` and `p-2` are both at most `n-1` and coprime, so their product divides `D`; hence `D/(p-1)≥p-2>3`.  If `e≥2`, then `D≥p^e-1` and
\[
\frac{p^e-1}{p-1}=1+p+\cdots+p^{e-1}>3
\]
on this locus.  Equations (1.6),(1.7) show that every new bridge row from `n≥11` starts more than three integers after every earlier bridge support.

Thus all non-asymptotic cross-row interactions are confined to the finitely many jumps through `n=9`; their concrete bases are exactly the finite list checked in `PREFIX_SEED_CERTIFICATE.json`.

# 2. Finite seed and ragged affine cover

The attached finite certificate/replay checks one early seed package with the following properties.

- It is a finite physical response covering one complete affine fibre at the early endpoint `H_6`.
- Its branch grades have one fixed finite spread `G_seed`.
- It is compatible with the finite exceptional bridge bases
  `12,20,30,60,140,210,420,840,1260,2520`; Section 1.2 handles all later bridge rows structurally.
- Its root reciprocal mass is at most `5/6`, and the early seed bridges have a certified crude mass bound `11/20`; hence root plus early bridge mass is strictly below `3/2`.

Compose the seed with one bridge at every later prime-power jump through an outer rank cutoff `B`.  By Section 1.2 the labels in this finite chain are physically separated, so the ordinary composability object factors through the n-ary physical multiplication domain of E2.  The quotient responses therefore paste to a physical relation covering a complete affine `H_B`-fibre.

Crucially, every bridge row is fixed-grade.  Hence every bridge adds the same grade constant to every old branch.  Therefore the branch-to-branch grade spread after any number of bridges is exactly the finite seed spread:
\[
\boxed{G_B=G_{seed}=O(1).}
\tag{2.1}
\]
The preparatory response before neutral amplification is thus a **ragged affine cover**: its torsor projection is surjective, and all branch grades lie in some interval `[m_B,M_B]` with `M_B-m_B=G_seed`.

# 3. Uniform bridge resource margin

Let `D_0,D_1,…` be the lower moduli of the bridge rows after the finite seed boundary.  At every nontrivial prime-power jump the endpoint modulus is multiplied by a prime, so
\[
D_{j+1}\ge2D_j.
\]
The first structural future row has `D_0≥60`.  By (1.4), the total reciprocal contribution of the entire infinite future bridge tower is bounded by
\[
\sum_{j\ge0}\frac6{D_j}
\le\frac6{D_0}\sum_{j\ge0}2^{-j}
\le\frac{12}{60}=\frac15.
\tag{3.1}
\]
The finite certificate gives root plus early bridge mass `<3/2`.  Therefore the seed plus **all** future universal bridges has mass
\[
<\frac32+\frac15<\frac74<2.
\tag{3.2}
\]
In particular there is a fixed positive open margin below `2`, uniform in the outer cutoff `B`.  We reserve such a margin for the neutral cube and later productive tail.

# 4. Sparse future footprint of the seed and bridges

Let a future signed-inverse row have current rank `Q>B`.  By E3 its support is contained in
\[
[cQ^2/\log Q,\,2Q^2]
\tag{4.1}
\]
up to fixed endpoint buffers.

Consider a bridge row at jump `n=p^e` with lower modulus `D=L_{n-1}`.  If one of its bounded physical envelopes can meet (4.1), then in particular
\[
D=O(Q^2).
\tag{4.2}
\]
The primorial through `n-1` divides `D`; the Chebyshev bounds proved in G2 therefore imply
\[
n,p=O(\log Q).
\tag{4.3}
\]
Using the lower end of (4.1) and the crude upper bound `a_r≤pD` gives
\[
D\gg Q^2/(\log Q)^2.
\tag{4.4}
\]
Successive nontrivial lower moduli multiply by at least `2`; the ratio between (4.2) and (4.4) is only polylogarithmic.  Hence only
\[
O(\log\log Q)
\]
bridge rows can meet the future support window.  Each such bridge has
\[
k=O(\sqrt p)=O(\sqrt{\log Q})
\]
bounded-complexity envelopes.  Therefore the number of preparatory envelopes capable of meeting the future row is
\[
\boxed{O(\sqrt{\log Q}\,\log\log Q)=o(Q/\log Q).}
\tag{4.5}
\]

By E3 bounded conflict incidence, each such envelope removes only `O(1)` future atoms.  Since the original row has `\asymp Q/\log Q` atoms, the ragged preparatory cover deletes only a vanishing fraction, uniformly in the outer cutoff `B`.

# 5. One neutral cube: grade rectification and startup width

Let the ragged cover have grades in `[m_B,M_B]` and put
\[
G=M_B-m_B=G_{seed}.
\]
Let `L(B)` be any nonnegative integer-valued function with
\[
L(B)=o(B/\log B).
\tag{5.1}
\]
Using G1, construct `G+L(B)` mutually compatible grade-neutral coordinates remote from the whole ragged cover.  By (3.2), their common total reciprocal cost may be chosen inside one fixed positive part of the remaining margin.

For a selector `\sigma∈\{0,1\}^{G+L}`, let `wt(\sigma)` be its Hamming weight.  All selectors have the same reciprocal value and the same residue translation; their grades are
\[
\lambda_B+wt(\sigma)
\]
for a common baseline `\lambda_B`.

For a ragged edge of grade `r` and a requested output offset `j∈[0,L(B)]`, require
\[
wt(\sigma)=(M_B-r)+j.
\tag{5.2}
\]
Because `0≤M_B-r≤G`, the right side lies in `[0,G+L]`.  The weight map
\[
wt:\{0,1\}^{G+L}\twoheadrightarrow[0,G+L]
\]
is surjective.  Therefore the matching object is the pullback
\[
\begin{CD}
P @>>> \{0,1\}^{G+L}\\
@VVV @VV{wt}V\\
E_{rag}\times[0,L] @>{(e,j)\mapsto M_B-r(e)+j}>> [0,G+L].
\end{CD}
\tag{5.3}
\]
The left projection is surjective by base-change stability.  Pasting with the ragged-cover surjection gives a physical cover of
\[
Tor_{H_B}(\alpha_B+\beta_B)
\times
[\lambda_B+M_B,\lambda_B+M_B+L(B)],
\tag{5.4}
\]
where `\beta_B` is the common residue translation of every neutral selector.

Thus **one** neutral cube simultaneously removes the finite ragged grade spread and creates the requested startup interval.  No branch section or chosen subset is used.

# 6. Future density after the neutral cube

The cube contributes only `O(G+L(B))` bounded-complexity physical envelopes, not one envelope for every Boolean selector.  By (2.1) and (5.1),
\[
G+L(B)=o(B/\log B).
\tag{6.1}
\]
For future `Q≥B`, `Q/log Q` is eventually increasing, so (6.1) is also `o(Q/log Q)`.  Together with (4.5) and E3 finite conflict incidence, the complete wide-start obstacle removes only `o(Q/log Q)` atoms from every future row.

Since E3 supplies a uniform positive lower row constant on a cofinal suffix, choose one fixed
\[
\sigma>0
\]
small enough that, after increasing the onset cutoff if necessary,
\[
|Surv(Q;B)|\ge \sigma\,|A_Q|
\tag{6.2}
\]
for every future current `Q>B`.  The numerical value of `\sigma` is theorem-level but never used as a selected packing witness.

# 7. Resource margin after neutral amplification

By (3.2) the ragged seed/bridge cover has a fixed open margin below `2`.  G1 lets us choose the neutral cube with arbitrarily small common total cost.  Hence there is a fixed
\[
\eta>0
\]
independent of the requested width function such that every wide-start branch satisfies
\[
W+\eta<2.
\tag{7.1}
\]

# 8. Exact theorem and quantifier order

Let
\[
\Phi(B)=B/\log B.
\]
The result proved above is
\[
\boxed{
\exists\eta>0\ \exists\sigma>0\ \forall L:\mathbf N_{\ge3}\to\mathbf N,
\quad L=o(\Phi)\Rightarrow
\exists B_0(L)\ \forall B\ge B_0(L),
\quad\exists WideStart(B,L).
}
\tag{8.1}
\]
Here `WideStart(B,L)` consists of a finite physical response covering one affine residue fibre times an integer interval of width at least `L(B)`, satisfying (6.2) and (7.1).

The order is essential.  `\eta` and `\sigma` are established before the downstream scalar theorem defines the particular startup request.  Only the onset cutoff `B_0` may depend on that request.  Therefore E4 contains no dependence on E5, E6, a Haxell packing point, or a first-hit horizon.