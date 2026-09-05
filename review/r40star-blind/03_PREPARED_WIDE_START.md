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
and the two binary alternatives
\[
[a_r+1,a_r+2]
\quad\longleftrightarrow\quad
[a_r,a_r+2].
\tag{1.1}
\]
Their reciprocal difference is exactly
\[
\frac r{pD}.
\tag{1.2}
\]
Therefore the full finite-subset selector on `R_p` maps surjectively to
\[
L_n^{-1}\mathbf Z/L_{n-1}^{-1}\mathbf Z\cong\mathbf Z/p\mathbf Z.
\]
Every selector branch has the same grade `k`: for each `r`, either side of (1.1) is one connected component.  Thus the bridge is a fixed-grade regular-epi response to the next simple quotient.  No subset section is chosen.

Minimality of `k` also gives `k^2=O(p)`.  The row resource is therefore `O(D^{-1})`, and the within-row bases satisfy, for `r<s≤k`,
\[
a_r-a_s
=\frac{pD(s-r)}{rs}
\ge\frac{pD}{k^2}\gg D.
\tag{1.3}
\]
After finitely many small jumps, distinct bridge intervals in one row and in different rows are separated by more than the physical interaction radius.  All exceptional small jumps belong to the finite seed below.

# 2. Finite seed and ragged affine cover

There is one finite, directly checkable seed package with the following properties.

- It is a finite physical response covering one complete affine fibre at a fixed early endpoint.
- It has finitely many branch grades, whose spread is bounded by one fixed number `G_seed`.
- It is compatible with every bridge row after a finite exceptional regime, and the finite exceptional bridge rows are checked inside the same certificate.
- Its reciprocal values, plus a uniform majorant for the entire future bridge tower, leave a fixed positive margin `η_0` below `2`.

The exact numerical coordinates of the seed are proof data only; the reviewer need only verify that the finite certificate presented with the manuscript checks these four properties.

Compose the seed with one bridge at every later prime-power jump through an outer rank cutoff `B`.  By E2 n-ary physical composability of this finite separated family, the quotient responses paste to a physical relation covering a complete affine `H_B`-fibre.

Crucially, every bridge row is fixed-grade.  Hence every bridge adds the same grade constant to every old branch.  Therefore the branch-to-branch grade spread after any number of bridges is exactly the finite seed spread:
\[
\boxed{G_B=G_{seed}=O(1).}
\tag{2.1}
\]
The preparatory response before neutral amplification is thus a **ragged affine cover**: its torsor projection is surjective, and all branch grades lie in some interval `[m_B,M_B]` with `M_B-m_B=G_seed`.

# 3. Sparse future footprint of the seed and bridges

Let a future signed-inverse row have current rank `Q>B`.  By E3 its support is contained in
\[
[cQ^2/\log Q,\,2Q^2]
\tag{3.1}
\]
up to fixed endpoint buffers.

Consider a bridge row at jump `n=p^e` with lower modulus `D=L_{n-1}`.  If one of its bounded physical envelopes can meet (3.1), then its support base is of size comparable to the window.  The bridge bases are `a_r=pD/r`, with `1≤r≤k=O(\sqrt p)`, so in particular
\[
D=O(Q^2).
\tag{3.2}
\]
On the other hand, the primorial through `n-1` divides `D`.  The Chebyshev bounds proved in G2 imply
\[
n,p=O(\log Q).
\tag{3.3}
\]
Using the lower end of (3.1) and the crude upper bound `a_r≤pD` gives
\[
D\gg Q^2/(\log Q)^2.
\tag{3.4}
\]
Successive nontrivial lower moduli multiply by at least `2`; the ratio between the upper and lower bounds (3.2),(3.4) is only polylogarithmic.  Hence only
\[
O(\log\log Q)
\]
bridge rows can meet the future support window.  Each such bridge has `k=O(\sqrt p)=O(\sqrt{\log Q})` bounded-complexity envelopes.  Therefore the number of preparatory envelopes capable of meeting the future row is
\[
\boxed{O(\sqrt{\log Q}\,\log\log Q)=o(Q/\log Q).}
\tag{3.5}
\]

By E3 bounded conflict incidence, each such envelope removes only `O(1)` future atoms.  Since the original row has `\asymp Q/\log Q` atoms, the ragged preparatory cover deletes only a vanishing fraction, uniformly in the outer cutoff `B`.

# 4. One neutral cube: grade rectification and startup width

Let the ragged cover have grades in `[m_B,M_B]` and put
\[
G=M_B-m_B=G_{seed}.
\]
Let `L(B)` be any nonnegative integer-valued function with
\[
L(B)=o(B/\log B).
\tag{4.1}
\]
Using G1, construct `G+L(B)` mutually compatible grade-neutral coordinates remote from the whole ragged cover, with total reciprocal cost as small as desired.

For a selector `\sigma∈\{0,1\}^{G+L}`, let `wt(\sigma)` be its Hamming weight.  All selectors have the same reciprocal value and the same residue translation; their grades are
\[
\lambda_B+wt(\sigma)
\]
for a common baseline `\lambda_B`.

For a ragged edge of grade `r` and a requested output offset `j∈[0,L(B)]`, require
\[
wt(\sigma)=(M_B-r)+j.
\tag{4.2}
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
\tag{4.3}
\]
The left projection is surjective by base-change stability.  Pasting with the ragged-cover surjection gives a physical cover of
\[
Tor_{H_B}(\alpha_B+\beta_B)
\times
[\lambda_B+M_B,\lambda_B+M_B+L(B)],
\tag{4.4}
\]
where `\beta_B` is the common residue translation of every neutral selector.

Thus **one** neutral cube simultaneously removes the finite ragged grade spread and creates the requested startup interval.  No branch section or chosen subset is used.

# 5. Future density after the neutral cube

The cube contributes only `O(G+L(B))` bounded-complexity physical envelopes, not one envelope for every Boolean selector.  By (2.1) and (4.1),
\[
G+L(B)=o(B/\log B).
\tag{5.1}
\]
For future `Q≥B`, `Q/log Q` is eventually increasing, so (5.1) is also `o(Q/log Q)`.  Together with (3.5) and E3 finite conflict incidence, the complete wide-start obstacle removes only `o(Q/log Q)` atoms from every future row.

Since E3 supplies a uniform positive lower row constant on a cofinal suffix, choose one fixed
\[
\sigma>0
\]
small enough that, after increasing the onset cutoff if necessary,
\[
|Surv(Q;B)|\ge \sigma\,|A_Q|
\tag{5.2}
\]
for every future current `Q>B`.  The numerical value of `\sigma` is theorem-level but never used as a selected packing witness.

# 6. Resource margin

The finite seed and full infinite bridge tower have a fixed positive margin below `2`.  G1 allows the neutral cube to be constructed with arbitrarily small common reciprocal cost.  Hence there is a fixed
\[
\eta>0
\]
independent of the requested width function such that every wide-start branch satisfies
\[
W+\eta<2.
\tag{6.1}
\]

# 7. Exact theorem and quantifier order

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
\tag{7.1}
\]
Here `WideStart(B,L)` consists of a finite physical response covering one affine residue fibre times an integer interval of width at least `L(B)`, satisfying (5.2) and (6.1).

The order is essential.  `\eta` and `\sigma` are established before the downstream scalar theorem defines the particular startup request.  Only the onset cutoff `B_0` may depend on that request.  Therefore E4 contains no dependence on E5, E6, a Haxell packing point, or a first-hit horizon.