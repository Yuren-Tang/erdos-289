# The twelve reviewer-facing statements

The machine-level R40 graph is compressed here to four generic inputs and eight E289-specific statements.  The review should reconstruct the public theorem through exactly these interfaces.

## Generic inputs

### G1. Remote grade-neutral switch
For every finite physical constraint and every positive reciprocal-mass budget there is, arbitrarily far out, a two-state physical switch `X_0 ↔ X_1` such that
\[
W(X_0)=W(X_1),\qquad g(X_1)=g(X_0)+1,
\]
both alternatives satisfy the given finite constraint, and their common reciprocal mass is below the budget.  Finitely many such switches can be constructed mutually compatible, producing a Boolean cube whose selector cardinality changes grade by exactly the number of high coordinates and changes neither reciprocal value nor residue.

### G2. Comparable prime bands
There are constants `Λ>1` and `c_Π,C_Π>0` such that eventually
\[
c_\Pi\frac X{\log X}
\le \#\{p:X<p\le\Lambda X\}
\le C_\Pi\frac X{\log X}.
\]

### G3. Restricted fixed-rank additive fold
Let `S` be a cyclic group of prime order `p`, `A⊂S` finite with `|A|=r`, and `0≤h≤r`.  For
\[
\Sigma_h:\operatorname{FinSub}_h(A)\to S,
\qquad O\mapsto\sum_{a\in O}a,
\]
one has
\[
|\operatorname{im}\Sigma_h|\ge\min\{p,h(r-h)+1\}.
\]
Hence `h(r-h)+1≥p` implies `Σ_h` is surjective.

### G4. Bounded-conflict quota thinning
A finite rowed graph of uniformly bounded maximum conflict degree admits a simultaneous independent thinning retaining a fixed positive fraction of every sufficiently large row.  This is the quota corollary of the standard Haxell independent-transversal theorem.

## E289-specific statements

### E1. Torsion filtration of `Q/Z`
For
\[
H_n=\{x\in\mathbf Q/\mathbf Z:nx=0\},\quad n\ge1,
\]
we have
\[
H_n=\langle[1/n]\rangle,\qquad |H_n|=n,
\]
\[
H_m\le H_n\iff m\mid n,
\qquad
H_m\vee H_n=H_{\operatorname{lcm}(m,n)}.
\]
The nonzero join-irreducible stages are exactly `H_{p^e}`.  If the current rank is `Q=p^e`, the simple factor `S_Q=F_Q/F_{<Q}` has order `p`, hence is canonically a one-dimensional `F_p`-object.  The endpoint stages
\[
H_X=H_{\operatorname{lcm}(1,\ldots,\lfloor X\rfloor)}
\]
are cofinal in `Q/Z`.

### E2. Physical decorated-relation calculus
Physical states are finite supports in the positive-integer path graph with all connected components of length `2` or `3`.  Compatible union is a partial commutative multiplication.  Reciprocal value `W`, grade `g` (number of components), and residue `res=W mod Z` are additive on compatible unions.

Finite right-total physically decorated relations form a category by pullback of composable labels, literal compatible union, then regular image.  Forgetting physical labels to `(res,g)` is normal oplax.  For a finite composable chain, if the ordinary string pullback `P_n` maps to `Phys^n` through the genuine n-ary multiplication domain `D_n`, the oplax comparison is an equality.  Reciprocal value supplies a subadditive filtration:
\[
\|S\circ R\|_W\le\|R\|_W+\|S\|_W.
\]

### E3. Total signed-inverse current supply
For every sufficiently late current `Q=p^e` there is a deterministic finite family `A_Q` of transverse binary atoms with:

1. `|A_Q| \asymp Q/log Q` on the late locus;
2. simple value in `S_Q` is nonzero and every simple-value fibre has cardinality at most `Q/p`;
3. distinguished centres are globally injective and the total conflict graph has uniformly bounded degree;
4. support lies in a controlled `Q^2`-scale window needed by future-footprint estimates;
5. a canonical row resource majorant `roleMass(Q)` is summable over all currents.

All carrier/sign/coefficient choices die inside this theorem.

### E4. Prepared wide affine start
There exist `η>0` and `σ>0` such that for every function `L(B)=o(B/log B)` there is `B_0(L)` for which every `B≥B_0(L)` admits a physical response covering one complete affine residue fibre over `H_B` times a grade interval of width at least `L(B)`, with every branch satisfying
\[
W\le2-\eta.
\]
For every future current, after deleting all preparatory obstacles, at least a `σ` fraction (in the `Q/log Q` scale) of the original signed-inverse row survives.

The construction is a finite seed plus universal fixed-grade bridge rows, followed by one G1 Boolean cube.  The ragged grade oscillation before the cube is bounded by the fixed finite seed oscillation, hence `O(1)`; the cube uses `O(L(B)+1)=o(B/log B)` physical coordinates.

The quantifier order is load-bearing:
\[
\exists\eta,\sigma>0\ \forall L=o(\Phi)\ \exists B_0(L)\ \forall B\ge B_0(L).
\]

### E5. Packing-independent local profile
Fix a sufficiently small theorem-level density `ρ>0`.  For each late current `J` define
\[
Adm_\rho(J)=\{A\subseteq Surv(J): |A|\ge \rho Q_J/\log Q_J\}.
\]
This is a finite family of dense subrows and contains no packing datum.

For every `A∈Adm_ρ(J)`, the finite occurrence channel
\[
\Gamma_A=
\left\{\left(\sum_{a\in O}sv_J(a),|O|\right):
O\subseteq A,\ |O|\le p_J\right\}
\subseteq S_J\times\mathbf N
\]
has a common horizontal rectangle after convolution with an incoming grade interval.  The proof is the image/fibre dichotomy: large simple-value image uses G3; small image forces a heavy nonzero fibre and yields a cyclic staircase.

Taking finite extrema over **all** `A∈Adm_ρ(J)` gives one packing-independent profile with
\[
d_\rho(Q)=O_\rho(\log^2 Q)\quad(Q\text{ composite}),
\]
and, for prime currents,
\[
d_\rho(q)=O_\rho(\log q),
\qquad
m_\rho(q)\gg_\rho q/\log q.
\]
The same profile is contained in every admissible row rectangle.

### E6. Sponsored final-ray theorem
Forget physical witnesses.  Prime event `q` acts on a grade interval by
\[
I\mapsto I+[d_q,d_q+m_q],
\]
whereas a composite event `Q` acts by
\[
[A,B]\mapsto[A+d_Q,B].
\]
The cumulative composite loss through `X` satisfies
\[
N(X)=\sum_{p^e\le X,\ e\ge2}d_\rho(p^e)
=O(\sqrt X\,\log^3X)=o(X/\log X).
\]
For every sufficiently late event `Q`, G2 supplies an earlier prime sponsor
\[
Q/\Lambda^2<q\le Q/\Lambda,
\]
whose mint is `\gg Q/log Q`.  Therefore all later demands remain legal and the supported grade intervals form a final ray.  Combining this with endpoint cofinality gives
\[
\exists k_0\ \forall k\ge k_0:\quad Term_k\ne\varnothing,
\]
where `Term_k` consists of target horizons with centre zero and grade interval containing `k`.

No actual Haxell packing is chosen in E6.

### E7. Finite-horizon physical realization
For a fixed first-hit horizon `X` from E6, only finitely many current rows are relevant.  Apply G4 once to those surviving rows.  The E4 survival modulus `σ` and the G4 quota modulus `ρ_P` give a fixed `ρ=σρ_P`, so every selected row projection belongs to the already-analysed `Adm_ρ(J)` of E5.

The selected global conflict-free atom pool yields the required genuine n-ary physical compatibility factorization through `D_n`, so E2 strictifies reachability and the local quotient rectangles paste as genuine physical covers.  E3 resource summability plus the open margin in E4 and E2 filtration give `W<2` on every realized branch.

Thus the realization projection is surjective:
\[
Real\twoheadrightarrow Horizon.
\]
No coherent infinite packing is asserted.

### E8. Terminal exactification and public Erdős 289
For every sufficiently large `k`, E6 gives `Term_k\ne\varnothing`.  Pull back the surjection `Real→Horizon` over `Term_k`, then pull back the universal final-edge cover along the canonical target section `(0,k)`.  Stability and composition of surjections give a literal physical state `S` with
\[
res(S)=0,\qquad g(S)=k,\qquad W(S)<2.
\]
Since `k>0`, the support is nonempty and `W(S)>0`.  The square
\[
\begin{CD}
Phys @>{W}>> \mathbf Q\\
@V{res}VV @VV{\bmod\mathbf Z}V\\
\mathbf Q/\mathbf Z @= \mathbf Q/\mathbf Z
\end{CD}
\]
shows `W(S)∈Z`; hence `0<W(S)<2` forces `W(S)=1`.  The component decomposition in E2 gives exactly `k` pairwise disjoint non-adjacent integer intervals, each of length `2` or `3`, proving Erdős Problem 289.

## Dependency order

The intended acyclic dependency skeleton is

\[
G1,G2,G3,G4,E1,E2\longrightarrow E3\longrightarrow E4\longrightarrow E5\longrightarrow E6,
\]

with the separate realization branch

\[
E2,E3,E4,E5,G4\longrightarrow E7,
\]

and the final merge

\[
E6,E7,E2\longrightarrow E8.
\]

More precise last-consumer information is in `06_DEPENDENCY_AND_REVIEW_CHECKLIST.md`.