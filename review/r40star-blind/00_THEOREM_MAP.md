# The twelve reviewer-facing statements — repaired quantifier normal form

This review surface contains four generic inputs and eight E289-specific statements.  The repaired form makes the local profile independent of both the Haxell packing **and the selected WideStart witness**.

## Generic inputs

### G1. Remote grade-neutral switch
For every finite physical constraint and every positive reciprocal-mass budget there is, arbitrarily far out, a two-state physical switch `X_0 ↔ X_1` such that
\[
W(X_0)=W(X_1),\qquad g(X_1)=g(X_0)+1,
\]
both alternatives satisfy the constraint, and their common reciprocal mass is below the budget.  Finitely many such switches may be chosen mutually compatible, producing a Boolean cube whose Hamming weight changes grade and changes neither reciprocal value nor residue.

### G2. Comparable prime bands
There are constants `Λ>1` and `c_Π,C_Π>0` such that eventually
\[
c_\Pi X/\log X\le \#\{p:X<p\le\Lambda X\}\le C_\Pi X/\log X.
\]

### G3. Restricted fixed-rank additive fold
If `S` is cyclic of prime order `p`, `A⊂S`, `|A|=r`, then the `h`-element subset-sum map satisfies
\[
|\operatorname{im}\Sigma_h|\ge\min\{p,h(r-h)+1\}.
\]
Hence `h(r-h)+1≥p` implies surjectivity.

### G4. Bounded-conflict quota thinning
A finite rowed graph of uniformly bounded maximum conflict degree admits a simultaneous independent thinning retaining a fixed positive fraction of every sufficiently large row.  This is the quota corollary of the standard Haxell independent-transversal theorem.

## E289-specific statements

### E1. Torsion filtration of `Q/Z`
For `H_n={x∈Q/Z:nx=0}`,
\[
H_n=\langle[1/n]\rangle,\quad |H_n|=n,
\quad H_m\le H_n\iff m\mid n,
\quad H_m\vee H_n=H_{\operatorname{lcm}(m,n)}.
\]
The nonzero join-irreducibles are exactly the prime powers `p^e`; the simple factor at current `Q=p^e` has order `p`; and
\[
H_X=H_{\operatorname{lcm}(1,\ldots,\lfloor X\rfloor)}
\]
is cofinal in `Q/Z`.

### E2. Physical decorated-relation calculus
Physical states are finite supports whose connected components have length `2` or `3`.  Compatible union is partial commutative multiplication; `W`, grade `g`, and `res=W mod Z` are additive.  Finite right-total physically decorated relations compose by pullback, literal compatible union, then regular image.  If the ordinary finite string pullback factors through the genuine n-ary multiplication domain `D_n`, the oplax target shadow strictifies.  Reciprocal value is subadditive under composition.

### E3. Total signed-inverse current supply
For every sufficiently late current `Q=p^e` there is a deterministic original row `A_Q^{orig}` of transverse binary atoms such that:

1. `|A_Q^{orig}|≥κ Q/log Q` for one fixed late-locus `κ>0` (and a matching `O(Q/log Q)` upper bound);
2. every simple-value fibre has size at most `Q/p`;
3. distinguished centres are globally injective and the conflict graph has uniformly bounded degree;
4. support lies in the controlled `Q^2`-scale window needed by E4;
5. a canonical row resource majorant `roleMass(Q)` is summable.

### E4. Prepared wide affine start
There exist theorem-level `η>0` and `σ>0` such that for every `L(B)=o(B/log B)` there is `B_0(L)` so that every `B≥B_0(L)` admits a physical response covering one affine `H_B`-fibre times an integer interval of width at least `L(B)`, with `W+η<2` on every branch.  If this witness is called `W_B`, then for every future current
\[
|Surv_{W_B}(Q)|\ge\sigma |A_Q^{orig}|.
\]
The witness covers `Tor_{H_B}(α_B+β_B)`; the full centre `α_B+β_B` must be carried downstream.

The quantifier order is
\[
\exists\eta,\sigma\ \forall L=o(\Phi)\ \exists B_0(L)\ \forall B\ge B_0(L)\ \exists W_B.
\]

### E5. WideStart-independent local profile
Fix `ρ>0`.  For each late current define
\[
\boxed{Adm_\rho(Q)=\{A\subseteq A_Q^{orig}:|A|\ge\rho Q/\log Q\}.}
\]
This family is defined on the original E3 row and contains **no WideStart witness, survivor set, conflict graph, or packing datum**.

For every `A∈Adm_ρ(Q)`, the finite simple-factor channel has a common horizontal rectangle after convolution with an incoming grade interval.  The proof is the diversity/redundancy dichotomy using E3's exact fibre bound and G3.  Finite extrema over all `A∈Adm_ρ(Q)` give one universal profile
\[
d_\rho(Q)=O_\rho(\log^2Q),
\]
and, for prime currents,
\[
d_\rho(q)=O_\rho(\log q),\qquad m_\rho(q)\gg_\rho q/\log q.
\]

Let `ρ_P` be the fixed G4 quota fraction.  After E4 has supplied theorem-level `σ`, choose once and for all
\[
0<\rho<\kappa\sigma\rho_P.
\]
This fixes `d_ρ,m_ρ` before any WideStart witness is selected.

### E6. Sponsored final-ray theorem
From the universal E5 profile define prime mint/composite debt and
\[
A(X)=\max_{Q\le X}a_Q,
\qquad
N(X)=\sum_{p^e\le X,e\ge2}d_\rho(p^e),
\]
with
\[
A(X)=o(X/\log X),\qquad N(X)=O(\sqrt X\log^3X)=o(X/\log X).
\]
For every late event `Q`, G2 gives an earlier prime sponsor
\[
Q/\Lambda^2<q\le Q/\Lambda
\]
with mint `\gg Q/log Q`.

Define the startup request
\[
\boxed{R(B)=A(\Lambda^2B)+N(\Lambda^2B)=o(B/\log B).}
\]
E4 is instantiated with this request **after** the universal profile is fixed.  The construction permits any additional prescribed lower bound `B_†` on the start.  Events whose sponsor lies before the start have rank `<Λ^2B`, so the corrected reserve covers the complete transition.

For the selected WideStart carry the full centre
\[
\gamma_B=\alpha_B+\beta_B.
\]
E1 cofinality eventually kills `γ_B`; the legal overlapping interval chain is a final ray.  Hence
\[
\exists k_0\ \forall k\ge k_0:\quad Term_k\ne\varnothing.
\]
No packing witness is chosen in E6.

### E7. Finite-horizon physical realization
Before invoking E6 in the global proof, use E3 resource summability and the E4 theorem-level margin `η` to fix a threshold `B_res` with
\[
\sum_{Q>B_{res}}roleMass(Q)<\eta.
\]
Run E6 with its arbitrary lower-bound parameter `B_†=B_res`; thus the WideStart base is resource-small **before** any first-hit horizon is chosen.

For a fixed finite horizon `X`, apply G4 once to the survivor rows.  Every packed row satisfies
\[
|Pack(Q)|\ge\kappa\sigma\rho_P Q/\log Q>\rho Q/\log Q,
\]
so it is a point of the already-analysed **original-row** `Adm_ρ(Q)`.  The globally independent pool and complete WideStart deletion give genuine n-ary compatibility; E2 strictifies the target channel.  E3 resource summability gives `W<2`.  Therefore
\[
Real\twoheadrightarrow Horizon.
\]

### E8. Terminal exactification and public Erdős 289
For sufficiently large `k`, E6 gives `Term_k≠∅`.  Pull `Real→Horizon` back over `Term_k`, then pull the universal edge cover back along the canonical target `(0,k)`.  Obtain a physical state `S` with
\[
res(S)=0,\qquad g(S)=k,\qquad W(S)<2.
\]
Since `k>0`, `W(S)>0`; residue zero implies `W(S)∈Z`; hence `W(S)=1`.  The components are exactly `k` pairwise disjoint non-adjacent intervals of lengths `2` or `3`.

## Corrected dependency order

The key repair is that E5 no longer depends on a selected E4 witness:
\[
E1,G2\to E3,
\qquad
E1,E2,E3,G1,G2\to E4,
\qquad
E1,E3,G3\to E5.
\]
The scalar branch is
\[
E4_{\text{theorem-level }\eta,\sigma},E5,G2\to E6,
\]
and the physical branch is
\[
E2,E3,E4,E5,G4\to E7.
\]
Finally
\[
E1,E2,E6,E7\to E8.
\]
The detailed quantifier and last-consumer audit is in `06_DEPENDENCY_AND_REVIEW_CHECKLIST.md`.