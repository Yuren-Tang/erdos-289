# E5–E6 — universal finite channel profile and sponsored final ray

This file is deliberately target/scalar only.  E5 is now completely independent of a selected WideStart witness: it analyses **all sufficiently dense subrows of the original E3 row**.  E6 uses that universal profile to choose the startup request, and only afterwards is one E4 WideStart witness selected.  No actual Haxell packing is chosen here.

# 1. Finite occurrence channel

Let `S` be a cyclic group of prime order `p`, let `A` be a finite occurrence set, and let
\[
f:A\to S^\times
\]
be the simple-value map.  Define the cardinality-graded subset-sum support
\[
\Gamma_f=
\left\{\left(\sum_{x\in O}f(x),|O|\right):
O\subseteq A,\ |O|\le p\right\}
\subseteq S\times\mathbf N.
\tag{1.1}
\]
For an incoming integer interval `I`, the target-level response support is
\[
\Gamma_f+(\{0\}\times I).
\tag{1.2}
\]

## 1.1 No-section occurrence lift

Put `B=im(f)`, `r=|B|`.  For `0≤h≤r`, let `Sub_h(B)` be the set of `h`-element subsets of `B`, and define
\[
Lift_h(f)=\{(C,u): C\in Sub_h(B),\ u:C\to A,\ f(u(c))=c\ \forall c\in C\}.
\]
Distinct `c` force `u` to be injective.  Every fibre of
\[
Lift_h(f)\to Sub_h(B)
\]
is a finite product of nonempty occurrence fibres, hence is nonempty.  Therefore this projection is surjective.  This realizes distinct simple values by distinct occurrences without selecting a section `B→A`.

# 2. Diversity branch

Define
\[
I_D(p,r)=\{h: h(r-h)+1\ge p\}.
\]
By G3, for every `h∈I_D(p,r)`, the sums of the `h`-element subsets of `B` fill `S`.  Pasting with the occurrence lift gives
\[
\boxed{S\times I_D(p,r)\subseteq\Gamma_f.}
\tag{2.1}
\]

If `I_D` is nonempty and `a=min I_D`, symmetry and unimodality of `h(r-h)` give
\[
I_D=[a,r-a]\cap\mathbf N.
\]
Also
\[
a<2p/r+1.
\tag{2.2}
\]
Indeed, for `h=\lceil2p/r\rceil`, once `h≤r/2`,
\[
h(r-h)\ge hr/2\ge p.
\]
Consequently, for every incoming interval `[A_0,B_0]`,
\[
\boxed{
S\times[A_0+a,B_0+r-a]
\subseteq
\Gamma_f+(\{0\}\times[A_0,B_0]).}
\tag{2.3}
\]

# 3. Redundancy branch

Suppose some nonzero `c∈S` has at least `p-1` preimages.  Work with the full finite solution set of `(p-1)`-element subsets of `f^{-1}(c)`, not with a distinguished chosen subset.  For each `0≤j<p`, its `j`-element subobjects give
\[
(jc,j)\in\Gamma_f.
\tag{3.1}
\]
Since `c≠0`, the map `j↦jc` for `0≤j<p` runs through all of `S`.

After convolution with `[A_0,B_0]`, the residue `jc` is available in grades `[A_0+j,B_0+j]`.  The intersection over all `j` is
\[
[A_0+p-1,B_0].
\]
Hence, whenever the incoming width is at least `p-1`,
\[
\boxed{
S\times[A_0+p-1,B_0]
\subseteq
\Gamma_f+(\{0\}\times[A_0,B_0]).}
\tag{3.2}
\]

# 4. Information balance

If
\[
M=\max_{s\in S}|f^{-1}(s)|,
\]
then trivially
\[
\boxed{|A|\le |im(f)|\,M=rM.}
\tag{4.1}
\]
Thus a channel with small output diversity necessarily has a heavy occurrence fibre.  Sections 2 and 3 are different constructions and are identified only at the common rectangle property (2.3)/(3.2).

# 5. Universal E289 dense-subrow specialization

Let `A_Q^{orig}` be the original deterministic E3 row at the late current `Q=p^e`.  Fix `ρ>0` and define
\[
\boxed{
Adm_\rho(Q)=\{A\subseteq A_Q^{orig}: |A|\ge\rho Q/\log Q\}.}
\tag{5.1}
\]
This definition contains no WideStart witness, survivor set, conflict graph, or packing datum.  It is a finite power-set fibre of the original E3 row.  Whenever `ρ` is below the E3 lower row constant, it is nonempty on a cofinal suffix.

For any `A∈Adm_ρ(Q)`, restrict the E3 simple-value map to `A`.  The exact fibre bound `M≤Q/p` and (4.1) give
\[
r:=|im(f)|
\ge\frac{|A|}{Q/p}
\gg_\rho\frac p{\log Q}.
\tag{5.2}
\]

## 5.1 Image-rich rows
If `I_D(p,r)` is nonempty, let `a(A)=min I_D`.  From (2.2),(5.2),
\[
\boxed{a(A)=O_\rho(\log Q).}
\tag{5.3}
\]
The target rectangle is (2.3).

## 5.2 Image-poor rows
If `I_D(p,r)` is empty, then `r^2<4p`.  Combining with (5.2),
\[
\boxed{p=O_\rho((\log Q)^2).}
\tag{5.4}
\]
By (4.1), some nonzero simple value has fibre size at least
\[
|A|/r
\gg_\rho \frac{Q}{\sqrt p\,\log Q}.
\tag{5.5}
\]
For a composite current `Q=p^e`, `e≥2`, one has `p≤\sqrt Q`; the right side of (5.5) is therefore `\gg p` uniformly at late rank.  In particular it is at least `p-1`, so the redundancy rectangle (3.2) applies.  Its demand is `p-1=O_ρ((\log Q)^2)` by (5.4).

For a prime current `Q=q`, E3 gives fibre capacity `Q/p=1`; hence `f` is injective, so only the image-rich branch occurs.  Then
\[
r=|A|\gg_\rho q/\log q,
\qquad
a(A)=O_\rho(\log q).
\tag{5.6}
\]

# 6. WideStart-independent finite extrema (E5)

For `A∈Adm_ρ(Q)` define the route demand
\[
\delta(Q,A)=
\begin{cases}
a(A),&\text{image-rich},\\p-1,&\text{image-poor}.
\end{cases}
\]
On the late locus `Adm_ρ(Q)` is finite and nonempty.  Define
\[
\boxed{d_\rho(Q)=\max_{A\in Adm_\rho(Q)}\delta(Q,A).}
\tag{6.1}
\]
The uniform estimates above give
\[
\boxed{d_\rho(Q)=O_\rho((\log Q)^2)}
\tag{6.2}
\]
for every current; on prime currents, where the poor branch is impossible,
\[
\boxed{d_\rho(q)=O_\rho(\log q).}
\tag{6.3}
\]

For a prime current define, **after** (6.1),
\[
\boxed{
m_\rho(q)=
\min_{A\in Adm_\rho(q)}
\bigl(r_A-a(A)-d_\rho(q)\bigr).
}
\tag{6.4}
\]
By (5.6),(6.3), every term in the minimum is `\gg_ρ q/\log q`, hence
\[
\boxed{m_\rho(q)\gg_\rho q/\log q.}
\tag{6.5}
\]

For every `A∈Adm_ρ(Q)`, the same common profile is contained in its target rectangle:

- if `Q` is composite and the incoming interval is `[A_0,B_0]` with width at least `d_ρ(Q)`, then
  \[
  S_Q\times[A_0+d_\rho(Q),B_0]
  \]
  lies in (1.2);
- if `Q=q` is prime, then
  \[
  S_q\times[A_0+d_\rho(q),B_0+d_\rho(q)+m_\rho(q)]
  \]
  lies in (1.2).

Thus E5 is independent not only of the Haxell packing but also of the selected E4 WideStart witness.  E7 will later show that its actual packed row is one point of this already-fixed universal admissible family.

# 7. Fix the theorem-level density before the startup request

Let `κ>0` be the late E3 lower row constant, let `σ>0` be the uniform survivor fraction supplied by the **statement** of E4, and let `ρ_P>0` be the fixed quota fraction supplied by G4 for the E3 conflict-degree bound.  These three constants are fixed before any WideStart witness is selected.  Choose once and for all
\[
\boxed{0<\rho<\kappa\sigma\rho_P.}
\tag{7.1}
\]
Apply Sections 5–6 with this `ρ`.  The resulting functions `d_ρ,m_ρ` are now fixed independently of every future WideStart witness.

# 8. Scalar event system

Enumerate currents by strictly increasing rank and let `x_n=Q_n`.  Associate to event `n` an interval action
\[
[A,B]\mapsto[A+a_n,B+b_n].
\]
For a prime event `q`, take
\[
a_n=d_\rho(q),
\qquad
b_n=d_\rho(q)+m_\rho(q),
\]
so the width increment is
\[
\chi_n=m_\rho(q)>0.
\]
For a composite event `Q`, take
\[
a_n=d_\rho(Q),\qquad b_n=0,
\]
so
\[
\chi_n=-d_\rho(Q).
\]
The action is legal when the incoming width is at least `a_n`; a legal output interval overlaps its predecessor because its new lower endpoint does not pass the old upper endpoint.

Put
\[
\Phi(X)=X/\log X.
\]
Define
\[
A(X)=\max_{Q_n\le X}a_n,
\]
and cumulative negative variation
\[
N(X)=\sum_{Q_n\le X}\max(-\chi_n,0)
=\sum_{p^e\le X,\ e\ge2}d_\rho(p^e).
\]
By (6.2),
\[
A(X)=O_\rho((\log X)^2)=o(\Phi(X)).
\tag{8.1}
\]
There are at most
\[
O(\sqrt X\log X)
\]
prime powers `p^e≤X` with `e≥2`, hence
\[
\boxed{
N(X)=O_\rho(\sqrt X\log^3X)=o(\Phi(X)).}
\tag{8.2}
\]

# 9. Earlier prime sponsors

Let `Λ` be the fixed G2 band constant.  For every sufficiently large current rank `Q`, apply G2 at `X=Q/Λ^2`.  The interval
\[
(Q/\Lambda^2,Q/\Lambda]
\]
contains a prime `q`.  This atomic current occurs earlier than `Q` and by (6.5) has mint
\[
m_\rho(q)\gg_\rho q/\log q
\asymp_{\Lambda,\rho} Q/\log Q
=\Theta(\Phi(Q)).
\tag{9.1}
\]
Thus every sufficiently late event has a bounded-multiplicative-lag earlier sponsor whose positive width increment is `\gg\Phi(Q)`.

# 10. Sponsored amortization with the corrected transition scale (E6)

Define the startup request
\[
\boxed{R(B)=A(\Lambda^2 B)+N(\Lambda^2 B).}
\tag{10.1}
\]
By (8.1),(8.2) and fixed-scale stability of `\Phi`,
\[
R(B)=o(\Phi(B)).
\tag{10.2}
\]
This request was defined from the universal E5 profile, before any E4 WideStart witness is selected.

E4 therefore supplies an onset `B_0(R)` for this request.  The scalar proof remains valid if we impose any additional prescribed lower bound `B_†`: choose
\[
B\ge\max\{B_0(R),B_†,B_{scalar}\},
\tag{10.3}
\]
where `B_scalar` is a fixed onset after which the E5 estimates and sponsor theorem hold.  Only now choose one WideStart witness `W_B` at base `B` and request `R`.  Let its initial grade interval be `I_B`, whose width is at least `R(B)`.

Events whose sponsor lies at or before the start satisfy
\[
q\le B,\qquad q>Q/\Lambda^2,
\]
so necessarily
\[
Q<\Lambda^2B.
\tag{10.4}
\]
Pessimistically discard all positive increments during this transition.  The reserve (10.1) covers every demand through `\Lambda^2B` and all cumulative negative variation there, so the scalar recursion is legal throughout the transition.

For every later event `Q>\Lambda^2B`, the sponsor from Section 9 satisfies `q>B` and lies inside the post-start chain.  Retaining only the positive increment of one sponsor and subtracting all negative variation through `Q` gives
\[
w(Q)\ge m_\rho(q)-N(Q).
\tag{10.5}
\]
By (9.1),(8.2),
\[
w(Q)\gg\Phi(Q),
\]
whereas the demand satisfies `a(Q)=o(\Phi(Q))` by (8.1).  Hence every sufficiently late event is legal.  Together with the transition argument, induction proves legality of the whole post-start chain.

Successive integer intervals overlap.  Sponsor increments are unbounded because their ranks are cofinal and `\Phi(X)→∞`.  Therefore the union of the interval chain contains every sufficiently large integer.

# 11. Carry the full WideStart centre

The chosen WideStart witness `W_B` covers an affine fibre
\[
Tor_{H_B}(\gamma_B),
\qquad
\boxed{\gamma_B:=\alpha_B+\beta_B},
\tag{11.1}
\]
where `\alpha_B` is the ragged Prefix centre and `\beta_B` is the common neutral-cube translation.  Productive current responses transport the image of this same fixed class through the endpoint filtration; they do not delete `\alpha_B`.

By E1 cofinality, the torsion class `\gamma_B∈(\mathbf Q/\mathbf Z)/H_B` is killed after a finite endpoint cutoff: there exists `X_abs≥B` such that its image in `(\mathbf Q/\mathbf Z)/H_X` is zero for every `X≥X_abs`.

The scalar interval chain is a final ray and remains so after discarding any finite initial segment.  Hence for every sufficiently large grade `k` there is a first-hit horizon `X≥X_abs` whose grade interval contains `k` and whose transported centre is zero.  Thus
\[
\boxed{\exists k_0\ \forall k\ge k_0:\quad Term_k\ne\varnothing.}
\tag{11.2}
\]
No packing witness, conflict graph, physical resource sum, or n-ary multiplication witness is used in this scalar theorem.

# 12. Quantifier order after repair

The load-bearing order is now explicit:

1. E3 fixes the original rows and `κ`; E4 proves uniform theorem-level `η,σ`; G4 fixes `ρ_P`.
2. Fix `ρ<κσρ_P`.
3. E5 takes extrema over **all `ρ`-dense subrows of the original E3 rows**, producing `d_ρ,m_ρ` independently of any WideStart witness.
4. E6 defines `R(B)` from this universal profile.
5. Choose `B` past the E4 onset for `R` and any additional prescribed lower bound `B_†`.
6. Only now select one WideStart witness `W_B`; it determines `Surv_{W_B}` and the full centre `γ_B=α_B+β_B`.
7. Run the scalar first-hit construction using the already-fixed universal profile.
8. E7 finally chooses one finite Haxell packing inside `Surv_{W_B}` and checks that its row projections belong to the already-analysed universal `Adm_ρ`.

Thus neither the profile nor the startup request depends on the selected WideStart witness.