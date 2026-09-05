# E5–E6 — finite information channel, uniform profile, and sponsored final ray

This file is deliberately target/scalar only.  It does not choose a Haxell packing and does not assert physical union for an arbitrary dense subrow.  Physical realization is postponed to E7.

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

# 5. E289 dense-subrow specialization

Fix `ρ>0`.  For a late current `Q=p^e`, let `Surv(Q)` denote the row surviving E4.  Define the finite set
\[
\boxed{
Adm_\rho(Q)=\{A\subseteq Surv(Q): |A|\ge\rho Q/\log Q\}.}
\tag{5.1}
\]
No independence or packing datum is part of this definition.  It is a finite power-set fibre.  On the sufficiently late locus it is nonempty whenever `ρ` is below the uniform E4/E3 density constant.

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

# 6. Packing-independent finite extrema (E5)

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

For every dense subrow `A`, the same common profile is contained in its target rectangle:

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

This is a target-level theorem for all dense subrows.  When E7 later supplies an **independent** dense subrow by Haxell, the same rectangle is physically realizable using the corresponding actual atoms.

# 7. Scalar event system

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
\tag{7.1}
\]
There are at most
\[
O(\sqrt X\log X)
\]
prime powers `p^e≤X` with `e≥2` (sum the crude counts `X^{1/e}` over `2≤e≤\log_2X`).  Hence
\[
\boxed{
N(X)=O_\rho(\sqrt X\log^3X)=o(\Phi(X)).}
\tag{7.2}
\]

# 8. Earlier prime sponsors

Let `Λ` be the fixed G2 band constant.  For every sufficiently large current rank `Q`, apply G2 at `X=Q/Λ^2`.  The interval
\[
(Q/\Lambda^2,Q/\Lambda]
\]
contains a prime `q`.  This atomic current occurs earlier than `Q` and by (6.5) has mint
\[
m_\rho(q)\gg_\rho q/\log q
\asymp_{\Lambda,\rho} Q/\log Q
=\Theta(\Phi(Q)).
\tag{8.1}
\]
Thus every sufficiently late event has a bounded-multiplicative-lag earlier sponsor whose positive width increment is `\gg\Phi(Q)`.

# 9. Sponsored amortization (E6)

The exact general argument is short.  Let the WideStart theorem E4 supply arbitrary initial width requests `L(B)=o(\Phi(B))`.  Define
\[
R(B)=A(\Lambda B)+N(\Lambda B).
\tag{9.1}
\]
By (7.1),(7.2) and fixed-scale stability of `\Phi`,
\[
R(B)=o(\Phi(B)).
\]
Instantiate E4 with this particular request.

Events whose sponsor lies before the chosen start have rank at most `\Lambda B`; pessimistically discard all positive increments.  The initial reserve (9.1) covers both every demand and the entire negative variation in this finite transition.

After sponsors lie inside the post-start chain, for an event of rank `Q` retain only the positive increment of one sponsor and subtract all negative variation through `Q`:
\[
w(Q)\ge m_\rho(q)-N(Q).
\tag{9.2}
\]
By (8.1),(7.2),
\[
w(Q)\gg\Phi(Q),
\]
whereas the demand satisfies `a(Q)=o(\Phi(Q))` by (7.1).  Hence every sufficiently late event is legal.  Induction, together with the finite transition already covered by the startup reserve, proves legality of the whole post-start chain.

Successive integer intervals overlap.  Sponsor increments are unbounded because their ranks are cofinal and `\Phi(X)→∞`.  Therefore the union of the interval chain contains every sufficiently large integer.

Finally, the E4 neutral cube contributes one literal residue `\beta_B`.  All productive current responses after the start are internal to the endpoint filtration, so the centre at cutoff `X` is the image of `\beta_B` in `A/H_X`.  E1 cofinality gives a finite `X_abs` after which this centre is zero.  Since the scalar interval chain contains a final ray, for every sufficiently large `k` there is a first-hit horizon at or beyond `X_abs` whose grade interval contains `k` and whose centre is zero.

Thus
\[
\boxed{\exists k_0\ \forall k\ge k_0:\quad Term_k\ne\varnothing.}
\tag{9.3}
\]
No packing witness, conflict graph, physical resource sum, or n-ary multiplication witness is used in this scalar theorem.