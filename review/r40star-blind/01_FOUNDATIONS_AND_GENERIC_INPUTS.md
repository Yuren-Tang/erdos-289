# Foundations and generic inputs

This file supplies E1, E2 and G1–G4 in a form intended to be checked without consulting Lean or earlier E289 packets.

# 1. Physical states and observations (E2, concrete part)

A **physical state** is a finite subset `S⊂N_{>0}` such that every connected component of the induced path graph is an interval of length `2` or `3`.  Distinct components are therefore separated by at least one unused integer.

Two states are **compatible** if they are disjoint and their union is again a physical state.  Compatible union is a partial commutative multiplication.  Write
\[
W(S)=\sum_{n\in S}\frac1n,
\qquad
g(S)=|\pi_0(S)|,
\qquad
res(S)=W(S)\bmod\mathbf Z\in A:=\mathbf Q/\mathbf Z.
\]
For a compatible finite tuple `(S_i)`, connected components do not merge, hence
\[
W\Bigl(\bigsqcup_iS_i\Bigr)=\sum_iW(S_i),
\qquad
g\Bigl(\bigsqcup_iS_i\Bigr)=\sum_i g(S_i),
\qquad
res\Bigl(\bigsqcup_iS_i\Bigr)=\sum_i res(S_i).
\]

If a nonempty physical state has grade `k`, it has exactly `k` pairwise disjoint, non-adjacent integer intervals, each of length `2` or `3`.

# 2. Torsion filtration of `Q/Z` (E1)

For `n≥1` define
\[
H_n:=\{x\in A:nx=0\}.
\]

## Lemma 2.1
\[
H_n=\langle[1/n]\rangle,
\qquad |H_n|=n.
\]

**Proof.**  If `[q]∈H_n`, then `nq∈Z`, so `q=j/n` modulo `Z` for some integer `j`.  Conversely every `[j/n]` is killed by `n`.  The classes
`0,1/n,…,(n-1)/n` are distinct modulo `Z`. ∎

## Lemma 2.2
For positive `m,n`,
\[
H_m\le H_n\iff m\mid n.
\]

**Proof.**  If `m|n`, every element killed by `m` is killed by `n`.  Conversely, if `H_m≤H_n`, then `[1/m]∈H_n`, so `n/m∈Z`. ∎

## Lemma 2.3
\[
H_m\vee H_n=H_{\operatorname{lcm}(m,n)}.
\]

**Proof.**  Put `L=lcm(m,n)`.  Lemma 2.2 gives `H_m,H_n≤H_L`.  Since
\[
\gcd(L/m,L/n)=1,
\]
choose integers `a,b` with `aL/m+bL/n=1`.  Dividing by `L`,
\[
1/L=a/m+b/n,
\]
so `[1/L]∈H_m+H_n`.  Lemma 2.1 gives the reverse inclusion. ∎

Thus the finite subgroup lattice of `A` is identified with positive integers ordered by divisibility, with join `lcm`.

## Lemma 2.4 — currents are prime powers
A nontrivial `n` is join-irreducible in the divisibility/lcm lattice iff
\[
n=p^e
\]
for a prime `p` and `e≥1`.

**Proof.**  If `n` has at least two distinct prime factors, split its prime-power factors into two proper divisors `a,b`; then `n=lcm(a,b)`.  If `n=p^e`, every divisor is `p^i`, and
`lcm(p^i,p^j)=p^{max(i,j)}=p^e` forces `i=e` or `j=e`. ∎

We call the stage of rank `Q=p^e` a **current**.

For a current `Q=p^e`, let `F_{<Q}` be the join of all lower-rank currents and put `F_Q=F_{<Q}\vee H_Q`.  Let `L_{<Q}` be the integer whose torsion subgroup is `F_{<Q}`.  Its `p`-adic valuation is exactly `e-1`: the lower current `p^{e-1}` is present (when `e>1`) but `p^e` is not, while all other lower currents contribute only their own prime factors.  Therefore
\[
\operatorname{lcm}(L_{<Q},p^e)=pL_{<Q}.
\]
By Lemma 2.1,
\[
|F_Q/F_{<Q}|=\frac{pL_{<Q}}{L_{<Q}}=p.
\]
Hence the **simple factor**
\[
S_Q:=F_Q/F_{<Q}
\]
is cyclic of prime order `p`, equivalently a one-dimensional vector object over `F_p`.

Finally define the endpoint
\[
H_X:=\bigvee_{p^e\le X}H_{p^e}.
\]
The prime powers `≤X` generate exactly
\[
H_X=H_{\operatorname{lcm}(1,\ldots,\lfloor X\rfloor)}.
\]
Every `[a/b]∈A` belongs to `H_b`, hence to `H_X` for `X≥b`.  Thus the endpoint filtration is cofinal in `A`.

# 3. Decorated finite relations and strictification (E2, categorical part)

Let `T,T'` be finite target sets.  A **physical response** from `T` to `T'` is a finite relation
\[
R\subseteq T\times Phys\times T'
\]
whose projection `R→T'` is surjective and whose labels obey the target observation equation appropriate to the application.  The crucial point is that the physical witness is retained until composition is certified.

Given `R:T_0⇝T_1` and `S:T_1⇝T_2`, form the ordinary pullback over `T_1`.  Restrict to pairs whose physical labels are compatible, map them by literal union to `Phys`, and take the regular image in `T_0×Phys×T_2`.  Associativity and identities follow from associativity of finite fibre products, associativity of compatible finite union, and idempotence of taking the extensional image.  Thus these finite decorated relations form a category.

Let
\[
Reach(R)\subseteq T\times T'
\]
be the label-forgetting relation.  Forgetting labels is in general only oplax under composition because an ordinary composable tuple of reachable edges need not have mutually compatible physical witnesses.

For a finite chain `R_0,…,R_{n-1}`, let `P_n` be the ordinary string pullback of the edge relations, and let `D_n⊂Phys^n` be the genuine domain on which the n-ary physical union exists.  If the physical tuple map from `P_n` factors through `D_n`, then every ordinary composable tuple is physically composable; hence the canonical inclusion
\[
Reach(R_{n-1}\circ\cdots\circ R_0)
\subseteq
Reach(R_{n-1})\circ\cdots\circ Reach(R_0)
\]
is an equality.  This is the only strictification principle used later.

For a finite response `R`, define
\[
\|R\|_W:=\sup\{W(s): (\_,s,\_)\in R\}.
\]
Compatible additivity of `W` gives
\[
\|S\circ R\|_W\le\|R\|_W+\|S\|_W.
\]
This filtration is consumed when a finite horizon is physically realized.

# 4. G1 — remote grade-neutral switches

Put
\[
P(a)=\frac1a+\frac1{a+1}.
\]
For every positive integer `a`,
\[
\boxed{
P(a)+P(a^2+3a+1)
=
P(a+2)+P\!\left(\frac{a(a+3)}2\right)+P(a(a+3)).
}
\tag{N}
\]
Indeed
\[
P(a)-P(a+2)
=\frac1a+\frac1{a+1}-\frac1{a+2}-\frac1{a+3},
\]
and reduction to the common denominator `a(a+1)(a+2)(a+3)` equals
\[
P\!\left(\frac{a(a+3)}2\right)+P(a(a+3))-P(a^2+3a+1).
\]

Interpret each `P(t)` as the binary interval `[t,t+1]`.  The left side of (N) has two binary components and the right side has three.  Hence the two alternatives have equal reciprocal value and grade difference exactly `1`.

As `a→∞`, every support position and every mutual support gap tends to infinity, while the common reciprocal mass tends to `0`.  Therefore, for every finite pre-existing physical constraint and every positive mass budget, sufficiently large `a` gives a switch remote from that constraint and below the budget.

For finitely many required coordinates, construct them successively: after each switch is chosen, add both of its alternatives to the finite constraint for the next step.  Thus every selector of the resulting Boolean cube is physically compatible.  The high-coordinate set `U` changes grade by exactly `|U|` and changes neither `W` nor `res`.

# 5. G2 — comparable prime bands

Write
\[
\theta(x)=\sum_{p\le x}\log p,
\qquad
\psi(x)=\sum_{p^m\le x}\log p
=\log\operatorname{lcm}(1,\ldots,\lfloor x\rfloor).
\]

## Lemma 5.1
For every `n≥1`,
\[
\binom{2n}{n}\mid\operatorname{lcm}(1,\ldots,2n+1).
\]

**Proof.** For a prime `p`, Legendre's double count gives
\[
v_p\binom{2n}{n}
=\sum_{j\ge1}
\left(\left\lfloor\frac{2n}{p^j}\right\rfloor
-2\left\lfloor\frac n{p^j}\right\rfloor\right).
\]
Every summand is `0` or `1`.  If the sum is `e`, there are `e` distinct positive exponents with nonzero summand, so the largest is at least `e` and has `p^j≤2n`; hence `p^e≤2n+1`. ∎

The central binomial coefficient is maximal, hence
\[
4^n\le(2n+1)\binom{2n}{n}.
\]
Lemma 5.1 gives eventually
\[
\psi(x)\ge c_\psi x
\]
for some `c_ψ>0`.

Every prime `n<p≤2n` divides `\binom{2n}{n}`, so
\[
\theta(2n)-\theta(n)\le2n\log2.
\]
Dyadic telescoping yields
\[
\theta(x)\le C_\theta x
\]
for an absolute `C_θ`.

Since
\[
\psi(x)=\sum_{m\ge1}\theta(x^{1/m}),
\]
we have
\[
0\le\psi(x)-\theta(x)
\le C_\theta\sum_{m\ge2}x^{1/m}
=O(\sqrt x\log x)=o(x).
\]
Thus eventually
\[
c_\theta x\le\theta(x)\le C_\theta x.
\]
Choose a fixed integer `Λ>1` with `c_θΛ>C_θ`.  Then
\[
\theta(\Lambda X)-\theta(X)\ge c_0X
\]
for some `c_0>0`.  Each prime in `(X,ΛX]` contributes at most `\log(ΛX)` and at least `\log X`; therefore eventually
\[
c_\Pi\frac X{\log X}
\le\#\{p:X<p\le\Lambda X\}
\le C_\Pi\frac X{\log X}.
\]

# 6. G3 — restricted fixed-cardinality additive fold

Let `F` be a field.  We use the following finite-grid coefficient detector.

## Lemma 6.1
If `P∈F[x_1,…,x_h]` has total degree at most `d_1+…+d_h` and the coefficient of `x_1^{d_1}\cdots x_h^{d_h}` is nonzero, then for finite sets `A_i⊂F` with `|A_i|>d_i` there is a grid point on which `P` is nonzero.

**Proof.**  Choose `B_i⊂A_i` with `|B_i|=d_i+1`.  Lagrange interpolation on `B_i` gives a linear functional `L_i` which kills powers `<d_i` and takes `x^{d_i}` to `1`.  Applying `L_1⊗⋯⊗L_h` to a polynomial of total degree at most `Σd_i` kills every monomial except the target monomial.  If `P` vanished on the grid, the functional would give zero, contradiction. ∎

Let
\[
\operatorname{Vdm}(x)=\prod_{i<j}(x_j-x_i).
\]
For distinct nonnegative integers `k_1,…,k_h` and
\[
m=\sum_i k_i-\frac{h(h-1)}2,
\]
one has
\[
[x_1^{k_1}\cdots x_h^{k_h}]
(x_1+\cdots+x_h)^m\operatorname{Vdm}(x)
=
m!\frac{\prod_{i<j}(k_j-k_i)}{\prod_i k_i!}.
\tag{V}
\]
This follows by expanding the Vandermonde determinant and observing that the determinant of falling factorials `(k_i)_{j-1}` equals the ordinary Vandermonde determinant, since the change of basis from monomials to falling factorials is unitriangular.

Now let `A⊂F_p` with `|A|=r`, and let
\[
\Sigma_h:\operatorname{FinSub}_h(A)\to F_p
\]
be restricted summation.  Set
\[
M=\min\{p-1,h(r-h)\}.
\]
Assume `|im Σ_h|≤M` and enlarge the image to a set `C⊂F_p` of exactly `M` elements.  Consider
\[
P(x_1,\ldots,x_h)=
\prod_{c\in C}\left(\sum_i x_i-c\right)\operatorname{Vdm}(x).
\]
This polynomial vanishes on `A^h`: repeated coordinates kill the Vandermonde; distinct coordinates have sum in `C`.

For every `0≤M≤h(r-h)` there exist distinct
\[
0\le k_1<\cdots<k_h\le r-1
\]
with
\[
\sum_i k_i=M+\frac{h(h-1)}2.
\]
To see this, write `M=qh+s`, `0≤s<h`, choose a nondecreasing sequence `λ_i∈[0,r-h]` summing to `M` with entries `q` or `q+1`, and put `k_i=(i-1)+λ_i`.

For these `k_i`, formula (V) gives the target coefficient of the top homogeneous part of `P`.  Since `M≤p-1` and `k_i≤r-1≤p-1`, all factorials are nonzero modulo `p`, and the distinct differences `k_j-k_i` are nonzero modulo `p`.  Hence the coefficient is nonzero.  Lemma 6.1 contradicts grid vanishing.

Therefore
\[
\boxed{
|\operatorname{im}\Sigma_h|
\ge\min\{p,h(r-h)+1\}.
}
\]
The statement is invariant under any additive equivalence from a cyclic order-`p` group to `F_p`, so it applies intrinsically to every simple factor `S_Q`.

# 7. G4 — bounded-conflict quota thinning

We use the standard Haxell independent-transversal theorem:

> If a finite graph has maximum degree at most `Δ` and its vertex partition has blocks of size at least `2Δ`, there is an independent transversal.

For a rowed graph of maximum degree at most `Δ`, split each row into disjoint full chunks of size `2Δ`, discard the remainder, and apply Haxell to the induced graph on the union of chunks, taking the chunks as partition blocks.  One selected vertex per chunk gives an independent set containing
\[
\left\lfloor\frac{|R_i|}{2\Delta}\right\rfloor
\]
vertices in row `i`.  Thus sufficiently large rows retain a fixed positive fraction simultaneously.

This quota corollary is the only use of Haxell in the proof.