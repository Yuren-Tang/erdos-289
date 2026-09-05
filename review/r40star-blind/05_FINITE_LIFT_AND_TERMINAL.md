# E7–E8 — finite-horizon physical realization and terminal exactification

This file is the physical branch of the proof.  The scalar first-hit theorem E6 is assumed already proved.  Only now is an actual Haxell packing chosen.

# 1. Fix the theorem-level density before any packing point

E3 gives, on the late locus, a constant `κ>0` with
\[
|A_Q^{orig}|\ge\kappa Q/\log Q.
\]
E4 gives a fixed survivor fraction `σ>0`, so after the complete wide-start obstacle
\[
|Surv(Q)|\ge\sigma|A_Q^{orig}|.
\]
The global conflict graph has maximum degree at most a fixed `Δ` by E3.  G4 gives a fixed positive quota fraction `ρ_P>0` for every sufficiently large surviving row.  Therefore any finite-horizon Haxell packing has row projections satisfying
\[
|Pack(Q)|\ge \rho_P|Surv(Q)|
\ge \kappa\sigma\rho_P\,Q/\log Q.
\tag{1.1}
\]
Fix once and for all a number
\[
0<\rho<\kappa\sigma\rho_P.
\tag{1.2}
\]
This `ρ` is theorem-level information chosen before any actual packing witness.  By (1.1), every later packed row belongs to the `Adm_ρ(Q)` already analysed in E5.

# 2. First choose a scalar horizon

For any sufficiently large requested grade `k`, E6 gives a nonempty target terminal set `Term_k`.  An element `X∈Term_k` consists of a finite cutoff after the WideStart base such that:

1. the scalar interval recursion through all currents up to `X` is legal;
2. the final grade interval `I_X` contains `k`;
3. the transported centre in `A/H_X` is zero.

Fix such an `X` only for the duration of the finite-horizon realization argument.  There are only finitely many current rows between the start and `X`.

# 3. One finite global Haxell packing

Consider the union of the surviving E3 rows for those finitely many currents, with an edge whenever two atoms cannot coexist in one physical state.  E3 gives one uniform maximum degree bound.  Apply G4 once to this finite rowed graph.  Let `P_X` be the resulting globally independent atom set.

For every current `Q≤X`, its row projection
\[
P_X(Q)=P_X\cap Surv(Q)
\]
satisfies (1.1), hence belongs to `Adm_ρ(Q)`.  Therefore the packing-independent E5 target rectangle applies to **this actual row** with the already-fixed scalar values `d_ρ(Q),m_ρ(Q)`.  No scalar constant is chosen after seeing `P_X`.

# 4. Physical realization of each local channel

For a fixed current `Q`, E5 obtained target subset-sum coverage from actual simple values in `P_X(Q)`.  We now retain the full finite occurrence-lift solution objects used in that proof rather than choosing a section of simple values.  Every chosen finite subset of `P_X(Q)` is a set of actual binary physical atoms.

Because `P_X` is globally independent, all atoms from all its rows are pairwise physically separated.  By the definition of the conflict graph this implies that their supports are disjoint and no two distinct atom supports become adjacent.  Hence any finite tuple of selected atoms lies in the genuine n-ary multiplication domain `D_n` of E2; its literal union is a physical state.

Furthermore, the E4 survivor construction removed every atom conflicting with any wide-start label.  Thus the entire tuple consisting of one wide-start state together with all selected productive atoms also lies in the corresponding n-ary domain.

Consequently the ordinary composability pullback for the finite chain factors through `D_n`.  E2 strictification therefore upgrades the target-level reachability composition to a genuine physical decorated relation whose target projection covers exactly the scalar rectangle predicted by E5 at every step.

Induction through the finitely many current events up to `X` gives a finite physical response
\[
R_X:\mathbf1_0\longrightarrow
T_X:=Tor_{H_X}(\alpha_X)\times I_X
\tag{4.1}
\]
whose target projection is surjective.  Here `\alpha_X` is the transported centre; for `X∈Term_k`, `\alpha_X=0` in `A/H_X`.

# 5. Reciprocal resource control

Let `η>0` be the open margin from E4:
\[
W(S_0)+\eta<2
\]
for every wide-start branch `S_0`.

E3 supplies a nonnegative summable family `roleMass(Q)` with the property that every local response at current `Q` uses at most that much reciprocal value.  Choose the WideStart base sufficiently late that
\[
\sum_{Q>B}roleMass(Q)<\eta.
\tag{5.1}
\]
This is compatible with E4 because E4 holds cofinally: after its onset one may increase `B` further.

For the finite chain up to `X`, E2's subadditive `W` filtration gives, for every edge label `S` of (4.1),
\[
W(S)
\le W(S_0)+\sum_{B<Q\le X}roleMass(Q)
< (2-\eta)+\eta
=2.
\tag{5.2}
\]
Thus every branch of every finite-horizon realization has `W<2`.

This is the last consumer of `roleMass`, the resource series, the conflict graph, the actual Haxell packing, and the n-ary compatibility witness.

# 6. Realization set and surjection to horizons (E7)

Let `Horizon` be the set of scalar cutoffs allowed after the chosen WideStart base.  For each `X∈Horizon`, define `Lift(X)` to be the set of finite data consisting of:

- one G4 packing for the rows up to `X` satisfying (1.1);
- the finite occurrence-lift witnesses needed by the E5 channel covers;
- the resulting physical response `R_X` of (4.1), with all edge labels satisfying (5.2).

The argument above proves
\[
Lift(X)\ne\varnothing
\]
for every scalar-legal horizon `X`.  No choice of a coherent family over all horizons is asserted.

Define the dependent sum
\[
Real:=\sum_{X\in Horizon}Lift(X).
\]
Its projection is therefore surjective:
\[
\boxed{Real\twoheadrightarrow Horizon.}
\tag{6.1}
\]
This is E7.

# 7. Universal target and edge objects

For each horizon `X`, let
\[
T_X=Tor_{H_X}(\alpha_X)\times I_X.
\]
Define the total target bundle
\[
\mathcal T:=\sum_{X\in Horizon}T_X.
\]
For a realization `\ell∈Lift(X)`, its response `R_X` is a finite set of physical edges covering `T_X`.  Define the universal edge object
\[
\mathcal E=
\{(X,\ell,t,e): \ell\in Lift(X),\ t\in T_X,
\ e\text{ is an edge of }R_X\text{ landing at }t\}.
\]
Because every `R_X→T_X` is surjective,
\[
\boxed{
\mathcal E\twoheadrightarrow Real\times_{Horizon}\mathcal T.
}
\tag{7.1}
\]
Every edge label in `\mathcal E` satisfies `W<2` by (5.2).

# 8. Terminal pullbacks (E8)

Fix a sufficiently large `k`.  E6 gives
\[
Term_k:=\{X\in Horizon:\alpha_X=0,\ k\in I_X\}\ne\varnothing.
\tag{8.1}
\]
Pull back (6.1) along `Term_k→Horizon`:
\[
\begin{CD}
Real_k @>>> Real\\
@VVV @VVV\\
Term_k @>>> Horizon.
\end{CD}
\tag{8.2}
\]
Surjections are stable under pullback, so
\[
Real_k\twoheadrightarrow Term_k.
\tag{8.3}
\]

For `X∈Term_k`, the point
\[
(0,k)\in Tor_{H_X}(0)\times I_X=T_X
\]
is canonical.  It defines a section of the target bundle over `Term_k`.  Pull (7.1) back along this section and (8.2).  We obtain
\[
\begin{CD}
E_k @>>> \mathcal E\\
@VVV @VVV\\
Real_k @>>> Real\times_{Horizon}\mathcal T,
\end{CD}
\tag{8.4}
\]
where the bottom map sends a realization at `X` to its requested target `(0,k)`.  Again the left projection is surjective.  Since `Term_k` is nonempty, so is `E_k`.

Choose any point of the nonempty finite solution object `E_k` only for the existential conclusion.  Its physical edge label is a state `S` satisfying
\[
\boxed{res(S)=0,\qquad g(S)=k,\qquad W(S)<2.}
\tag{8.5}
\]
No global or canonical selection is asserted.

# 9. Literalization to reciprocal value one

The observations commute:
\[
\begin{CD}
Phys @>{W}>> \mathbf Q\\
@V{res}VV @VV{q_{\mathbf Z}}V\\
\mathbf Q/\mathbf Z @= \mathbf Q/\mathbf Z.
\end{CD}
\]
Thus `res(S)=0` means `W(S)` lies in the kernel of `q_Z`, namely `Z`.

Because `g(S)=k>0`, the physical state is nonempty.  Every reciprocal summand is positive, so
\[
W(S)>0.
\]
Together with (8.5),
\[
0<W(S)<2,
\qquad W(S)\in\mathbf Z,
\]
hence
\[
\boxed{W(S)=1.}
\tag{9.1}
\]

By the definition of a physical state, `S` has exactly `g(S)=k` connected components; they are pairwise disjoint, non-adjacent finite intervals of positive integers, each of length `2` or `3`.  Therefore every sufficiently large `k` occurs in an exact reciprocal representation of `1`, proving Erdős Problem 289.