# E7–E8 — finite-horizon physical realization and terminal exactification

This file is the physical branch of the proof.  The repaired scalar theorem E6 uses a profile fixed on the original E3 rows, before any WideStart witness is chosen.  An actual Haxell packing is chosen only after a finite scalar horizon is fixed.

# 1. Fix the theorem-level density before any packing point

E3 gives, on the late locus, a constant `κ>0` with
\[
|A_Q^{orig}|\ge\kappa Q/\log Q.
\]
E4 gives a theorem-level survivor fraction `σ>0`.  G4 gives a fixed positive quota fraction `ρ_P>0` for every sufficiently large row in the E3 bounded-conflict graph.  In E5 we already fixed
\[
0<\rho<\kappa\sigma\rho_P
\tag{1.1}
\]
and defined
\[
Adm_\rho(Q)=\{A\subseteq A_Q^{orig}:|A|\ge\rho Q/\log Q\}.
\tag{1.2}
\]
Thus the profile `d_ρ,m_ρ` is fixed before any WideStart witness, survivor set, or packing point exists.

For any E4 WideStart witness `W_B`, its survivor row satisfies
\[
|Surv_{W_B}(Q)|\ge\sigma|A_Q^{orig}|.
\tag{1.3}
\]
After G4 thinning, every actual packed row will therefore satisfy
\[
|Pack(Q)|\ge\rho_P|Surv_{W_B}(Q)|
\ge\kappa\sigma\rho_P\,Q/\log Q
>\rho Q/\log Q,
\tag{1.4}
\]
and hence will automatically belong to the already-defined universal `Adm_ρ(Q)`.

# 2. Put the resource threshold before the scalar first-hit construction

Let `η>0` be the theorem-level open margin supplied by E4.  E3 gives a nonnegative summable family `roleMass(Q)`.  Choose once and for all a threshold `B_res` such that
\[
\sum_{Q>B_{res}}roleMass(Q)<\eta.
\tag{2.1}
\]

The repaired E6 construction allows an arbitrary prescribed lower bound `B_†` on its WideStart base.  Invoke E6 with
\[
B_\dagger=B_{res}.
\]
E6 then chooses a base `B≥B_res`, instantiates E4 at its already-defined startup request, and fixes one WideStart witness `W_B`.  Write
\[
\gamma_B=\alpha_B+\beta_B
\]
for its full affine centre.  E6 constructs from this same fixed WideStart a scalar interval chain with a final ray and with transported centre eventually zero.

Thus the resource-tail condition (2.1) is fixed **before** any scalar first-hit horizon is chosen.  There is no later motion of the WideStart base.

# 3. First choose a scalar horizon

For any sufficiently large requested grade `k`, E6 gives a nonempty target terminal set
\[
Term_k=\{X:\gamma_B\text{ maps to }0\text{ in }(\mathbf Q/\mathbf Z)/H_X,
\ k\in I_X\}.
\]
Fix one `X∈Term_k` only for the duration of the finite-horizon realization argument.  There are only finitely many current rows between the fixed start `B` and `X`.

# 4. One finite global Haxell packing

Consider the union of the surviving E3 rows `Surv_{W_B}(Q)` for those finitely many currents, with an edge whenever two atoms cannot coexist in one physical state.  E3 gives one uniform maximum degree bound.  Apply G4 once to this finite rowed graph.  Let `P_X` be the resulting globally independent atom set.

For every current `B<Q≤X`, its row projection
\[
P_X(Q)=P_X\cap Surv_{W_B}(Q)
\]
satisfies (1.4), is a subset of `A_Q^{orig}`, and hence belongs to the **WideStart-independent** `Adm_ρ(Q)` analysed in E5.  Therefore the already-fixed target rectangle profile `d_ρ(Q),m_ρ(Q)` applies to this actual row.  No scalar constant is chosen after seeing `W_B` or `P_X`.

# 5. Physical realization of each local channel

For a fixed current `Q`, E5 obtained target subset-sum coverage from actual simple values in `P_X(Q)`.  We now retain the full finite occurrence-lift solution objects used in that proof rather than choosing a section of simple values.  Every chosen finite subset of `P_X(Q)` is a set of actual binary physical atoms.

Because `P_X` is globally independent, all atoms from all its rows are pairwise physically separated.  By the definition of the conflict graph this means that their supports are disjoint and no two distinct atom supports become adjacent.  Hence every finite selected subset lies in the genuine n-ary multiplication domain `D_n` of E2; its literal union is a physical state.

Furthermore, `Surv_{W_B}(Q)` was defined by deleting every atom conflicting with **any label of the complete WideStart response** `W_B`.  Thus adjoining any selected productive subset to any WideStart branch also lies in the genuine n-ary physical multiplication domain.

Consequently the ordinary composability pullback for the finite chain factors through `D_n`.  E2 strictification upgrades the target-level reachability composition to a genuine physical decorated relation whose target projection covers exactly the scalar rectangle predicted by E5 at every step.

Induction through the finitely many current events up to `X` gives a finite physical response
\[
R_X:\mathbf1_0\longrightarrow
T_X:=Tor_{H_X}(\gamma_X)\times I_X,
\tag{5.1}
\]
whose target projection is surjective, where `\gamma_X` is the image of the fixed WideStart centre `\gamma_B` in the endpoint quotient.  For `X∈Term_k`, `\gamma_X=0`.

# 6. Reciprocal resource control

Every WideStart branch `S_0` satisfies
\[
W(S_0)+\eta<2.
\tag{6.1}
\]
By the ordering in Section 2, the chosen base already satisfies
\[
\sum_{Q>B}roleMass(Q)
\le\sum_{Q>B_{res}}roleMass(Q)<\eta.
\tag{6.2}
\]
For the finite chain up to `X`, E2's subadditive `W` filtration gives, for every edge label `S` of (5.1),
\[
W(S)
\le W(S_0)+\sum_{B<Q\le X}roleMass(Q)
< (2-\eta)+\eta
=2.
\tag{6.3}
\]
Thus every branch of every finite-horizon realization has `W<2`.

This is the last consumer of `roleMass`, the resource series, the conflict graph, the actual Haxell packing, and the n-ary compatibility witness.

# 7. Realization set and surjection to horizons (E7)

Let `Horizon` be the scalar-legal cutoffs of the fixed E6 construction after the chosen WideStart base.  For each `X∈Horizon`, define `Lift(X)` to be the set of finite data consisting of:

- one G4 packing for the rows up to `X` satisfying (1.4);
- the finite occurrence-lift witnesses needed by the E5 channel covers;
- the resulting physical response `R_X` of (5.1), with all edge labels satisfying (6.3).

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
\tag{7.1}
\]
This is E7.

# 8. Universal target and edge objects

For each horizon `X`, let
\[
T_X=Tor_{H_X}(\gamma_X)\times I_X.
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
\tag{8.1}
\]
Every edge label in `\mathcal E` satisfies `W<2` by (6.3).

# 9. Terminal pullbacks (E8)

Fix a sufficiently large `k`.  E6 gives
\[
Term_k:=\{X\in Horizon:\gamma_X=0,\ k\in I_X\}\ne\varnothing.
\tag{9.1}
\]
Pull back (7.1) along `Term_k→Horizon`:
\[
\begin{CD}
Real_k @>>> Real\\
@VVV @VVV\\
Term_k @>>> Horizon.
\end{CD}
\tag{9.2}
\]
Surjections are stable under pullback, so
\[
Real_k\twoheadrightarrow Term_k.
\tag{9.3}
\]

For `X∈Term_k`, the point
\[
(0,k)\in Tor_{H_X}(0)\times I_X=T_X
\]
is canonical.  It defines a section of the target bundle over `Term_k`.  Pull (8.1) back along this section and (9.2).  We obtain
\[
\begin{CD}
E_k @>>> \mathcal E\\
@VVV @VVV\\
Real_k @>>> Real\times_{Horizon}\mathcal T,
\end{CD}
\tag{9.4}
\]
where the bottom map sends a realization at `X` to its requested target `(0,k)`.  Again the left projection is surjective.  Since `Term_k` is nonempty, so is `E_k`.

Choose any point of the nonempty finite solution object `E_k` only for the existential conclusion.  Its physical edge label is a state `S` satisfying
\[
\boxed{res(S)=0,\qquad g(S)=k,\qquad W(S)<2.}
\tag{9.5}
\]
No global or canonical selection is asserted.

# 10. Literalization to reciprocal value one

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
Together with (9.5),
\[
0<W(S)<2,
\qquad W(S)\in\mathbf Z,
\]
hence
\[
\boxed{W(S)=1.}
\tag{10.1}
\]

By the definition of a physical state, `S` has exactly `g(S)=k` connected components; they are pairwise disjoint, non-adjacent finite intervals of positive integers, each of length `2` or `3`.  Therefore every sufficiently large `k` occurs in an exact reciprocal representation of `1`, proving Erdős Problem 289.