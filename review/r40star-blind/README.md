# Erdős 289 — R40* blind mathematical review packet

**Status:** frozen authorial review candidate; **no independent PASS is claimed**.

This directory is the complete intended surface for a fresh background-blind mathematical review of the current ordinary Erdős 289 proof.  The surrounding `paper/` directory and repository history are **not** part of the review packet and should not be used to fill gaps.

## Public claim under review

For a finite set `S ⊂ N_{>0}`, let

\[
W(S)=\sum_{n\in S}\frac1n.
\]

The claim is:

> For every sufficiently large integer `k`, there exist exactly `k` pairwise disjoint and non-adjacent finite intervals of positive integers, each of length at least `2`, whose reciprocal weights sum to `1`.

The proof works in the stronger subsystem in which every connected component has length `2` or `3`, but this review packet asks only for the ordinary total-component-count conclusion above.

## Review rule

Please reconstruct the proof **only from this directory**, plus the single explicitly external combinatorial input below.

Do **not** use:

- `paper/` or its R16 manuscript;
- earlier review packets, R16–R40 history, or `research-workbench` dossiers;
- Lean source as a substitute for an omitted human argument;
- any historical Tail / DirectLTAR / MasterSlab / donor / predecessor construction.

If a required implication is not justified inside this packet (or by the one allowed external theorem), mark it as a gap rather than searching the history for a repair.

## One allowed external theorem

The only intended external combinatorial black box is the standard Haxell independent-transversal theorem in the following form:

> If a finite graph has maximum degree at most `Δ` and its vertex partition has blocks of size at least `2Δ`, then it has an independent transversal.

The packet uses only the immediate quota corollary obtained by splitting each row into full blocks of size `2Δ`: a bounded-conflict rowed graph admits a simultaneous independent thinning retaining a fixed positive fraction of every row.

No Lovász local lemma or probabilistic argument is part of the proof.

## Reading order

1. `00_THEOREM_MAP.md` — the twelve reviewer-facing statements and their dependency order.
2. `01_FOUNDATIONS_AND_GENERIC_INPUTS.md` — physical states, `Q/Z` filtration, and generic leaves N, Π, D, P.
3. `02_SIGNED_INVERSE_PROVIDER.md` — the total current family and its five exported capabilities.
4. `03_PREPARED_WIDE_START.md` — finite Prefix, sparse future footprint, and one neutral Hamming pullback.
5. `04_LOCAL_PROFILE_AND_SCALAR.md` — finite information channel, packing-independent profile, and sponsored final-ray theorem.
6. `05_FINITE_LIFT_AND_TERMINAL.md` — finite-horizon Haxell realization, n-ary strictification, resource control, terminal descent, and `W=1`.
7. `06_DEPENDENCY_AND_REVIEW_CHECKLIST.md` — last-consumer ledger and requested hostile checks.

## Intended proof architecture

The proof is deliberately split into two branches that meet only at the end:

\[
\text{target/scalar dynamics}\quad\longrightarrow\quad Term_k\neq\varnothing,
\]

and

\[
\text{finite physical realization}\quad\longrightarrow\quad Real\twoheadrightarrow Horizon.
\]

The scalar branch is completed **before** any actual Haxell packing is chosen.  Only after a finite first-hit horizon is fixed is one finite packing chosen and lifted physically.  Terminalization is then regular-epimorphism base change.

## What counts as a successful review

A PASS should mean that, without importing historical knowledge, the reviewer can verify:

1. every theorem statement is sufficient for its stated consumers;
2. all quantifiers have the displayed order, especially `WideStart`, `σ,ρ_P,ρ`, and packing-independent extrema;
3. no selected section / representative is hidden where only a regular image or pullback is justified;
4. pairwise conflict-freeness is not silently substituted for genuine n-ary physical composability;
5. all resource estimates are consumed before terminal descent and really give `W<2` for every realized branch;
6. the final state has residue zero, positive reciprocal value, and value below `2`, hence value exactly `1`;
7. the final component decomposition gives exactly the public interval statement.

Suggested verdicts: `PASS`, `INCOMPLETE — Minor Repair`, `INCOMPLETE — Major Revision`, or `COUNTEREXAMPLE / FATAL GAP`.

Please identify the **first load-bearing failed implication** if the verdict is not PASS.