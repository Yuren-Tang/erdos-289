# Erdős 289 — repaired R40* blind mathematical review packet

**Status:** repaired frozen authorial review candidate after an independent `INCOMPLETE — Minor Repair` verdict; **no independent PASS is claimed**.

This directory is the complete intended surface for a fresh background-blind mathematical review of the current ordinary Erdős 289 proof.  The surrounding `paper/` directory and repository history are **not** part of the review packet and should not be used to fill gaps.

## Public claim under review

For a finite set `S ⊂ N_{>0}`, let
\[
W(S)=\sum_{n\in S}\frac1n.
\]
The claim is:

> For every sufficiently large integer `k`, there exist exactly `k` pairwise disjoint and non-adjacent finite intervals of positive integers, each of length at least `2`, whose reciprocal weights sum to `1`.

The proof works in the stronger subsystem in which every connected component has length `2` or `3`, but this packet asks only for the ordinary total-component-count conclusion.

## Review rule

Please reconstruct the proof **only from this directory**, plus the single explicitly external Haxell theorem below.

Do **not** use `paper/`, earlier packets, repository history, research-workbench dossiers, or Lean files to repair an argument.  If a required implication is absent, mark it as a gap.

## One allowed external theorem

Use the standard Haxell independent-transversal theorem in the form:

> If a finite graph has maximum degree at most `Δ` and its vertex partition has blocks of size at least `2Δ`, then it has an independent transversal.

The packet uses only the immediate quota corollary obtained by splitting each row into full blocks of size `2Δ`.  No Lovász local lemma or probabilistic argument is part of the proof.

## Reading order

For a **fresh blind review**, use:

1. `00_THEOREM_MAP.md`
2. `01_FOUNDATIONS_AND_GENERIC_INPUTS.md`
3. `02_SIGNED_INVERSE_PROVIDER.md`
4. `03_PREPARED_WIDE_START.md`
5. `04_LOCAL_PROFILE_AND_SCALAR.md`
6. `05_FINITE_LIFT_AND_TERMINAL.md`
7. `06_DEPENDENCY_AND_REVIEW_CHECKLIST.md`
8. `PREFIX_SEED_CERTIFICATE.json` and `verify_prefix_seed.py` for the finite Prefix seed.

If you are **re-reviewing the previous failed packet**, read `REPAIR_RESPONSE.md` first; it lists the four local repairs and the specific implications to recheck.

## Intended proof architecture

The repaired load-bearing order is
\[
\text{original E3 rows}
\to
\text{universal dense-subrow profile}
\to
\text{startup request}
\to
\text{one selected WideStart}
\to
\text{scalar final ray}
\to
\text{finite Haxell realization}
\to
\text{terminal pullback}.
\]

The key repair is that the E5 profile is now defined over **all sufficiently dense subrows of the original E3 row**, not over survivor rows of a selected WideStart witness.  Hence the profile and startup request are fixed before that witness exists.

The scalar/physical split remains: actual Haxell packing occurs only after a finite scalar horizon is fixed.

## What counts as a successful review

A PASS should mean that, without historical material, the reviewer can verify:

1. E5's profile is genuinely independent of the selected WideStart witness;
2. the sponsor transition is correctly reserved through `Λ^2B`;
3. the full centre `α_B+β_B` is carried and eventually annihilated;
4. the resource-small start is fixed before scalar first-hit;
5. every theorem statement is sufficient for its consumer;
6. no hidden section/representative is selected where only a finite solution relation or pullback is justified;
7. pairwise conflict-freeness is not substituted for genuine n-ary physical composability;
8. resource estimates really imply `W<2` before terminal descent;
9. terminal regular-epi/base-change steps are valid;
10. the final state gives the public interval statement.

Suggested verdicts: `PASS`, `INCOMPLETE — Minor Repair`, `INCOMPLETE — Major Revision`, or `COUNTEREXAMPLE / FATAL GAP`.

If not PASS, please identify the **first load-bearing failed implication**.