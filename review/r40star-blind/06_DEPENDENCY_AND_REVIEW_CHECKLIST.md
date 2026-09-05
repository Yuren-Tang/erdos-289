# Dependency / last-consumer ledger and hostile review checklist

This file is normative for the blind review.  If a proof appears to use information after the listed last consumer, or an undeclared dependency, report it.

# 1. Corrected dependency skeleton

The reviewer-facing dependencies are:

- `E1` depends only on elementary arithmetic of `Q/Z`.
- `E2` depends only on the concrete physical-state definitions and finite Set-level pullback/image calculus.
- `G1` is the explicit grade-neutral reciprocal identity plus finite remoteness induction.
- `G2` is the elementary Chebyshev/lcm-binomial argument.
- `G3` is the polynomial restricted-fold theorem.
- `G4` is the quota corollary of the external Haxell theorem.
- `E3` depends on `E1,G2` and elementary congruence/divisor estimates.
- `E4` depends on `E1,E2,E3,G1,G2` plus the finite Prefix seed certificate.
- `E5` depends on `E1,E3,G3,E4` only through the existence of dense survivor rows; it contains **no actual Haxell point**.
- `E6` depends on `E1,E4,E5,G2` and is purely scalar/target-level.
- `E7` depends on `E2,E3,E4,E5,G4`; this is the first and last place an actual finite Haxell packing is chosen.
- `E8` depends on `E1,E2,E6,E7` and ordinary pullback stability of surjections.

In particular, the following dependencies are intentionally absent:

- no `E5/E6 -> E4` edge;
- no actual packing point in `E5` or `E6`;
- no probability/LLL dependency anywhere;
- no MasterSlab, DirectLTAR, donor/predecessor, filtered-lifting, or opposite-coset Tail dependency;
- no Lean theorem is accepted as a substitute for a missing human proof.

# 2. Last-consumer ledger

| Datum / coordinate | Created in | Last consumer | Must be absent afterwards |
|---|---|---|---|
| carrier prime `b`, sign, inverse residues `c_±` | E3 | transversality / coefficient proofs inside E3 | yes |
| retained coefficient `k` as construction coordinate | E3 | fibre/support/conflict proofs inside E3 | yes |
| `Q^2/log Q` support scale | E3 | E4 future-footprint estimate and E3 resource proof | yes after E4 |
| distinguished centre `Qk` of an atom | E3 | global conflict-incidence proof | yes before scalar dynamics |
| bridge arithmetic bases `a_r`, lcm moduli | E4 | bridge coverage/separation and future footprint | yes at E4 boundary |
| finite seed numerical coordinates | E4 certificate | proof of seed properties | yes at E4 boundary |
| neutral-cube individual coordinates | E4 | Hamming pullback and future subdensity | yes at E4 boundary |
| literal neutral residue `β_B` | E4 | centre-vanishing part of E6 | yes after `Term_k` |
| simple-value image `B`, image size `r`, route label rich/poor | E5 | proof of common rectangle profile | yes at E5 boundary |
| a heavy value and heavy subset solution object | E5 | redundancy rectangle proof | yes at E5 boundary |
| `d_ρ,m_ρ` | E5 | E6 scalar dynamics and E7 realization | yes before E8 |
| scalar event history / sponsor choices | E6 | proof `Term_k≠∅` | yes before terminal pullback |
| actual Haxell packing point | E7 | finite-horizon physical lift | yes at E7 boundary |
| conflict graph | E3/E7 | finite Haxell lift | yes at E7 boundary |
| n-ary compatibility factorization | E7 | E2 strictification of the finite lift | yes at E7 boundary |
| `roleMass` and its summability | E3 | E7 bound `W<2` | yes at E7 boundary |
| finite horizon `X` | E6/E7 | terminal pullbacks in E8 | yes after target point pullback |
| residue and grade target `(0,k)` | E8 | literalization | public conclusion |

# 3. Quantifier checklist

Please check these in the written order, not merely informally.

## WideStart
The required statement is
\[
\exists\eta>0\ \exists\sigma>0\ \forall L,
\quad L=o(B/\log B)\Rightarrow
\exists B_0(L)\ \forall B\ge B_0(L)\ \exists WideStart(B,L).
\]
The margin `η` and survivor modulus `σ` must not depend on the later startup request `L`; only its onset may do so.

## Density and packing
The order is:

1. E4 proves `σ` before any Haxell point.
2. G4 has a theorem-level quota fraction `ρ_P` depending only on the fixed conflict-degree bound.
3. Fix one `ρ<κσρ_P`.
4. E5 proves a common profile for **all** `ρ`-dense subrows.
5. E6 chooses a scalar first-hit horizon using only that common profile.
6. E7 finally chooses one finite Haxell point and observes that its row projections are `ρ`-dense.

Any proof which chooses `d_ρ,m_ρ` after inspecting the actual packing is invalid.

## Finite solution objects
Whenever existence is obtained by a finite fibre or finite subset family, the proof may work with the whole nonempty solution object and take a regular image.  It must not silently introduce a global section.  In particular check:

- distinct simple-value occurrence lifting in E5;
- heavy-fibre `(p-1)`-subsets in E5;
- Hamming-weight matching in E4;
- terminal target-point realization in E8.

# 4. Arithmetic / asymptotic hostile checks

Please independently verify:

1. the bounded transversality-exception count from `\ell b^2≡±1 (mod p^e)`;
2. coefficient multiplicity `O(1)` from carriers dividing `Qk±1` while `b>Q/B_car`;
3. exact simple-value fibre bound `≤Q/p` after deterministic coefficient deduplication;
4. global centre recovery/injectivity from the unordered atom;
5. prime and non-prime `roleMass` series convergence;
6. Prefix bridge subset-sum coverage and fixed-grade property;
7. future bridge-footprint estimate `O(sqrt(log Q) log log Q)` and the distinction between rank cutoff `B` and lcm modulus `L_B`;
8. the fact that the ragged Prefix grade spread is the fixed finite seed spread, not a growing quantity;
9. E5's implication `image-poor => p=O((log Q)^2)` and the uniform availability of `p-1` equal-value occurrences for every composite `Q=p^e`;
10. cumulative composite debt `O(sqrt X log^3 X)=o(X/log X)`;
11. existence of an earlier prime sponsor in `(Q/Λ^2,Q/Λ]` from G2;
12. the startup reserve argument and the absence of a fixed-point dependence on the selected WideStart witness.

# 5. Physical / categorical hostile checks

Please verify:

1. an independent set in the stated conflict graph really implies the full finite tuple lies in the n-ary physical multiplication domain, not merely pairwise label compatibility;
2. survivor rows are compatible with every wide-start branch, not just with one selected branch;
3. E5 is only a target-level profile theorem for arbitrary dense subrows; physical subset union is asserted only in E7 for the actual independent packing;
4. E2 strictification is applied only after the `P_n -> D_n` factorization is proved;
5. every finite-horizon response covers the whole target fibre/interval, so `Lift(X)` is nonempty for each scalar-legal `X`;
6. `roleMass` is consumed in E7 and not silently re-proved in terminalization;
7. terminalization uses only pullback stability and composition of surjections;
8. `res=0` really means `W∈Z`, and `g=k>0` really implies `W>0` for the concrete physical states.

# 6. Requested review output

Please return:

- verdict: `PASS`, `INCOMPLETE — Minor Repair`, `INCOMPLETE — Major Revision`, or `COUNTEREXAMPLE / FATAL GAP`;
- the first load-bearing failed implication, if any;
- a list of any statements whose hypotheses are insufficient for their stated consumers;
- any quantifier-order or hidden-choice failure;
- any place where a diagrammatic/base-change claim is being used without the required surjectivity or physical composability premise;
- whether the public Erdős 289 conclusion follows from the validated internal state theorem.

A stylistic objection by itself should not change the mathematical verdict, but please record exposition issues separately.