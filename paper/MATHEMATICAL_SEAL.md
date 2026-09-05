# Erdős 289 — mathematical seal and publication baseline

**Date:** 5 September 2026  
**Status:** ordinary Erdős 289 mathematics independently PASSed; manuscript rewrite pending.

## 1. Authoritative mathematical object

The authoritative closed-packet proof is the repaired blind-review candidate at commit

`f326a37fcb8957919a51d70498920fcfc6f86f62`

under `review/r40star-blind/`.

A fresh independent reviewer reconstructed the public Erdős 289 theorem from that pinned directory only, using only the explicitly allowed Haxell independent-transversal theorem externally, and returned **PASS**.

The earlier failed packet at

`604f7ce759304533b1c06bea9a06f9f219421532`

is retained as provenance for the preceding **INCOMPLETE — Minor Repair** verdict.  The repair fixed the WideStart/profile quantifier order, the `Lambda^2 B` transition cutoff, the full centre `gamma_B = alpha_B + beta_B`, and resource-before-first-hit ordering.

No later authorial packet supersedes the independently reviewed proof unless a new review-triggered mathematical defect is found.

The transcribed PASS report contains one evident formatting loss in the displayed composite-debt bound.  The authoritative reviewed estimate is

`N(X) = O_rho(sqrt(X) log^3 X) = o(X/log X)`,

not `O_rho(X log^3 X)`.  The latter would contradict the displayed little-o conclusion and must not be propagated into the manuscript.

## 2. Frozen proof spine

The publication proof must preserve the following dependency firewall.

1. E3 supplies the deterministic original current row `A_Q^orig`, simple-value fibre bound, conflict incidence, support scale, and summable role mass.
2. E5 analyses **all sufficiently dense subrows of `A_Q^orig`**, before any WideStart witness or Haxell packing exists.  Thus the canonical profile `d_rho,m_rho` is WideStart- and packing-independent.
3. E4 independently supplies a WideStart with a uniform survivor fraction `sigma` and resource margin `eta`.
4. E6 is scalar-only.  It uses the fixed profile and a startup request `R(B)=A(Lambda^2 B)+N(Lambda^2 B)`, carries the full centre `gamma_B`, and can be run above an arbitrarily prescribed lower cutoff.
5. The resource cutoff `B_res` is chosen before the scalar first-hit construction, then E6 is run with `B >= B_res`.
6. Only after a finite first-hit horizon is fixed does E7 apply Haxell once.  The packed row is dense enough to lie in the already analysed universal admissible class.
7. Resource, conflict, packing, and n-ary compatibility all die in E7.  E8 is Set-level regular-epi/base-change terminal descent followed by `res=0`, positivity, and `W<2`, hence `W=1`.

## 3. R42 differential disposition

The mathematics-only R42 packet was inspected after the independent PASS.  Its static validator, Prefix seed replay, and vendored frozen-blob replay all pass, but these are integrity/regression checks rather than a proof seal.  R42 is not the mathematical authority because it still labels itself as requiring a fresh review.  Three local improvements are worth absorbing into the publication manuscript because they only make already-valid interfaces explicit:

### 3.1 Late-domain typing

Introduce a literal threshold `Q_prof` and regard the local profile as defined only on

`Current_{>=Q_prof}`.

Enumerate only that late subtype in the scalar schedule.  Do not arbitrarily totalize `d,m` over early currents.  The WideStart base is chosen `B>=Q_prof`, so all later currents lie in the profile domain.

### 3.2 Haxell quota versus density

State the generic Haxell corollary first as an all-row quota

`|A ∩ R_i| >= floor(|R_i|/L_P)`.

Positive relative density `rho_P>0` is a corollary only after the survivor row is large enough, e.g. `|R_i|>=L_P`.  Add the eventual non-small survivor lemma explicitly before using relative density in the finite lift.

### 3.3 Endpoint/current-step glue

Add the elementary lemma

`H_{Q_J-1}=F_{<J}` and `H_{Q_J}=F_J`.

The first equality is the identity of indexing conditions `Q_R < Q_J` and `Q_R <= Q_J-1`; the second uses injectivity of current rank so that the equal-rank summand is exactly `J`.  This makes the associated-graded local response `F_{<J}->F_J` literally the endpoint step `H_{Q_J-1}->H_{Q_J}` used in the global chain.

These are exposition/type/glue improvements, not new proof mechanisms.

## 4. R42 material not adopted

Do **not** replace the independently reviewed universal admissible family by R42's narrower independent-subrow family.  The publication baseline keeps

`Adm_rho(Q) = { A subset A_Q^orig : |A| >= rho Q/log Q }`.

This is strictly cleaner: E5 knows neither WideStart nor Haxell.  Physical independence is introduced only in E7 when the actual finite packing is chosen.

Likewise, do not regress from the full WideStart centre

`gamma_B = alpha_B + beta_B`

to a centre described only by the neutral translation `beta_B`.

## 5. Reviewer wording correction

The independent PASS recorded one non-load-bearing wording issue in E2.  Avoid saying that arbitrary right-total physically decorated relations, after restricting the ordinary pullback to compatible labels, automatically "form a category".  Right-totality need not survive an arbitrary compatibility restriction.

The manuscript should instead say:

- physically decorated finite relations admit a partial/composable span calculus;
- ordinary pullback, literal physical union, and regular image define composition on those finite diagrams for which the required target coverage and `P_n -> D_n` n-ary factorization are established;
- every composition used in the E289 proof satisfies these stronger hypotheses.

No public theorem depends on unrestricted closure.

## 6. Publication work order

1. Rewrite the old R16 manuscript around the independently PASSed ordinary E289 spine.
2. Delete the historical active machinery: MasterSlab, DirectLTAR, donor/predecessor allocation, target-specific filtered lifting, opposite-coset Tail, and fixed-profile `(b_2,b_3)` strengthening from the critical path.
3. Present the upper proof diagrammatically: physical response calculus -> quotient/simple-factor channel -> universal dense-restriction profile -> scalar final ray / finite realization split -> terminal pullback -> `W=1`.
4. Cite Haxell as the only external packing theorem; do not include the historical self-contained augmenting-sequence proof in the critical path.
5. Keep Lean status and LLM assistance disclosures accurate: the mathematical proof has an independent human-readable PASS; complete Lean formalization is a separate unfinished project unless and until independently built and audited.

This file is the authority boundary for the publication rewrite branch.