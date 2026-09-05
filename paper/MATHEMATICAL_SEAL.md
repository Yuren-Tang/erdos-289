# Erdős 289 — mathematical provenance and publication baseline

**Date:** 5 September 2026  
**Status:** core ordinary-E289 proof spine independently reconstructed; later exact-interface defects repaired in the publication manuscript; manuscript-level independent review still OPEN.

## 1. Provenance boundary

The repaired background-blind proof at

`f326a37fcb8957919a51d70498920fcfc6f86f62`

under `review/r40star-blind/` received an independent reconstruction-level **PASS**.  Its predecessor

`604f7ce759304533b1c06bea9a06f9f219421532`

had received **INCOMPLETE — Minor Repair** and was repaired for the WideStart/profile quantifier order, the transition reserve, the full centre `gamma_B = alpha_B + beta_B`, and resource-before-first-hit ordering.

A later hostile review of the mathematics/engineering R44 packet did not find a central counterexample, but correctly identified three mathematical exact-interface defects relevant to a human paper:

1. the signed-inverse carrier cutoff was written with an untyped quotient-looking `Q/B_car`;
2. the neutral-cube resource tolerance changed field implicitly;
3. the restricted-fold polynomial proof used the top homogeneous coefficient without an explicit bridge excluding lower homogeneous contributions.

R45 is consulted only as a source of local exactifications for these points.  It is **not** imported wholesale as the publication ontology, and its Lean-engineering requirements are not publication blockers for the human mathematical paper.

## 2. Publication exactifications now adopted

The active manuscript uses the following exact mathematical interfaces.

### 2.1 Natural carrier cutoff

With integer prime-band multiplier `Lambda` and `B_car = Lambda+1`, define

`X_Q = Q div B_car`

by natural-number Euclidean division and take carriers in

`X_Q < b <= Lambda X_Q`.

The proof records

`B_car b > Q`, `b < Q`, and `X_Q asymp Q`.

No field-valued `Q/B_car`, hidden floor, or alternative rounding convention remains in the construction.

### 2.2 Neutral budget

The remote neutral-cube theorem takes a positive rational resource budget `epsilon in Q_{>0}`.  If a later consumer supplies a positive real tolerance, choose a smaller positive rational tolerance first.  The retained per-coordinate complete-envelope complexity is the canonical constant `5`.

### 2.3 Restricted-fold coefficient bridge

For

`H_C(T)=prod_{c in C}(T-c)=T^M+R_C(T)` with `deg R_C<M`,

the Vandermonde is homogeneous of degree `h(h-1)/2`.  Hence no term from `R_C(sum x_i)V` can contribute to a monomial of total degree `M+h(h-1)/2`.  The coefficient used in the Nullstellensatz contradiction is therefore literally the coefficient computed from `(sum x_i)^M V`.

The manuscript also spells out why the factorial and Vandermonde factors are nonzero modulo `p`.

### 2.4 Intrinsic bounded-lag sponsor

The scalar proof no longer exposes a quotient interval such as `Q/Lambda^2 < q <= Q/Lambda`.  From the integer prime-band theorem it proves a bounded-lag lemma

`q < Q <= Lambda_s q`

for one fixed integer `Lambda_s>1`, using only natural-number Euclidean division.  The startup request is correspondingly

`R(B)=A(Lambda_s B)+N(Lambda_s B)`.

## 3. Frozen proof spine for the paper

The publication proof must preserve the following information firewall.

1. Signed inverse supplies the deterministic original current row `A_Q`, simple-value fibre bound, conflict incidence, support scale, and summable role mass.
2. The local finite-channel theorem analyses **all sufficiently dense subrows of the original row**, before any WideStart witness or Haxell packing exists.  The canonical profile is therefore WideStart- and packing-independent.
3. WideStart independently supplies a uniform survivor fraction `sigma` and resource margin `eta`.
4. The scalar theorem consumes only the universal profile, bounded-lag sponsors, and the full centre `gamma_B`; it can be run above an arbitrarily prescribed lower cutoff.
5. The resource tail cutoff is chosen before scalar first-hit.
6. Only after a finite first-hit horizon is fixed is Haxell applied once.  The packed rows are dense enough to lie in the already analysed universal class.
7. Resource, conflict, packing, and n-ary compatibility die in finite physical realization.  Terminalization is then Set-level base change followed by `res=0`, positivity, and `W<2`, hence `W=1`.

## 4. Later packet material deliberately not adopted

Do not narrow the universal admissible family to rows carrying extra independence or packing structure.  The paper keeps the stronger and cleaner class

`Adm_rho(Q) = { A subset A_Q : |A| >= rho Q/log Q }`.

Haxell/physical independence appears only when the actual finite realization is chosen.

Do not regress from the full centre

`gamma_B = alpha_B + beta_B`

to a centre described only by the neutral translation `beta_B`.

Do not import packet-level demands for Lake files, theorem-to-Lean declaration ledgers, exact Mathlib representations, or zero-discretion formal transcription into the human-paper publication gate.  Those belong to the separate formalization project unless they expose an ambiguity in the mathematical statement itself.

## 5. Categorical wording discipline

Avoid saying that arbitrary right-total decorated relations with compatibility restriction automatically form a category.  The manuscript uses a partial/composable decorated-relation calculus.  Composition is invoked only after target coverage and the required `P_n -> D_n` n-ary physical factorization have been proved.

Universal transport, quotient/simple-factor passage, regular images, pullbacks, base change, information-loss boundaries, and terminal descent remain diagrammatic.  Ordinary arithmetic/combinatorial leaves are presented as explicit providers for the corresponding arrows; the paper does not claim a meaningless global character-minimality theorem over all possible encodings.

## 6. Current publication gate

The active `paper/post-pass-rewrite` LaTeX is the publication object.  It must now receive an independent **manuscript-level** reading of the exact PDF/source, with particular attention to faithful transcription of the four exactifications above and to theorem-hypothesis/consumer consistency.

A separate R45 engineering review is not required for this publication line.  A manuscript reviewer can simultaneously recheck the local mathematical repairs and the paper's self-contained exposition.

Complete Lean formalization remains a separate unfinished project unless and until independently built and audited.
