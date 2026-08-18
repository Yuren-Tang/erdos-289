# Formalization roadmap

This file records what is proved, what is not, and what the remaining work is.
It is the document to read before trusting any summary sentence elsewhere in
the repository.

The mathematics being formalized is the two-part descent:

* **Part I** — the universal graded affine-correction theorem (`AffineCorrection/`);
* **Part II** — the descent from that theorem to Erdős problem 289 (`Erdos289/`).

## 0. Status in one line

The universal core, the five isolated hard leaves, and the reciprocal
infrastructure are proved unconditionally and are transitively axiom-audited.
**The unconditional Erdős 289 theorem is not proved.** Two layers are missing:
the instantiation of the universal core at the reciprocal system, and the
quantitative verification of that instantiation's hypotheses.

## 1. Two leaf lists, and why they do not actually conflict

The design notes behind this development name the five hard leaves in two
different ways, and the difference is the single most common source of
confusion about how far along the project is.

| landed | note | leaves | where the signed-inverse row certificate sits |
| --- | --- | --- | --- |
| 19:00 `411a3e8d` | *post-bite leaf-DAG freeze* | `E, N, T, P, D` | `T` is a leaf, and "the hard part is the quantitative carrier supply/resource theorem" |
| 19:55 `91409485` | *hard-leaf interface audit* | `E, N, Π, P, D` | not a leaf: "derived finite arithmetic downstream of `Π`" |
| 20:14 `2b38a87b` | *Lean 4.33 zero-axiom route* | `E, N, Π, P, D` | same; "the five final hard leaves are **still** `E, N, Π, P, D`" |

(Times are the commit dates in `Yuren-Tang/research-workbench` on 2026-08-17.
A shallow clone shows all three in one grafted commit and cannot order them.)

**The two lists disagree about labelling, not about content.** Both say the
same thing has to be proved: the quantitative row certificate. One calls it a
fifth leaf named `T`; the other splits it into the external input `Π` plus
arithmetic derived below it. `T` is, up to naming, `Π` together with that
derived arithmetic.

This package uses the `Π` list, and the chronology settles it: the `Π` list is
the later one, and the last word on the question is the Lean note itself. It is
also the finer decomposition, so the genuinely external input is isolated to a
single prime-counting statement, and it is what the existing code already
implements.

The consequence for reading the status: all five of `E, N, Π, P, D` are proved,
*and* the content that the other list calls `T` is not. Only `T`'s atom-level
ingredients are — complementary signed-inverse pairs, the bounded quadratic
shape of downwardness exceptions, the four-point coefficient-fibre bound, and
the reservoir and pool constructors. So "all five leaves are complete" and "a
large amount of work remains" are both true and not in tension.

What remains is also not a *further* conceptual leaf. It is the arithmetic
verification that the manuscript itself calls "the last genuinely arithmetic
realization theorem", plus the wiring of the universal core.

## 2. What is proved unconditionally

### Universal core (Part I)

| object | declaration |
| --- | --- |
| partial commutative physical monoid | `AffineCorrection.PartialAddCommMonoid` |
| coherent observation functor | `AffineCorrection.ObservationSystem` |
| Grothendieck normal form of correction morphisms | `AffineCorrection.GradedCorrection.Hom` |
| realizer pullback and regular epi cover | `AffineCorrection.Realizer`, `Covers` |
| compatible composition epi | `AffineCorrection.CompositionCovers` |
| exact-fibre transfer | `AffineCorrection.grade_mem_exactSpectrum_of_covers_target` |
| target centering and its universal property | `AffineCorrection.CenteredValue.desc`, `desc_unique` |
| compact stage resolution | `AffineCorrection.CompactStage.system` |
| least absorber | `AffineCorrection.LeastAbsorber.minimal` |
| grade-resource quantale | `AffineCorrection.GradeResource` |
| free enriched closure | `AffineCorrection.FreeClosure.hom_le_of_edge_le` |
| cyclic ladder | `AffineCorrection.CyclicLadder.zmod_generatesIn_pred` |
| cofinal interval spectrum | `AffineCorrection.intervalSpectrum_cofinite` |

### The five leaves

| leaf | statement | declaration |
| --- | --- | --- |
| `E` | every constrained unit-fraction presentation fibre is inhabited | `Erdos289.unitFractionRefinementCofinality` |
| `N` | the neutral grade-one fibre has arbitrarily light remote points | `Erdos289.remoteLightNeutralGradeOne` |
| `Π` | explicit prime count in `(n, 4n]` from mathlib's Chebyshev bounds | `Erdos289.comparablePrimeSupply_explicit` |
| `P` | Haxell `2Δ`-thick chunk packing | `Erdos289.IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le` |
| `D` | Dias da Silva–Hamidoune restricted-fold image growth | `Erdos289.RestrictedFold.image_card_lower_bound` |

`P` and `D` are vendored from Apache-2.0 sources; see `THIRD_PARTY.md`.

### Reciprocal infrastructure

Path-support partial monoid with additive value and grade; binary and ternary
blocks and their exact identities; upper blockification; the constructive
remote separated Egyptian leaf and its rational-target composition; arbitrarily
light mobility; the prime-power filtration of `ℚ/ℤ` and its simple fibres;
signed-inverse atoms and their transversality; local profiles; the quantitative
reservoir interface; the unit selector; the literal-statement bridge.

### Faithfulness of the statement

`Erdos289.erdos289LiteralSeparated_of_statement` derives, from
`Erdos289.Erdos289Statement`, the sentence displayed on erdosproblems.com/289,
and `Erdos289.erdos289Literal_of_statement` derives the form used by the
`erdos_289` entry of `google-deepmind/formal-conjectures`. The intrinsic
statement is therefore not merely *believed* to be Erdős 289; the implication is
machine-checked. It is also strictly stronger: all blocks have length two or
three, and consecutive blocks are required to be non-adjacent.

## 3. What is missing

### Layer A — instantiating the universal core (thin, partly done)

`Erdos289/EngineBridge.lean` fixes the universal data at the reciprocal system
and identifies the universal conclusion with the statement the descent needs.

* A1. *Done.* `Erdos289.reciprocalObservation` is the compact-stage observation
  system on `ℚ/ℤ`; `Erdos289.isAdditiveOn_value`, `isAdditiveOn_grade` and
  `isAdditiveOn_residue` supply the additivity the composition theorem wants.
* A2. *Done.* `Erdos289.selectorFamily` is the physical family, and
  `Erdos289.cofiniteSaturation_of_exactSpectrum` shows that cofiniteness of
  `AffineCorrection.exactSpectrum (selectorFamily c) Support.residue
  Support.grade 0` *is* `CofiniteSaturation 1 c`.
* A3. **Open.** `Covers` for one local stage, from `CoversAtGrade`
  (`Erdos289/LocalProfiles.lean`).  This is where the arithmetic layers enter.
* A4. **Open.** composition of stages via `CompositionCovers`.  The physical
  side is available: `Erdos289.aggregateSupport_value`, `aggregateSupport_grade`
  and `aggregateSupport_residue`.
* A5. **Open, and not merely mechanical.** `LiteralizesTarget` at a compact
  stage `H` asserts that a target realizer's residue is exactly zero, while the
  realizer pullback only gives residue in `H`.  Closing that gap is the
  defect-absorption step, whose universal object is
  `AffineCorrection.LeastAbsorber`; it needs the endpoint stages to eventually
  contain the fixed finite defect subgroup.

A note on the core itself, and on where the fault lay.
`AffineCorrection.exactSpectrum` originally ranged over the whole ambient state
type, so it forgot the physical family; the transfer theorem's conclusion was
therefore strictly weaker than its own proof supported, and useless for E289,
whose admissibility constraints live exactly in the family.

This was **not** a defect in the manuscript. Part I defines
`Spec_g(τ) := {g(x) : x ∈ C, W(x) = τ}` over the ambient configuration object
`C`, and in the manuscript `C` *is* the admissible `{2,3}`-block system — the
final claim is written `Spec_{2,3}(1)`. The Lean encoding chose a wider ambient
type, `Support = Finset ℕ+`, and carried admissibility in the family `F`
instead; transcribing the manuscript's definition literally against that wider
`C` is what lost the constraints. The fix restores the manuscript's intent and
strictly generalizes it: taking `F = Set.univ` recovers the original
definition verbatim.

### Layer B — the quantitative verification (arithmetic, absent)

This is Part II §16–§18 of the manuscript. It is deliberately *not* categorical:
it is the finite arithmetic that verifies the hypotheses of the aggregation
theorem in the strict reciprocal system.

* B1. **Usable form of `Π`.** *Done.*
  `Erdos289.comparablePrimes_card_isBigO` states
  `(fun n => n / log n) =O[atTop] (fun n => #(comparablePrimes n))`, i.e.
  `#{p : n < p ≤ 4n} ≫ n / log n`.  The `√(4n) log(4n)` error term of the
  Chebyshev lower bound is absorbed by `Asymptotics.IsLittleO`.

  A note on style, binding for the rest of layer B: **an asymptotic statement
  is formalized as an asymptotic statement.**  It is not replaced by an
  inequality valid beyond a hand-picked numerical threshold.  mathlib's
  `Asymptotics` and `Filter.atTop` API is what makes this both faithful and
  short; the first draft of this module took the numerical route and was more
  than twice as long for a strictly less faithful statement.
* B2. **Row supply (manuscript Thm 17.1).** *In progress.* For every large
  prime power `Q`, a raw row of `≫ Q / log Q` signed-inverse atoms with
  distinct current coefficients.
  * *Done.* The carrier band. `Erdos289.SignedInverse.bandBase` chooses the
    comparable band so that `b < Q` is automatic, and
    `card_carrierPrimes_ge` shows the only carrier lost to the current-stage
    exclusions is `p` itself.  Its growth is inherited asymptotically from B1
    through `bandBase_isBigO`.
  * *Done.* The quadratic-congruence root bound.
    `Erdos289.primePower_squareFiber_card_le_four` bounds a square fibre of
    `(ZMod (p ^ e))ˣ` by four points, uniformly in `p` and `e`.  The odd branch
    is the cyclic two-torsion; the `p = 2` branch — which the earlier code had
    flagged as intended but not supplied — is the elementary fact that an odd
    square root of one modulo `2 ^ e` is `±1` modulo `2 ^ (e - 1)`.
  * *Done.* The deletion step.
    `Erdos289.SignedInverse.exists_multiplier_of_goodOrientations_eq_empty`
    shows that a band carrier with no usable orientation solves
    `λ b² = ±1` in `ZMod Q` with `1 ≤ λ ≤ 3` (because `Q ≤ 4 b` on the band)
    and `p ∤ λ`; and `card_badCarriers_le` concludes that at most twenty-four
    carriers of a band are lost, independently of `Q`.
  * *Done.* The assembly at band level.
    `Erdos289.SignedInverse.card_goodCarriers_ge` says a family of band
    carriers keeps all but at most twenty-four of its members, and
    `bandCard_isBigO` says the band itself carries `≫ Q / log Q` primes.
  * **Open.** Deduplication by coefficient (the four-point fibre bound is
    available as `carrierFamily_coefficientFiber_card_le_four`), the rank-half
    truncation, and the resulting centre and mass bounds.
* B3. **Bounded conflict degree.** *Done.*
  `Erdos289.SignedInverse.reservoir_conflictNeighbors_card_le` bounds the
  conflict degree of a signed-inverse row by `2 (max 1 separation + 1)`, a
  constant independent of the current prime power and of the row size.  The
  general statement for any family of binary atoms is
  `Erdos289.TransverseReservoir.conflictNeighbors_card_le_of_binary`.
* B4. **Packing.** *Done, modulo the chunk partition.*
  `Erdos289.exists_compatiblePool_of_binary` turns any partition of the atoms
  of a binary reservoir into chunks of size at least
  `4 (max 1 separation + 1)` into a `CompatibleTransversePool`, via the
  conflict graph `Erdos289.TransverseReservoir.conflictGraph` and the packing
  leaf.  What B2 still has to supply is a row large enough to be cut into
  enough such chunks.
* B5. **Local profiles.** Prime rows: the epi-grade interval `[a_p, b_p]` from
  `D` via `restrictedFold_coversAtGrade`. Proper prime powers: the fixed grade
  `p - 1` from `atom_cyclic_coversAtGrade` plus exported neutral atoms.
* B6. **Donor flow.** The one-use supply/demand inequality; the running-balance
  form is `Erdos289.GradeAggregation.donor_flow_nonneg`.
* B7. **Interval aggregation.** `∑_{p ≤ X} log p = O(X)` and
  `∑_{p ≤ X} p / log p ≫ X² / log² X`, hence eventual overlap. The
  interval-decomposition step is
  `Erdos289.GradeAggregation.exists_grades_of_mem_sum_Icc`; the eventual-ray
  step is `AffineCorrection.intervalSpectrum_cofinite`.
* B8. **Cost summability.** Convergence of `∑ 1/(p log p)` over primes and of
  `∑ log Q / Q^{3/2}` over prime powers.
* B9. **Tempered finite prefix (manuscript Thm 16.1).** A complete-sequence
  seed, the lcm endpoint bridge, and the uniform bound `W < 2 - η`. No module
  for this exists yet.

### Layer C — final assembly

`Erdos289.cofiniteSaturation_one_of_centered` is the entry point: it needs, for
every sufficiently large `k`, one admissible support of grade `k` with value in
`(0, 2)` and vanishing centered residue. Layers A and B produce exactly that.

## 4. Discipline for the remaining work

Unfinished leaves are **explicit theorem parameters or certificate structure
fields, never global axioms**. `scripts/source_scan.py` rejects `axiom`, and
`Audit.lean` pins the transitive axiom set of every exported theorem with
`#guard_msgs`, so an accidental assumption cannot enter silently.

A conditional theorem of the shape

```text
(quantitative row certificate) → Erdos289Statement
```

is an acceptable and intended intermediate deliverable. A global axiom asserting
the same thing is not.
