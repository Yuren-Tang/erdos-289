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

## 1. Two leaf lists, and which one this package implements

The design notes behind this development contain **two different lists of five
hard leaves**, and the difference is the single most common source of confusion
about how far along the project is.

| list | leaves | where the signed-inverse row certificate sits |
| --- | --- | --- |
| *leaf-DAG freeze* | `E, N, T, P, D` | `T` **is** a leaf: it is the quantitative reservoir theorem |
| *hard-leaf interface audit* | `E, N, Π, P, D` | not a leaf; "derived finite arithmetic downstream of `Π`" |

This package implements the **second** list. All five of `E, N, Π, P, D` are
proved. In the first list's vocabulary that means `T` is *not* proved: only its
atom-level ingredients are (complementary signed-inverse pairs, the bounded
quadratic shape of downwardness exceptions, the four-point coefficient-fibre
bound, and the reservoir/pool constructors).

So "all five leaves are complete" and "a large amount of work remains" are both
true, and they are not in tension. What remains is not a further conceptual
leaf; it is the arithmetic verification that the manuscript itself calls "the
last genuinely arithmetic realization theorem", plus the mechanical wiring of
the universal core.

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

A note on the core itself: `AffineCorrection.exactSpectrum` originally ranged
over the whole ambient state type and so forgot the physical family, which
made the transfer theorem's conclusion strictly weaker than its own proof
supported — and useless for E289, whose admissibility constraints live exactly
in the family.  It is now family-relative.

### Layer B — the quantitative verification (arithmetic, absent)

This is Part II §16–§18 of the manuscript. It is deliberately *not* categorical:
it is the finite arithmetic that verifies the hypotheses of the aggregation
theorem in the strict reciprocal system.

* B1. **Usable form of `Π`.** *Done.*
  `Erdos289.card_comparablePrimes_ge` gives
  `(n : ℝ) / (2 * Real.log n) ≤ (comparablePrimes n).card` for `n ≥ 50 ^ 4`,
  absorbing the `√(4n) log(4n)` error term of the theta lower bound.
* B2. **Row supply (manuscript Thm 17.1).** For every large prime power `Q`, a
  raw row of `≫ Q / log Q` signed-inverse atoms with distinct current
  coefficients. Needs: a bound on the number of roots of `λ b² ≡ ±1 (mod Q)`
  for bounded `λ`; deduplication by coefficient (the four-point fibre bound is
  already available as `carrierFamily_coefficientFiber_card_le_four`); the
  rank-half truncation and the resulting centre and mass bounds.
* B3. **Bounded conflict degree.** Global injectivity and bounded span of the
  distinguished centres, giving a uniform bound on
  `TransverseReservoir.conflictNeighbors`.
* B4. **Packing.** Apply `P` to B3 to obtain a `CompatibleTransversePool` whose
  size is a fixed positive fraction of the row.
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
