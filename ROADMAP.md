# Formalization roadmap

This file records what is proved, what is not, and what the remaining work is.
It is the document to read before trusting any summary sentence elsewhere in
the repository.

The mathematics being formalized is the two-part descent:

* **Part I** — the universal graded affine-correction theorem (`AffineCorrection/`);
* **Part II** — the descent from that theorem to Erdős problem 289 (`Erdos289/`).

## 0. Status in one line

The universal core, the five isolated hard leaves, the reciprocal
infrastructure, the descent spine and the **finite core provider** are proved
unconditionally and are transitively axiom-audited.  **The unconditional
Erdős 289 theorem is not proved.**  Exactly one obligation remains: the
manuscript's *cofinal tail provider*, isolated as the explicit hypothesis of
`Erdos289.erdos289Statement_of_tailInterface`.

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
| `Π` | prime count in `(n, 4n]` from mathlib's Chebyshev bounds | `Erdos289.comparablePrimeSupply_explicit`, asymptotically `Erdos289.comparablePrimes_card_isBigO` |
| `P` | Haxell `2Δ`-thick chunk packing | `Erdos289.IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le` |
| `D` | Dias da Silva–Hamidoune restricted-fold image growth | `Erdos289.RestrictedFold.image_card_lower_bound` |

`P` and `D` are vendored from Apache-2.0 sources; see `THIRD_PARTY.md`.

### Reciprocal infrastructure

Path-support partial monoid with additive value and grade; binary and ternary
blocks and their exact identities; upper blockification; the constructive
remote separated Egyptian leaf and its rational-target composition; arbitrarily
light mobility; the prime-power filtration of `ℚ/ℤ` and its simple fibres;
signed-inverse atoms and their transversality; local profiles and their grade
intervals; the quantitative reservoir interface and its packing; the row
certificate of a prime-power current; the unit selector; the descent spine; the
finite core provider; the literal-statement bridge.

### Faithfulness of the statement

`Erdos289.erdos289LiteralSeparated_of_statement` derives, from
`Erdos289.Erdos289Statement`, the sentence displayed on erdosproblems.com/289,
and `Erdos289.erdos289Literal_of_statement` derives the form used by the
`erdos_289` entry of `google-deepmind/formal-conjectures`. The intrinsic
statement is therefore not merely *believed* to be Erdős 289; the implication is
machine-checked. It is also strictly stronger: all blocks have length two or
three, and consecutive blocks are required to be non-adjacent.

## 3. The two provider interfaces, and which one is left

The active authorial surface (clean qualitative proof v4.1) factors the whole
descent through exactly two provider interfaces and three elementary universal
lemmas.  That factorization is what `Erdos289/Descent.lean` implements, and it
is why the earlier "layer A" wiring through `Covers` / `CompositionCovers` /
`LiteralizesTarget` is no longer on the critical path: those are the general
Part I machinery, while the descent only needs its specialization, which the
manuscript states as three elementary lemmas.

### The spine — done

`Erdos289/Descent.lean`:

* `CoreStage` is the finite core interface: one common grade, a complete
  torsor of residues under a subgroup `H ≤ ℚ/ℤ`, a strictly positive barrier
  slack `2 - sup W`, and a footprint.
* `TailCovers` is the cofinal tail interface at one grade `h`: states beyond
  that footprint, of grade exactly `h` and mass at most `ε`, whose residues
  cover `G/H`.
* `exists_saturationWitness_of_tailCovers` is *torsor induction* at the class
  `0` (manuscript §5): the tail is asked for `-τ`, its discrepancy lands in
  `H`, and the core state at that element of the torsor cancels it exactly.
* `exists_mem_lowerPrimePowerStage` is *eventual torsor trivialization*
  (manuscript §6): a centered residue is annihilated by its denominator, so it
  lies in every late bounded prime-power stage — the hypothesis `τ ∈ G` is
  eventually free.
* `Support.value_eq_one_of_residue_zero` is *adjacent-lift uniqueness*
  (manuscript §7).
* `cofiniteSaturation_one_of_core_tail` and `erdos289Statement_of_core_tail`
  are §8.

### Provider 1, the finite core — done, unconditionally

`Erdos289/CoreSeed.lean` constructs it.  The manuscript's generic finite torsor
seed is a complete sequence for a finite cyclic group realized by
arbitrarily-light equal-grade switches placed one beyond another.  The complete
sequence used is the simplest one, `c₁ = ⋯ = c_{D-1} = 1`; the manuscript's
binary sequence is shorter but length is not part of the theorem, and the mass
bound `(D-1)/D` is the same either way.

* `exists_ladder` builds `D - 1` switches of increment `1/D`, each beyond the
  previous footprint, from `Erdos289.arbitrarilyLightMobility` (leaves `E` and
  `N`).  State `j` has mass `β + j/D` with `0 < β < 1/2`, and all states share
  one grade and one footprint.
* `exists_lt_nsmul_of_mem_zmultiples` reads the ladder as a torsor: every
  element of a cyclic group of exponent `D` is `j·a` with `j < D`.
* `exists_coreStage` assembles a `CoreStage` with subgroup
  `⟨[1/D]⟩`, barrier slack `1/2`, for every `D ≥ 1` and every constraint.

No lcm bridge is needed for this interface.  The bridge in the manuscript
enlarges the core subgroup from `G_{B₀}` to `G_B`; that only moves work from
the tail provider to the core provider, and the spine does not care which side
does it.

### Provider 2, the cofinal tail — open

`Erdos289.erdos289Statement_of_tailInterface` is Erdős 289 with this as its
only hypothesis: beyond any finite footprint `F`, and for any core class `τ`,
there is `N` such that every grade `h ≥ N` admits an ambient group `G ∋ τ` and
a load `ε < 1/2` with `TailCovers originalConstraint F ⟨[1/D]⟩ G h ε`.

This is where all the arithmetic lives.  The pieces already proved:

* **B1. Usable form of `Π`.** *Done.*
  `Erdos289.comparablePrimes_card_isBigO` states
  `(fun n => n / log n) =O[atTop] (fun n => #(comparablePrimes n))`.

  A note on style, binding for the rest: **an asymptotic statement is
  formalized as an asymptotic statement.**  It is not replaced by an
  inequality valid beyond a hand-picked numerical threshold.  mathlib's
  `Asymptotics` and `Filter.atTop` API is what makes this both faithful and
  short; the first draft of this module took the numerical route and was more
  than twice as long for a strictly less faithful statement.
* **B2. Row supply (manuscript Thm 17.1).** *Done, as an exact statement.*
  * The carrier band: `Erdos289.SignedInverse.bandBase` chooses the comparable
    band so that `b < Q` is automatic; `card_carrierPrimes_ge` shows the only
    carrier lost to the current-stage exclusions is `p` itself; its growth is
    inherited asymptotically from B1 through `bandBase_isBigO` and
    `bandCard_isBigO`.
  * The quadratic-congruence root bound:
    `Erdos289.primePower_squareFiber_card_le_four`, uniform in `p` and `e`.
    The odd branch is the cyclic two-torsion; the `p = 2` branch — which the
    earlier code had flagged as intended but not supplied — is the elementary
    fact that an odd square root of one modulo `2 ^ e` is `±1` modulo
    `2 ^ (e - 1)`.
  * The deletion step:
    `Erdos289.SignedInverse.exists_multiplier_of_goodOrientations_eq_empty`
    and `card_badCarriers_le` (at most twenty-four carriers lost, uniformly).
  * Deduplication and truncation: `Erdos289.SignedInverse.exists_injOn_subset`,
    `chosenCoefficientFiber_card_le_eight`, `card_upperCoefficient_ge`, and the
    assembly `exists_rowCertificate`, which gives a row with pairwise distinct
    coefficients, `#A - 24 ≤ 8 #R` and `#R - ⌊#R/2⌋ ≤ #T`, and distinguished
    centres at least `Q ⌊#R/2⌋ - 1`.
* **B3. Bounded conflict degree.** *Done.*
  `Erdos289.SignedInverse.reservoir_conflictNeighbors_card_le` bounds the
  conflict degree by `2 (max 1 separation + 1)`, independent of the current
  prime power and of the row size.
* **B4. Packing.** *Done, modulo the chunk partition.*
  `Erdos289.exists_compatiblePool_of_binary`.  What remains is to cut a row
  into enough chunks of size `4 (max 1 separation + 1)`.
* **B5. Local profiles.** *Done for the prime rows.*
  `Erdos289.TransverseReservoir.restrictedFold_coversAtGrade_Icc` gives the
  whole epi-grade interval `[a, m - a]` from the endpoint condition, by
  concavity of `h ↦ h (m - h)` (`Erdos289.mul_sub_le_mul_sub_of_between`).
  Proper prime powers use `atom_cyclic_coversAtGrade`; exporting neutral atoms
  to fix their grade is still open.
* **B6. Donor flow.** The running-balance inequality is
  `Erdos289.GradeAggregation.donor_flow_nonneg`; the injective matching it
  supports is not yet written.
* **B7. Interval aggregation.** `Erdos289.GradeAggregation.exists_grades_of_mem_sum_Icc`
  is the Minkowski step and `AffineCorrection.intervalSpectrum_cofinite` the
  eventual-ray step.  What is missing is the overlap estimate that feeds them.
* **B8. Cost summability.** Not started.  The invariant content is
  `∑ᵢ cᵢ < ∞ ⇒ ∑_{i>N} cᵢ → 0`, i.e. the tail load can be pushed below the
  fixed slack `1/2` by moving the base stage outward.
* **B9. Tempered prefix.** *No longer needed as a separate obligation.*
  In this factorization the tail is required to be admissible for
  `constraintBeyond c F`, which is exactly "compatible with every core state";
  temperedness is then the tail provider's own obligation to still exist, not a
  separate interface.

### Layer C — final assembly

Discharged: `Erdos289.erdos289Statement_of_tailInterface`.

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
