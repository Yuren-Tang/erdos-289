# Formalization roadmap

This file records what is proved, what is not, and what the remaining work is.
It is the document to read before trusting any summary sentence elsewhere in
the repository, and it is the only place where completion status is recorded:
module and theorem names describe mathematics, not progress.

The mathematics being formalized is the two-part descent:

* **Part I** — the universal graded affine-correction theorem (`AffineCorrection/`);
* **Part II** — the descent from that theorem to Erdős problem 289 (`Erdos289/`).

## 0. Status in one line

The universal core, the five external inputs, the reciprocal infrastructure,
the descent spine and the **finite core stage** are proved unconditionally and
are transitively axiom-audited.  **The unconditional Erdős 289 theorem is not
proved.**  Exactly one obligation remains: the manuscript's *cofinal tail
interface*, isolated as the explicit hypothesis of
`Erdos289.smallBlockSaturation_of_tailInterface`.

## 1. Two ways of counting the external inputs

The design notes behind this development name the hard external inputs in two
different ways, and the difference is a recurring source of confusion about how
far along the project is.

| landed | note | inputs | where the signed-inverse row certificate sits |
| --- | --- | --- | --- |
| 19:00 `411a3e8d` | *post-bite leaf-DAG freeze* | `E, N, T, P, D` | `T` is one of them, and "the hard part is the quantitative carrier supply/resource theorem" |
| 19:55 `91409485` | *hard-leaf interface audit* | `E, N, Π, P, D` | not one of them: "derived finite arithmetic downstream of `Π`" |
| 20:14 `2b38a87b` | *Lean 4.33 zero-axiom route* | `E, N, Π, P, D` | same |

(Times are the commit dates in `Yuren-Tang/research-workbench` on 2026-08-17.
A shallow clone shows all three in one grafted commit and cannot order them.)

**The two lists disagree about labelling, not about content.**  Both say the
same thing has to be proved: the quantitative row certificate.  One calls it a
fifth input named `T`; the other splits it into the genuinely external input
`Π` plus arithmetic derived below it.  `T` is, up to naming, `Π` together with
that derived arithmetic.

This package uses the `Π` list.  It is the later one, it is the finer
decomposition — the genuinely external input is isolated to a single
prime-counting statement — and it is what the code implements.

The consequence for reading the status: all five of `E, N, Π, P, D` are proved,
*and* the content that the other list calls `T` is not finished.  Only `T`'s
atom-level ingredients are: complementary signed-inverse pairs, the bounded
quadratic shape of downwardness exceptions, the uniform four-point
coefficient-fibre bound, and the reservoir and pool constructors.  So "all five
are complete" and "a large amount of work remains" are both true and not in
tension.

What remains is not a further conceptual input.  It is the arithmetic
realization theorem the manuscript calls "the last genuinely arithmetic
realization theorem", together with its assembly against the universal core.

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

### The five external inputs

| label | statement | declaration |
| --- | --- | --- |
| `E` | every constrained unit-fraction presentation fibre is inhabited | `Erdos289.unitFractionRefinementCofinality` |
| `N` | the neutral grade-one fibre has arbitrarily light remote points | `Erdos289.remoteLightNeutralGradeOne` |
| `Π` | some ratio `Λ ≥ 2` makes the band `(n, Λn]` carry `≫ n / log n` primes | `Erdos289.ComparableBand`; every `Λ ≥ 3` is one (`Erdos289.bandPrimes_card_isBigO`), the smallest witness being `Erdos289.comparableBandThree` |
| `P` | Haxell's `2Δ`-thick chunk packing | `Erdos289.IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le` |
| `D` | Dias da Silva–Hamidoune restricted-fold image growth | `Erdos289.RestrictedFold.image_card_lower_bound` |

`P` and `D` are vendored from Apache-2.0 Lean sources; see `THIRD_PARTY.md`.
The two theorems themselves are due to Haxell and to Dias da Silva and
Hamidoune; see the references in `README.md`.

### Reciprocal infrastructure

Path-support partial monoid with additive value and grade; binary and ternary
blocks and their exact identities; upper blockification; the constructive
remote separated Egyptian presentation and its rational-target composition;
arbitrarily light mobility; the prime-power filtration of `ℚ/ℤ` and its simple
fibres; signed-inverse atoms and their transversality; local profiles and their
grade intervals; the quantitative reservoir interface and its packing; the row
certificate of a prime-power current; the unit selector; the descent spine; the
finite core stage; the identification of the intrinsic statement with the
source sentence.

### Faithfulness of the statement

Three propositions are kept apart, and the relations between them are proved:

```text
SmallBlockSaturation  →  IntervalSaturation  ↔  ErdosProblem289
  intervalSaturation_of_smallBlock    erdosProblem289_iff_intervalSaturation
```

The second arrow is an equivalence, not an identification asserted in prose.
Forwards, a component of a support is convex, hence an integer interval.
Backwards, an integer interval is connected
(`Erdos289.denominatorIcc_preconnected`), so a family of pairwise non-adjacent
intervals has exactly as many components as members
(`Erdos289.saturationWitness_of_intervalFamily`).

* `Erdos289.ErdosProblem289` is the sentence of problem 289 itself, with
  positivity of every lower endpoint and with non-adjacency, written out
  directly over integer intervals.  `Erdos289Test/Smoke.lean` checks by
  `Iff.rfl` that it is that sentence and not a paraphrase, and derives from it
  the weaker form used by the `erdos_289` entry of
  `google-deepmind/formal-conjectures`, which omits non-adjacency.
* `Erdos289.IntervalSaturation` is the same problem stated intrinsically, over
  the problem's own block-size class `nontrivialBlockSizes = {n | 2 ≤ n}`.
* `Erdos289.SmallBlockSaturation` is the strengthening this development proves
  conditionally: the same over `smallBlockSizes = {2, 3}`.

The stronger `{2,3}` theorem is never called "the Erdős 289 statement".

## 3. The two interfaces, and which one is left

The active authorial surface (clean qualitative proof v4.1) factors the whole
descent through exactly two interfaces and three elementary universal lemmas.
That factorization is what `Erdos289/Descent.lean` implements, and it is why
the general Part I machinery — `Covers` / `CompositionCovers` /
`LiteralizesTarget` — is not on the critical path: the descent needs only its
specialization, which the manuscript states as three elementary lemmas.

### The spine — done

`Erdos289/Descent.lean`:

* `CoreStage` is the finite core interface: one common grade, a complete torsor
  of residues under a subgroup `H ≤ ℚ/ℤ`, a strictly positive barrier slack
  `2 - sup W`, and a footprint.
* `TailCovers` is the cofinal tail interface at one grade `h`: states
  compatible with that footprint, of grade exactly `h` and mass at most `ε`,
  realizing every target of `G` modulo `H`.  The bare interface assumes neither
  `H ≤ G` nor that the realized residue lies in `G`; only along the filtration
  chain, where the groups do increase, is this literally coverage of a
  quotient.
* `exists_saturationWitness_of_tailCovers` is *torsor induction* at the class
  `0` (manuscript §5): the tail is asked for `-τ`, its discrepancy lands in
  `H`, and the core state at that element of the torsor cancels it exactly.
* `exists_mem_lowerPrimePowerStage` is *eventual torsor trivialization*
  (manuscript §6): a centered residue is annihilated by its denominator, so it
  lies in every late bounded prime-power stage — the hypothesis `τ ∈ G` is
  eventually free.
* `Support.value_eq_one_of_residue_zero` is *adjacent-lift uniqueness*
  (manuscript §7): the selector interval `(0, 2)` is cut out by the two lifts
  of the target residue adjacent to the target, so a centered residue of zero
  pins the value.
* `cofiniteSaturation_one_of_core_tail` and `smallBlockSaturation_of_core_tail`
  are §8.

### Interface 1, the finite core — done, unconditionally

`Erdos289/CoreSeed.lean` constructs it.  The manuscript's generic finite torsor
seed is a complete sequence for a finite cyclic group realized by
arbitrarily-light equal-grade switches placed one beyond another.  The complete
sequence used is the simplest one, `c₁ = ⋯ = c_{D-1} = 1`; the manuscript's
binary sequence is shorter, but length is not part of the theorem, and the mass
bound `(D-1)/D` is the same either way.

* `exists_ladder` builds `D - 1` switches of increment `1/D`, each beyond the
  previous footprint, from `Erdos289.arbitrarilyLightMobility` (inputs `E` and
  `N`).  State `j` has mass `β + j/D`, and all states share one grade and one
  footprint.
* `exists_lt_nsmul_of_mem_zmultiples` reads the ladder as a torsor: every
  element of a cyclic group of exponent `D` is `j·a` with `j < D`.
* `exists_coreStage` assembles a `CoreStage` with subgroup `⟨[1/D]⟩` and
  **any** prescribed barrier slack `s ∈ (0,1)`, for every `D ≥ 1` and every
  constraint.  The slack is a parameter, not the number `1/2`.

No lcm bridge is needed here.  The bridge in the manuscript enlarges the core
subgroup from `G_{B₀}` to `G_B`; that only moves work from the tail interface
to the core interface, and the spine does not care which side does it.

### Interface 2, the cofinal tail — open, and delimited

`Erdos289.smallBlockSaturation_of_tailInterface` is the `{2,3}` strengthening
with this as its only hypothesis: for any finite core footprint `F` and any
core class `τ`, there is `N` such that every grade `h ≥ N` admits an ambient
group `G ∋ τ` and a load `ε < s` with
`TailCovers originalConstraint F ⟨[1/D]⟩ G h ε`, where `D` and the slack `s`
are parameters of the theorem.

**A correction, recorded because it changed the interface.**  The tail was
originally required to lie entirely *beyond* the core's footprint.  That is
strictly stronger than the manuscript's requirement, which is that every tail
state be *physically compatible* with every core state, and it is not
achievable: the atoms of a row at current `Q` reach only as far as the
truncation rank allows, and the band size bounds that rank, whereas a core
footprint can lie arbitrarily far out.  `Erdos289.constraintAvoiding` is the
faithful condition — the constraint together with the footprint and its
separation neighbourhood as obstacles — and `TailCovers`, `TailStage` and the
stage chain now use it.  Remoteness implies it
(`avoids_avoiding_of_avoids_beyond`), so nothing that used to fit stopped
fitting.  On the arithmetic side this is the manuscript's *core-obstacle
deletion*, and it costs at most twice the obstacle's size
(`Erdos289.SignedInverse.card_obstructed_le`).

The scaffolding that turns arithmetic into the hypothesis is complete.

* `TailStage` is `TailCovers` plus the footprint the next stage must clear.
* `TailStage.comp` is torsor induction one level down; `tailStage_empty` is the
  base; `tailStage_chain` iterates it along a chain of subgroups.
* `tailCovers_of_stages` is the resulting interface: a finite chain of stages
  whose grades sum to `h` and whose loads sum to at most `ε`.
* `tailStage_of_pool` makes one current one link of that chain, and its
  hypothesis is mechanism-independent: a compatible transverse pool inside a
  finite footprint that reaches its local target at grade `h`
  (`CompatibleTransversePool.CoversAtGrade`) is a stage from
  `lowerPrimePowerStage Q` to `primePowerStage Q` with load `h · maxMass`.  No
  arithmetic of the current appears in it.
  `tailStage_of_pool_of_restrictedFold` is the prime-current route, which
  supplies that target from the Dias da Silva–Hamidoune interval
  (`CompatibleTransversePool.coversAtGrade_of_restrictedFold`).
* `exists_pool_state_of_class` is what `tailStage_of_pool` runs on, and
  `exists_compatiblePool_of_binary_of_card` produces the pool from a row that
  is merely large enough, together with the chunk count it preserves.

At a **prime** current the whole passage from a band of carriers to a tail
stage is now proved, end to end.

* `Erdos289.SignedInverse.exists_rowReservoir` turns the row certificate into a
  reservoir of binary atoms: exactly one atom per surviving carrier (distinct
  coefficients give starts at least `Q - 1` apart), each avoiding the obstacle,
  each of mass below `2 / (Q t - 1)`.
* `Erdos289.SignedInverse.card_simpleValues_rowReservoir`: at a prime current
  the image in the simple fibre is as large as the row, and the injectivity
  passes to the packed subpool
  (`TransverseReservoir.card_simpleValues_of_subset`).
* `Erdos289.SignedInverse.exists_tailStage_of_band` composes row certificate,
  reservoir, pool and stage, with `Λ, d, t`, the surviving size `m` and the
  interval endpoint `a` all parameters, and one supply inequality.
* `Erdos289.SignedInverse.eventually_exists_tailStage` is its asymptotic form:
  every sufficiently large prime current is a tail stage, provided the total
  demand of the selections and the packing is `o(Q / log Q)`.

What is left is therefore three items, one heavy and two coupled.

* **T1 (heavy), the proper prime powers.** The target is mechanism-independent
  and is exactly what the descent consumes:
  `Erdos289.CompatibleTransversePool.CoversAtGrade`, the statement that every
  class of the simple fibre is the class of a compatible subfamily of exactly
  `h` atoms.  This is §9's local object `I(J)` of one simple jump, realized
  physically; both the prime and the proper-prime-power arithmetic serve it,
  the split between them is internal, and §10 records that it "is not an
  invariant of the qualitative theorem".

  At a prime current the target is proved
  (`Erdos289.CompatibleTransversePool.coversAtGrade_of_restrictedFold`, reached
  through `Erdos289.SignedInverse.exists_tailStage_of_band`).  At `Q = p ^ e`
  with `e ≥ 2` the simple fibre is cyclic of order `p`, the row's atoms need
  not have distinct classes, and Dias da Silva–Hamidoune is not the mechanism.

  The cyclic mechanism reaching the target is proved:
  `Erdos289.CompatibleTransversePool.coversAtGrade_of_two_classes` takes a pool
  carrying two *distinct* classes `u ≠ v` in disjoint stocks and produces
  `CoversAtGrade h maxMass` for every `h ≥ p`.  Its combinatorial core is
  `Erdos289.exists_multiplicities_of_two_simpleFibreClasses`: writing
  `d = v - u ≠ 0`, the class of `k₁` atoms of class `u` and `k₂` of class `v` is
  `h·u + k₂·d`, and `d` is invertible, so `k₂` is determined modulo `p` and its
  least representative is below `p ≤ h`.

  The classes themselves are now identified arithmetically, uniformly in the
  exponent.  `Erdos289.SignedInverse.coefficient_nsmul_atom_simpleFibreClass`
  pins an atom's class by the exact equation `k • class = generator`, where `k`
  is its current coefficient and the generator is the class of `1/Q`: the
  atom's residue is `1/(Q k)` plus a companion in the lower stage, and
  `k · (1/(Q k)) = 1/Q` on the nose.  Since the fibre has prime order `p` and
  `k` is a unit modulo `p`, that equation determines the class, and
  `atom_simpleFibreClass_eq_iff` says two atoms share a class exactly when
  their coefficients agree modulo `p`.  (The prime-current injectivity is now a
  corollary rather than a separate argument.)

  What remains is therefore one arithmetic statement, in coefficients:
  **at a proper prime power the row contains, in two distinct residue classes
  modulo `p`, at least `h` coefficients in the first and at least `p - 1` in
  the second.**  Nothing else about the current enters.

  One case is settled negatively and needs the other mechanism.  At `p = 2`
  every coefficient is a unit modulo `2`, hence odd, so all atoms of a row
  share the single nonzero class of a two-element fibre and no two distinct
  classes exist.  There the padding route — neutral atoms of grade one and
  class zero — is not an alternative but a necessity, and it needs an interface
  slightly wider than `CoversAtGrade` as currently stated, since a neutral atom
  is not transverse and so cannot belong to the pool.

  The alternative mechanism — the cyclic orbit
  (`Erdos289.TransverseReservoir.atom_cyclic_coversAtGrade`) with padding by
  neutral atoms of grade one and class zero — would sit below the same
  `CoversAtGrade` interface, and the choice between the two is not visible to
  the descent.

  The chain cannot skip a current: `lowerPrimePowerStage Q'` contains
  `annihilatorStage R` for every prime power `R < Q'`, so the stages must run
  through *all* prime powers between the core exponent and the top.
* **T2 and T3 are one coupled problem, and it is unresolved.** Each ingredient
  is in place:

  * grades — `Erdos289.GradeAggregation.exists_grades_of_mem_sum_Icc` for the
    Minkowski step, `AffineCorrection.intervalSpectrum_cofinite_of_eventually`
    for the eventual ray, and the per-current interval `[a, m - a]` of
    `exists_tailStage_of_band`;
  * loads — `Erdos289.exists_rank_of_cost_le`, which lowers a stage's load by
    raising its truncation rank, and `Erdos289.sum_lt_of_le_geometric`, which
    keeps a geometrically prescribed run of loads under the barrier slack;
  * supply — `Erdos289.SignedInverse.eventually_demand_le_card_carrierPrimes`,
    which meets any demand growing more slowly than `Q / log Q`.

  What does not yet exist is a *simultaneous* schedule: a single choice of
  `m(Q)`, `t(Q)`, `a(Q)` and `h(Q)`, over the currents the chain must use,
  satisfying the grade-overlap estimate `A_{j+1} ≤ B_j + 1`, the load
  summability, the supply inequality, and the restricted-fold endpoint
  condition at once — while the chain runs through every prime power.  The
  constraints pull against each other: raising the truncation rank lowers the
  load but raises the demand, and raising the surviving size widens the grade
  interval but raises the demand again.  Until such a schedule is proved, T2
  and T3 are an open coupled asymptotic parameter-balancing problem.  There is
  no presently known need for new external number theory in it.

**T4, the endpoints — done.**  The bottom is
`Erdos289.lowerPrimePowerStage_le_zmultiples_coreExponent`: taking the core
modulus to be the current's core exponent `lcm(1, …, Q-1)` makes the chain
start exactly where the core torsor ends, because
`Erdos289.annihilatorStage_eq_zmultiples` identifies the `q`-torsion of `ℚ/ℤ`
with `⟨[1/q]⟩`.  The converse inclusion, needed to place a later current above
the core, is
`Erdos289.zmultiples_reciprocalResidue_le_lowerPrimePowerStage`.  The top is
`Erdos289.exists_mem_lowerPrimePowerStage`, already proved.

#### The arithmetic already proved for T1–T3

* **B1. Usable form of `Π`.** *Done, and asymptotic.*
  `Erdos289.ComparableBand` packages a ratio `Λ ≥ 2` together with
  `(fun n => n / log n) =O[atTop] (fun n => #(bandPrimes Λ n))`.  The ratio is
  existentially quantified, so no particular ratio enters the mathematics
  downstream.  `Erdos289.bandPrimes_card_isBigO` proves that *every* integer
  ratio at least three is a comparable band: subtracting mathlib's two
  Chebyshev estimates leaves the main term `(Λ - 2)(log 2) n`, positive exactly
  from `Λ = 3` on.  `Erdos289.comparableBandThree` is the smallest witness this
  mechanism supplies; whether a stronger route eventually reaches ratio two is
  irrelevant, since the statement quantifies the ratio away.

  A note on style, binding for the rest: **an asymptotic statement is
  formalized as an asymptotic statement.**  It is not replaced by an inequality
  valid beyond a hand-picked numerical threshold.  mathlib's `Asymptotics` and
  `Filter.atTop` API is what makes this both faithful and short; the first
  draft of this module took the numerical route and was more than twice as long
  for a strictly less faithful statement.
* **B2. Row supply (manuscript Thm 17.1).** *Done, parametrically.*
  * The carrier band: `Erdos289.SignedInverse.bandBase` chooses the band base
    so that `b < Q` is automatic; `card_carrierPrimes_ge` shows the only
    carrier lost to the current-stage exclusions is `p` itself; its growth is
    inherited asymptotically from B1 through `bandBase_isBigO` and
    `bandCard_isBigO`, both stated for an arbitrary `ComparableBand`.
  * The quadratic-congruence root bound:
    `Erdos289.primePower_squareFibre_card_le_four`, uniform in `p` and `e`.
    This four *is* sharp and uniform, so it is a genuine constant of the
    theorem.  The odd branch is the cyclic two-torsion; the `p = 2` branch is
    the elementary fact that an odd square root of one modulo `2 ^ e` is `±1`
    modulo `2 ^ (e - 1)`.
  * The deletion step:
    `Erdos289.SignedInverse.exists_multiplier_of_goodOrientations_eq_empty`
    exhibits a multiplier in `[1, Λ)`, and `card_badCarriers_le` bounds the
    carriers lost by `4 (Λ - 1)`, uniformly in the current.  The two signed
    targets of one multiplier do not double the four-point fibre bound, because
    the two worst cases never coincide: where a square fibre has four points the
    current is a power of two beyond the third, and there `-1` is not a square,
    so only one of the two signed targets is hit
    (`Erdos289.primePower_signedSquareFibre_card_le_four`).
  * Deduplication and truncation: `Erdos289.SignedInverse.exists_injOn_subset`,
    `sectionCoefficientFibre_card_le` (at most `2d` carriers share a
    coefficient, for any scale `d` with `Q² + 1 < (n+1)^{d+1}`),
    `card_upperCoefficient_ge`, and the assembly
    `Erdos289.SignedInverse.exists_rowCertificate`, which gives a row `R` with
    pairwise distinct coefficients, `#A - 4(Λ-1) ≤ 2d · #R`, a truncation `T`
    with `#R - t ≤ #T` at any rank `t`, and distinguished centres at least
    `Q·t - 1` — hence remoteness beyond any fixed footprint and a corresponding
    mass bound.  The band ratio `Λ`, the fibre scale `d` and the truncation
    rank `t` are all parameters.
* **B3. Bounded conflict degree.** *Done.*
  `Erdos289.SignedInverse.reservoir_conflictNeighbors_card_le` bounds the
  conflict degree by `2 (max 1 separation + 1)`, independent of the current
  prime power and of the row size.  The constant is the geometry of the
  constraint, not a choice.
* **B4. Packing.** *Done.*
  `Erdos289.exists_compatiblePool_of_binary_of_card`: a binary reservoir whose
  row has at least `2Δ = 4 (max 1 separation + 1)` atoms carries a compatible
  transverse pool, of at least as many atoms as there are chunks; the factor
  two is Haxell's, and `Δ` is B3.  The chunk partition is supplied by
  `Erdos289.IndependentTransversal.exists_chunkPoolPartition`.
* **B5. Local profiles.** *Done for the prime rows.*
  `Erdos289.TransverseReservoir.restrictedFold_coversAtGrade_of_mem_Icc` gives
  the whole epi-grade interval `[a, m - a]` from the endpoint condition, by
  concavity of `h ↦ h (m - h)` (`Erdos289.mul_sub_le_mul_sub_of_between`).
  Proper prime powers use `atom_cyclic_coversAtGrade`; exporting neutral atoms
  to fix their grade is still open.
* **B6. Donor flow.** The running-balance inequality is
  `Erdos289.GradeAggregation.donor_flow_nonneg`; the injective matching it
  supports is not yet written.
* **B7, B8.** See T2 and T3, which are one coupled problem.
* **B10. Core-obstacle deletion.** *Done.*
  `Erdos289.SignedInverse.card_obstructed_le`: at most twice the obstacle's
  size many members of a row have an atom meeting the obstacle, whatever the
  current and the row.  Each obstacle point lies in at most two of the row's
  binary blocks, and the row's starts are distinct.
* **B11. Supply.** *Done, asymptotically.*
  `Erdos289.SignedInverse.eventually_demand_le_card_carrierPrimes`: a demand
  growing more slowly than `Q / log Q` is eventually met by the band.  The
  coefficient-fibre scale needed for it is the absolute constant two
  (`Erdos289.SignedInverse.scale_two_of_lt`), because the band base is a fixed
  fraction of the current.
* **B9. Tempered prefix.** *No longer a separate obligation.*
  In this factorization the tail is required to be admissible for
  `constraintBeyond c F`, which is exactly "compatible with every core state";
  temperedness is then the tail's own obligation to still exist, not a separate
  interface.

### Final assembly

Discharged: `Erdos289.smallBlockSaturation_of_tailInterface`, and through
`Erdos289.erdosProblem289_of_smallBlockSaturation` the source sentence itself.

## 4. Discipline for the remaining work

Unproved obligations are **explicit theorem parameters or certificate structure
fields, never global axioms**.  `scripts/source_scan.py` rejects `axiom`, and
`Audit.lean` pins the transitive axiom set of every exported theorem with
`#guard_msgs`, so an accidental assumption cannot enter silently.

A conditional theorem of the shape

```text
(quantitative row certificate) → SmallBlockSaturation
```

is an acceptable and intended intermediate deliverable.  A global axiom
asserting the same thing is not.

Numerical witnesses stay witnesses.  Replacing the band ratio `4`, the core
slack, the truncation rank or a placement threshold by another valid choice
must require changing only the proof or definition that constructs the
corresponding abstract datum — never a downstream mathematical statement.  See
`DESIGN.md`.
