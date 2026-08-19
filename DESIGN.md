# Design contract

This package implements mathematical objects already fixed independently of
Lean.  Its declarations are not permitted to weaken a universal construction
to a convenient witness.

For every new layer, development proceeds in this order:

1. **Mathematical object.** State the intrinsic object, morphism, fibre,
   image, universal property, or canonical extremum required by the proof.
2. **Working language.** Replace the categorical presentation by an equivalent
   ordinary formulation only after the intrinsic object has been fixed.
3. **Lean realization.** Use the strongest stable mathlib API implementing that
   working formulation.  A convenient special witness is not an implementation
   of a universal object unless equivalence has already been proved.

The current core has the following audited correspondence.

| Mathematical object | Working language | Lean declaration |
| --- | --- | --- |
| multiplication-domain subobject and multiplication graph | functional partial commutative addition | `PartialAddCommMonoid` |
| coherent observation functor and natural transformation | transition maps commuting with exact observation | `ObservationSystem` |
| `∫ B(UQ × M)` | strict triples `(u; d, m)` | `GradedCorrection.Hom` |
| correction fibre | subtype cut out by transition and grade equalities | `GradedCorrection.Required` |
| realizer pullback | state and required point with equal observations | `Realizer` |
| regular epimorphic cover in `Set` | surjective pullback projection | `Covers` |
| compatible-composition correspondence | two realizers and a defined physical sum | `CompatibleRealizer` |
| regular epi onto the composite fibre | surjectivity of the canonical composite map | `CompositionCovers` |
| pullback along the distinguished target section | realizers over the target point | `TargetRealizer` |
| factorization through the exact fibre | exact-value equality for every target realizer | `LiteralizesTarget` |
| image under grade of the exact fibre of a physical family | membership by an exact physical witness lying in the family | `exactSpectrum` |
| path-support multiplication domain | graph-disjoint induced union | `Support.GraphDisjoint`, `supportPCM` |
| coproduct of physically disjoint support graphs | graph isomorphism and induced component equivalence | `Support.GraphDisjoint.unionGraphIso`, `support_grade_additive` |
| local reciprocal coordinate calculations | exact rational identities confined to the arithmetic boundary | `upper_blockification_identity`, `endpoint_switch_identity`, `neutral_grade_one_identity` |
| canonical length-two atom | connected two-vertex induced support | `binaryBlock`, `binaryBlock_blockSize` |
| canonical length-three atom and endpoint switch | connected three-vertex support containing its shifted binary face | `ternaryBlock`, `endpoint_inclusion_switch` |
| prime-power filtration of `ℚ/ℤ` | joins of multiplication-kernel subgroups and their subquotient | `lowerPrimePowerStage`, `primePowerStage`, `PrimePowerSimpleFibre` |
| filtered-transverse physical lift | stage factorization with nonzero image in the associated simple quotient | `Support.FilteredTransverse` |
| compatible transverse reservoir | global point of the pairwise-compatible reservoir subobject | `CompatibleTransversePool` |
| finite compatible pool colimit | union as the iterated defined product in the physical PCM | `aggregateSupport`, `aggregateSupport_grade`, `aggregateSupport_value` |
| `P(M × B)` with Minkowski tensor | powerset of the additive grade-resource monoid | `GradeResource` and its `CommMonoid`/`IsQuantale` instances |
| free enriched transitive closure | join of weights of all quiver paths | `FreeClosure.hom`, `FreeClosure.hom_le_of_edge_le` |
| finite cyclic ladder | orbit of the free monogenic action | `CyclicLadder.orbit`, `CyclicLadder.GeneratesIn` |
| fixed-cardinality sumset | image of the additive fold from `h`-element subobjects | `RestrictedFold.Domain`, `RestrictedFold.Surjective` |
| restricted-fold image growth | cardinality of the canonical fold image | `RestrictedFold.image_card_lower_bound` |
| local simple-fibre profile | image of the joint observation/grade map | `localProfile`, `CoversAtGrade` |
| coordinate-free prime-fibre coverage | DdS transported through an additive equivalence | `RestrictedFold.coversAtGrade_of_card_bound` |
| quota packing | global point of the independent feasibility subobject | `IndependentTransversal.Feasible`, `IndependentTransversal.HasPacking` |
| independent chunk transversal | global section of the one-per-block independent subobject | `IndependentTransversal.ChunkFeasible`, `IndependentTransversal.hasChunkPacking_of_two_mul_maxDegree_le` |
| constrained unit-fraction presentation | nonempty exact weight fibre after every finite constraint | `UnitFractionPresentation`, `UnitFractionRefinementCofinality` |
| remote separated Egyptian realization | least arithmetic-progression crossing followed by numerator-decreasing greedy tail | `separatedEgyptianPresentation`, `unitFractionRefinementCofinality` |
| positive-rational refinement | iterated fibrewise union beyond enlarged compact constraints | `RationalPresentation.unionBeyond`, `rationalPresentation_of_pos` |
| same-grade mobility fibre | binary faces and ternary endpoint extensions of one remote presentation | `SameGradeDeformation`, `RationalPresentation.endpointDeformation` |
| light mobility from reciprocal fibres | positive-excess blockification plus the exact finite neutral grade tower | `PositiveExcessBlockification`, `NeutralGradePoint`, `arbitrarilyLightMobility_of_refinement_neutral` |
| neutral grade-one deformation | nonempty `(ΔW,Δg)=(0,1)` fibre at arbitrarily small load | `NeutralGradeOnePoint`, `RemoteLightNeutralGradeOne`, realized by `remoteLightNeutralGradeOne` |
| comparable prime band | a ratio `Λ ≥ 2` whose band `(n, Λn]` carries `≫ n / log n` primes | `ComparableBand`, witnessed at `Λ = 4` by `comparableBandFour` |
| cofinal union of touching grade intervals | principal final ideal | `intervalSpectrum_cofinite`, `cofiniteSaturation_of_interval_witnesses` |
| epi-grade interval of a prime row | concavity of `h ↦ h (m - h)` on the symmetric range | `mul_sub_le_mul_sub_of_between`, `TransverseReservoir.restrictedFold_coversAtGrade_Icc` |
| coefficient fibre of a carrier band | roots of a quadratic congruence in `(ZMod (p^e))ˣ` | `primePower_squareFibre_card_le_four`, `SignedInverse.sectionCoefficientFibre_card_le` |
| row certificate of a prime-power current | deletion, deduplication and rank truncation of the band | `SignedInverse.exists_rowCertificate` |
| finite homogeneous affine prefix | complete torsor of a finite cyclic residue group at one grade | `CoreStage`, `exists_coreStage` |
| cofinal defect-controlled correction system | residue cover of `G/H` at one grade beyond a footprint | `TailCovers` |
| torsor induction | cancellation of the tail discrepancy inside the core torsor | `exists_saturationWitness_of_tailCovers` |
| eventual torsor trivialization | finite additive order of a centered residue | `exists_mem_lowerPrimePowerStage` |
| cofinite exact grade spectrum, over a class of block sizes | principal final ideal in component count | `CofiniteSaturation`, `IntervalSaturation`, `SmallBlockSaturation` |
| the source-level sentence of problem 289 | eventually many pairwise non-overlapping, non-adjacent integer intervals of reciprocal sum one | `ErdosProblem289`, `erdosProblem289_of_intervalSaturation` |

The following substitutions are forbidden unless an equivalence theorem is
first supplied:

- replacing a least, greatest, initial, terminal, limit, colimit, image, or
  fibre construction by one merely sufficient witness;
- reintroducing whole-family homogeneity or all-pairs compatibility where the
  intrinsic interface is a graded fibre or compatible-composition epi;
- exposing proof coordinates or historical bookkeeping in a public interface;
- importing an E289 arithmetic or combinatorial module into the universal
  affine-correction core;
- replacing a parametric statement in the public API by one of its numerical
  specializations.

Numerical constants are governed by the same rule.  A constant may occur in a
public statement only if it belongs to the source problem, to an exact
identity, to a sharp or uniform structural theorem, or to a genuinely canonical
extremum.  A constant obtained by specializing an already-parametric theorem is
a *witness*: it may occur inside a proof, or as a clearly labelled corollary,
but it must not replace the parametric theorem in the public API, in the
documentation, or in the dependency architecture.

The operative test: replacing a witness such as the band ratio `4`, the core
slack `1/2`, the truncation fraction, or a coarse placement threshold by
another valid witness must require changing only the proof or the definition
that constructs the corresponding abstract datum — never a downstream
mathematical statement.

Likewise an asymptotic statement is formalized as an asymptotic statement, and
is never replaced by an inequality valid beyond a hand-picked threshold.

Naming follows the mathematics: modules and declarations are named after the
objects and theorems they concern, not after their position in the dependency
graph or their completion status.  Words such as "provider", "leaf" or
"bridge", and any statement about what remains to be done, belong in
`ROADMAP.md`.

Engineering policy for production modules:

- Lean and mathlib are pinned to `v4.33.0`;
- `autoImplicit` and `relaxedAutoImplicit` are disabled;
- imports are explicit; production code does not use bare `import Mathlib`;
- unproved obligations are explicit theorem parameters or certificate fields,
  never global axioms;
- acceptance requires a local build, a source scan, and a transitive axiom
  audit of exported theorems.
