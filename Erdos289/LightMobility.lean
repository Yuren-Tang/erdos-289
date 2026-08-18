module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.EndpointConfigurations
public import Erdos289.UpperBlockification
public import Erdos289.DeformationComposition
public import Erdos289.EgyptianRefinement
import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Arbitrarily-light exact mobility

Upper blockification creates a small positive excess at a known component cost.
An endpoint deformation removes that excess from the desired value difference,
and an equally remote neutral tower pays exactly the component cost.  Only the
intrinsic fibre interfaces survive in the resulting theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The two hard reciprocal fibres E and N imply arbitrarily-light mobility. -/
theorem arbitrarilyLightMobility_of_refinement_neutral
    (hE : UnitFractionRefinementCofinality)
    (hN : RemoteLightNeutralGradeOne) :
    ArbitrarilyLightMobility := by
  intro q hq c ε hε
  have hsixth : 0 < ε / 6 := by linarith
  obtain ⟨b⟩ := positiveExcessBlockification_of_unitFractionRefinement
    hE q hq c (ε / 6) hsixth
  let cB := constraintBeyond c b.support
  obtain ⟨w⟩ := rationalPresentation_of_pos hE b.excess b.excess_pos
    (endpointConstraint cB)
  let d : SameGradeDeformation b.excess cB := w.endpointDeformation
  let baseLower : Support := d.upper
  let baseUpper : Support := b.support ∪ d.lower
  have hbaseLower : baseLower.Admissible smallBlockSizes c := by
    exact admissible_of_admissible_beyond c d.upper_admissible
  have hbaseUpper : baseUpper.Admissible smallBlockSizes c := by
    exact Support.admissible_unionBeyond c b.admissible d.lower_admissible
  have hbaseValue : baseUpper.value = baseLower.value + q := by
    change (b.support ∪ d.lower).value = d.upper.value + q
    rw [Support.value_union
        (support_disjoint_of_avoids_beyond c d.lower_admissible.2.1),
      b.value_eq, d.value_eq]
    ring
  have hbaseGrade : baseUpper.grade = baseLower.grade + b.atoms := by
    change (b.support ∪ d.lower).grade = d.upper.grade + b.atoms
    rw [grade_union_of_pairBeyond c (F := b.support)
        (by intro z hz; exact hz) d.lower_admissible.2.1,
      b.grade_eq, d.grade_eq]
    omega
  have hbaseLight : baseLower.value < ε / 2 := by
    have hlower : d.lower.value < 2 * b.excess := by
      simpa [d] using w.endpointDeformation_lower_lt_two_mul b.excess_pos
    change d.upper.value < ε / 2
    rw [d.value_eq]
    linarith [b.excess_lt]
  let footprint := pairFootprint baseLower baseUpper
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨t⟩ := neutralGradePoint hN b.atoms
    (constraintBeyond c footprint) (ε / 2) hhalf
  refine ⟨{
    lower := baseLower ∪ t.upper
    upper := baseUpper ∪ t.lower
    lower_admissible := admissible_union_of_pairBeyond c
      (F := footprint)
      (by intro z hz; exact Finset.mem_union_left _ hz)
      hbaseLower t.upper_admissible
    upper_admissible := admissible_union_of_pairBeyond c
      (F := footprint)
      (by intro z hz; exact Finset.mem_union_right _ hz)
      hbaseUpper t.lower_admissible
    value_eq := ?_
    grade_eq := ?_
    lower_value_lt := ?_ }⟩
  · rw [value_union_of_pairBeyond c (F := footprint)
          (by intro z hz; exact Finset.mem_union_right _ hz)
          t.lower_admissible.2.1,
        value_union_of_pairBeyond c (F := footprint)
          (by intro z hz; exact Finset.mem_union_left _ hz)
          t.upper_admissible.2.1,
        hbaseValue, t.value_eq]
    ring
  · rw [grade_union_of_pairBeyond c (F := footprint)
          (by intro z hz; exact Finset.mem_union_right _ hz)
          t.lower_admissible.2.1,
        grade_union_of_pairBeyond c (F := footprint)
          (by intro z hz; exact Finset.mem_union_left _ hz)
          t.upper_admissible.2.1,
        hbaseGrade, t.grade_eq]
    omega
  · rw [value_union_of_pairBeyond c (F := footprint)
          (by intro z hz; exact Finset.mem_union_left _ hz)
          t.upper_admissible.2.1,
        t.value_eq]
    linarith [t.lower_value_lt]

/-- Unconditional arbitrarily-light mobility in the reciprocal path model. -/
theorem arbitrarilyLightMobility : ArbitrarilyLightMobility :=
  arbitrarilyLightMobility_of_refinement_neutral
    unitFractionRefinementCofinality remoteLightNeutralGradeOne

end Erdos289
