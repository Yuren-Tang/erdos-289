module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryConfigurations
public import Erdos289.PresentationComposition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Upper blockification of reciprocal presentations

A remote coefficient-one presentation is sent to connected binary blocks.  The
result has the same number of components and an explicitly positive reciprocal
excess.  Polynomial coordinates are confined to this realization module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Start of the binary block replacing the reciprocal atom `1/n`. -/
def upperBlockStart (n : Denominator) : Denominator :=
  ⟨2 * n.1 - 1, by have hn := n.2; omega⟩

/-- Denominator of the positive excess created by upper blockification. -/
def upperResidualDenominator (n : Denominator) : Denominator :=
  ⟨2 * n.1 * (2 * n.1 - 1), by
    have heven : 0 < 2 * n.1 := Nat.mul_pos (by decide) n.2
    have hodd : 0 < 2 * n.1 - 1 := by omega
    exact Nat.mul_pos heven hodd⟩

theorem upperBlockStart_injective : Function.Injective upperBlockStart := by
  intro a b h
  apply Subtype.ext
  have hv := congrArg Subtype.val h
  simp only [upperBlockStart] at hv
  omega

@[simp]
theorem upperBlockStart_value (n : Denominator) :
    (upperBlockStart n).1 = 2 * n.1 - 1 := rfl

@[simp]
theorem upperResidualDenominator_value (n : Denominator) :
    (upperResidualDenominator n).1 = 2 * n.1 * (2 * n.1 - 1) := rfl

theorem upperBlockMass_eq (n : Denominator) :
    binaryBlockMass (upperBlockStart n) =
      reciprocal n + reciprocal (upperResidualDenominator n) := by
  unfold binaryBlockMass reciprocal
  rw [upperBlockStart_value, upperResidualDenominator_value]
  have hs : 2 * n.1 - 1 + 1 = 2 * n.1 := by have hn := n.2; omega
  rw [← Nat.cast_one, ← Nat.cast_add, hs]
  exact upper_blockification_identity n

def upperBlockStarts (S : Support) : Finset Denominator :=
  S.image upperBlockStart

def upperResidual (S : Support) : ℚ :=
  ∑ n ∈ S, reciprocal (upperResidualDenominator n)

/-- Constraint requested before replacing atoms by binary blocks. -/
def upperBlockificationConstraint
    (c : PhysicalConstraint) (threshold : ℕ) : PhysicalConstraint where
  obstacle := denominatorPrefix (max (c.obstacleCutoff + 1) threshold)
  separation := max 1 c.separation + 2

theorem upperPresentation_remote
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (w : RationalPresentation q (upperBlockificationConstraint c threshold))
    {n : Denominator} (hn : n ∈ w.support) :
    c.obstacleCutoff + 1 < n.1 ∧ threshold < n.1 := by
  have hnot : n ∉ (upperBlockificationConstraint c threshold).obstacle := by
    intro hobs
    exact (Finset.disjoint_left.mp w.avoids hn) hobs
  simp only [upperBlockificationConstraint, mem_denominatorPrefix] at hnot
  omega

theorem upperPresentation_binaryPlacement
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (w : RationalPresentation q (upperBlockificationConstraint c threshold)) :
    BinaryPlacement c (upperBlockStarts w.support) := by
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    have hremote := (upperPresentation_remote w ha).1
    change c.obstacleCutoff < 2 * a.1 - 1
    omega
  · intro x hx y hy hxy
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
    have hab : a ≠ b := fun h => hxy (congrArg upperBlockStart h)
    have hdist := w.pointSeparated a ha b hb hab
    simp only [upperBlockificationConstraint] at hdist
    by_cases hablt : a.1 < b.1
    · apply binaryBlock_crossSeparated_of_lt
      simp only [upperBlockStart]
      rw [Nat.dist_eq_sub_of_le hablt.le] at hdist
      omega
    · have hbalt : b.1 < a.1 := by
        have : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        omega
      apply binaryBlock_crossSeparated_of_gt
      simp only [upperBlockStart]
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hbalt.le] at hdist
      omega

theorem upperBlockStarts_card (S : Support) :
    (upperBlockStarts S).card = S.card := by
  exact Finset.card_image_of_injective S upperBlockStart_injective

theorem upperConfiguration_value
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (w : RationalPresentation q (upperBlockificationConstraint c threshold)) :
    (binaryConfiguration (upperBlockStarts w.support)).value =
      q + upperResidual w.support := by
  rw [binaryConfiguration_value c _ (upperPresentation_binaryPlacement w)]
  unfold upperBlockStarts
  rw [Finset.sum_image]
  · simp_rw [upperBlockMass_eq]
    rw [Finset.sum_add_distrib]
    have hvalue : ∑ n ∈ w.support, reciprocal n = q := by
      simpa [Support.value] using w.value_eq
    rw [hvalue]
    rfl
  · intro a _ b _ hab
    exact upperBlockStart_injective hab

theorem upperResidual_pos_of_pos
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (hq : 0 < q)
    (w : RationalPresentation q (upperBlockificationConstraint c threshold)) :
    0 < upperResidual w.support := by
  have hne : w.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hv := w.value_eq
    rw [h] at hv
    simp [Support.value] at hv
    linarith
  unfold upperResidual
  exact Finset.sum_pos (fun n _ => by
    unfold reciprocal
    have hnq : (0 : ℚ) < (upperResidualDenominator n).1 := by
      exact_mod_cast (upperResidualDenominator n).2
    positivity) hne

theorem upperResidual_term_lt
    (threshold : ℕ) (ht : 0 < threshold) (n : Denominator)
    (hn : threshold < n.1) :
    reciprocal (upperResidualDenominator n) <
      reciprocal n / (threshold : ℚ) := by
  have hnat : threshold * n.1 < (upperResidualDenominator n).1 := by
    simp only [upperResidualDenominator_value]
    have hfac : threshold < 2 * (2 * n.1 - 1) := by
      have hnpos := n.2
      omega
    have hmul := (Nat.mul_lt_mul_right n.2).mpr hfac
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hprod : (0 : ℚ) < (threshold : ℚ) * (n.1 : ℚ) := by
    exact mul_pos (by exact_mod_cast ht) (by exact_mod_cast n.2)
  have hcast : (threshold : ℚ) * (n.1 : ℚ) <
      ((upperResidualDenominator n).1 : ℚ) := by
    exact_mod_cast hnat
  unfold reciprocal
  calc
    1 / ((upperResidualDenominator n).1 : ℚ) <
        1 / ((threshold : ℚ) * (n.1 : ℚ)) :=
      one_div_lt_one_div_of_lt hprod hcast
    _ = (1 / (n.1 : ℚ)) / (threshold : ℚ) := by
      field_simp

theorem upperResidual_lt_div
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (hq : 0 < q) (ht : 0 < threshold)
    (w : RationalPresentation q (upperBlockificationConstraint c threshold)) :
    upperResidual w.support < q / (threshold : ℚ) := by
  have hne : w.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hv := w.value_eq
    rw [h] at hv
    simp [Support.value] at hv
    linarith
  unfold upperResidual
  calc
    ∑ n ∈ w.support, reciprocal (upperResidualDenominator n) <
        ∑ n ∈ w.support, reciprocal n / (threshold : ℚ) :=
      Finset.sum_lt_sum_of_nonempty hne fun n hn =>
        upperResidual_term_lt threshold ht n (upperPresentation_remote w hn).2
    _ = q / (threshold : ℚ) := by
      rw [← Finset.sum_div]
      congr 1
      simpa [Support.value] using w.value_eq

/-- Exact blockification data before imposing a quantitative excess bound. -/
theorem upperBlockification_data
    {q : ℚ} {c : PhysicalConstraint} {threshold : ℕ}
    (hq : 0 < q)
    (w : RationalPresentation q (upperBlockificationConstraint c threshold)) :
    ∃ B : Support, ∃ ρ : ℚ, ∃ k : ℕ,
      B.Admissible smallBlockSizes c ∧ B.value = q + ρ ∧
      B.grade = k ∧ 0 < ρ := by
  exact ⟨binaryConfiguration (upperBlockStarts w.support),
    upperResidual w.support, w.support.card,
    binaryConfiguration_admissible c _ (upperPresentation_binaryPlacement w),
    upperConfiguration_value w,
    (binaryConfiguration_grade c _ (upperPresentation_binaryPlacement w)).trans
      (upperBlockStarts_card w.support),
    upperResidual_pos_of_pos hq w⟩

/-- Leaf E supplies arbitrarily accurate positive-excess blockifications. -/
theorem positiveExcessBlockification_of_unitFractionRefinement
    (hE : UnitFractionRefinementCofinality)
    (q : ℚ) (hq : 0 < q) (c : PhysicalConstraint) (ε : ℚ) (hε : 0 < ε) :
    Nonempty (PositiveExcessBlockification q c ε) := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_gt (q / ε)
  have ht : 0 < threshold := by
    have hquot : 0 < q / ε := by positivity
    exact_mod_cast (hquot.trans hthreshold)
  have hqdiv : q / (threshold : ℚ) < ε := by
    rw [div_lt_iff₀ (by exact_mod_cast ht)]
    have hmul := (div_lt_iff₀ hε).mp hthreshold
    nlinarith
  obtain ⟨w⟩ := rationalPresentation_of_pos hE q hq
    (upperBlockificationConstraint c threshold)
  exact ⟨{
    support := binaryConfiguration (upperBlockStarts w.support)
    excess := upperResidual w.support
    atoms := w.support.card
    admissible := binaryConfiguration_admissible c _
      (upperPresentation_binaryPlacement w)
    value_eq := upperConfiguration_value w
    grade_eq := (binaryConfiguration_grade c _
      (upperPresentation_binaryPlacement w)).trans (upperBlockStarts_card w.support)
    excess_pos := upperResidual_pos_of_pos hq w
    excess_lt := (upperResidual_lt_div hq ht w).trans hqdiv }⟩

end Erdos289
