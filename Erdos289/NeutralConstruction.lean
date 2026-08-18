module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.BinaryConfigurations
public import Erdos289.ProviderInterfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section

/-!
# Concrete neutral grade-one configurations

The intrinsic target is `NeutralGradeOnePoint`.  Polynomial coordinates occur
only in this construction module, where the exact binary-to-ternary reciprocal
identity is realized by admissible binary path configurations.
-/

set_option autoImplicit false

namespace Erdos289

def neutralQuadratic (a : Denominator) : Denominator :=
  ⟨a.1 ^ 2 + 3 * a.1 + 1, by omega⟩

def neutralShift (a : Denominator) : Denominator := ⟨a.1 + 2, by omega⟩

def neutralMiddleDenominator (a : Denominator) : Denominator :=
  ⟨neutralMiddle a, by
    simp only [neutralMiddle]
    apply Nat.div_pos
    · exact le_trans (by decide : 2 ≤ 1 * (1 + 3))
        (Nat.mul_le_mul a.2 (Nat.add_le_add_right a.2 3))
    · exact Nat.zero_lt_succ 1⟩

def neutralProduct (a : Denominator) : Denominator :=
  ⟨a.1 * (a.1 + 3), Nat.mul_pos a.2 (Nat.add_pos_right a.1 (by norm_num))⟩

def neutralLowerStarts (a : Denominator) : Finset Denominator :=
  {a, neutralQuadratic a}

def neutralUpperStarts (a : Denominator) : Finset Denominator :=
  {neutralShift a, neutralMiddleDenominator a, neutralProduct a}

theorem two_dvd_neutralProduct (a : Denominator) :
    2 ∣ a.1 * (a.1 + 3) := by
  rcases Nat.even_or_odd a.1 with ha | ha
  · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp ha) _
  · exact dvd_mul_of_dvd_right
      (even_iff_two_dvd.mp (ha.add_odd (⟨1, by norm_num⟩ : Odd (3 : ℕ)))) _

/--
Proof technology: one coarse lower bound that simultaneously dominates the
finitely many gap inequalities of the neutral identity.  The bound itself is a
witness and is not part of any interface; the statement consumed elsewhere is
`eventually_neutralBinaryPlacements`.
-/
private theorem neutralBinaryPlacements_of_large
    (c : PhysicalConstraint) (a : Denominator)
    (ha : 2 * (c.obstacleCutoff + max 1 c.separation + 10) < a.1) :
    BinaryPlacement c (neutralLowerStarts a) ∧
      BinaryPlacement c (neutralUpperStarts a) := by
  let m := max 1 c.separation
  have ham : m < a.1 := by
    dsimp [m]
    omega
  have ham2 : 2 * m + 20 < a.1 := by
    dsimp [m]
    omega
  have hac : c.obstacleCutoff < a.1 := by omega
  have ha2 : 2 ≤ a.1 := by omega
  have hcancel : 2 * (a.1 * (a.1 + 3) / 2) = a.1 * (a.1 + 3) :=
    Nat.mul_div_cancel' (two_dvd_neutralProduct a)
  have hLowerGap : a.1 + 1 + m < (neutralQuadratic a).1 := by
    simp only [neutralQuadratic]
    nlinarith
  have hShiftMiddleGap :
      (neutralShift a).1 + 1 + m < (neutralMiddleDenominator a).1 := by
    simp only [neutralShift, neutralMiddleDenominator, neutralMiddle]
    nlinarith [hcancel]
  have hMiddleProductGap :
      (neutralMiddleDenominator a).1 + 1 + m < (neutralProduct a).1 := by
    simp only [neutralMiddleDenominator, neutralMiddle, neutralProduct]
    nlinarith [hcancel]
  have hShiftProductGap :
      (neutralShift a).1 + 1 + m < (neutralProduct a).1 := by
    omega
  constructor
  · constructor
    · intro x hx
      simp only [neutralLowerStarts, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hac
      · simp only [neutralQuadratic]
        nlinarith
    · intro x hx y hy hxy
      simp only [neutralLowerStarts, Finset.mem_insert,
        Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact (hxy rfl).elim
      · exact binaryBlock_crossSeparated_of_lt hLowerGap
      · exact binaryBlock_crossSeparated_of_gt hLowerGap
      · exact (hxy rfl).elim
  · constructor
    · intro x hx
      simp only [neutralUpperStarts, Finset.mem_insert,
        Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · simp only [neutralShift]
        omega
      · simp only [neutralMiddleDenominator, neutralMiddle]
        nlinarith
      · simp only [neutralProduct]
        nlinarith
    · intro x hx y hy hxy
      simp only [neutralUpperStarts, Finset.mem_insert,
        Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact (hxy rfl).elim
      · exact binaryBlock_crossSeparated_of_lt hShiftMiddleGap
      · exact binaryBlock_crossSeparated_of_lt hShiftProductGap
      · exact binaryBlock_crossSeparated_of_gt hShiftMiddleGap
      · exact (hxy rfl).elim
      · exact binaryBlock_crossSeparated_of_lt hMiddleProductGap
      · exact binaryBlock_crossSeparated_of_gt hShiftProductGap
      · exact binaryBlock_crossSeparated_of_gt hMiddleProductGap
      · exact (hxy rfl).elim

/--
Eventual admissibility of the neutral family.  For every physical constraint,
all sufficiently remote members of the polynomial neutral family are placed
admissibly on both sides of the identity.

This is the intrinsic statement: no particular threshold occurs in it, and any
witness dominating the finitely many gap inequalities proves it.
-/
theorem eventually_neutralBinaryPlacements (c : PhysicalConstraint) :
    ∃ N : ℕ, ∀ a : Denominator, N < a.1 →
      BinaryPlacement c (neutralLowerStarts a) ∧
        BinaryPlacement c (neutralUpperStarts a) :=
  ⟨2 * (c.obstacleCutoff + max 1 c.separation + 10),
    fun a ha => neutralBinaryPlacements_of_large c a ha⟩

theorem neutralLowerStarts_card (a : Denominator) :
    (neutralLowerStarts a).card = 2 := by
  have hne : a ≠ neutralQuadratic a := by
    intro h
    have hv := congrArg Subtype.val h
    simp [neutralQuadratic] at hv
    nlinarith [a.2]
  simp [neutralLowerStarts, hne]

theorem neutralUpperStarts_card (a : Denominator) (ha : 2 ≤ a.1) :
    (neutralUpperStarts a).card = 3 := by
  have hsm : neutralShift a ≠ neutralMiddleDenominator a := by
    intro h
    have hv := congrArg Subtype.val h
    simp [neutralShift, neutralMiddleDenominator, neutralMiddle] at hv
    have hcancel : 2 * (a.1 * (a.1 + 3) / 2) = a.1 * (a.1 + 3) :=
      Nat.mul_div_cancel' (two_dvd_neutralProduct a)
    rw [← hv] at hcancel
    nlinarith
  have hsp : neutralShift a ≠ neutralProduct a := by
    intro h
    have hv := congrArg Subtype.val h
    simp [neutralShift, neutralProduct] at hv
    nlinarith
  have hmp : neutralMiddleDenominator a ≠ neutralProduct a := by
    intro h
    have hv := congrArg Subtype.val h
    simp [neutralMiddleDenominator, neutralMiddle, neutralProduct] at hv
    have hpos : 0 < a.1 * (a.1 + 3) := by positivity
    have hlt : a.1 * (a.1 + 3) / 2 < a.1 * (a.1 + 3) :=
      Nat.div_lt_self hpos (by omega)
    exact (ne_of_lt hlt) hv
  simp [neutralUpperStarts, hsm, hsp, hmp]

theorem neutralGradeOnePoint_of_placements
    (c : PhysicalConstraint) (ε : ℚ) (a : Denominator)
    (ha : 2 ≤ a.1)
    (hlow : BinaryPlacement c (neutralLowerStarts a))
    (hupp : BinaryPlacement c (neutralUpperStarts a))
    (hlight : (binaryConfiguration (neutralLowerStarts a)).value < ε) :
    Nonempty (NeutralGradeOnePoint c ε) := by
  refine ⟨{
    lower := binaryConfiguration (neutralLowerStarts a)
    upper := binaryConfiguration (neutralUpperStarts a)
    lower_admissible := binaryConfiguration_admissible c _ hlow
    upper_admissible := binaryConfiguration_admissible c _ hupp
    value_eq := ?_
    grade_eq := ?_
    value_pos := ?_
    value_lt := hlight }⟩
  · rw [binaryConfiguration_value c _ hupp,
      binaryConfiguration_value c _ hlow]
    have hL : ∑ x ∈ neutralLowerStarts a, binaryBlockMass x =
        binaryBlockMass a + binaryBlockMass (neutralQuadratic a) := by
      have hne : a ≠ neutralQuadratic a := by
        intro h
        have hv := congrArg Subtype.val h
        simp [neutralQuadratic] at hv
        nlinarith [a.2]
      simp [neutralLowerStarts, hne]
    have hU : ∑ x ∈ neutralUpperStarts a, binaryBlockMass x =
        binaryBlockMass (neutralShift a) +
          binaryBlockMass (neutralMiddleDenominator a) +
            binaryBlockMass (neutralProduct a) := by
      have hsm : neutralShift a ≠ neutralMiddleDenominator a := by
        intro h
        have hv := congrArg Subtype.val h
        simp [neutralShift, neutralMiddleDenominator, neutralMiddle] at hv
        have hcancel : 2 * (a.1 * (a.1 + 3) / 2) = a.1 * (a.1 + 3) :=
          Nat.mul_div_cancel' (two_dvd_neutralProduct a)
        rw [← hv] at hcancel
        nlinarith
      have hsp : neutralShift a ≠ neutralProduct a := by
        intro h
        have hv := congrArg Subtype.val h
        simp [neutralShift, neutralProduct] at hv
        nlinarith
      have hmp : neutralMiddleDenominator a ≠ neutralProduct a := by
        intro h
        have hv := congrArg Subtype.val h
        simp [neutralMiddleDenominator, neutralMiddle, neutralProduct] at hv
        have hpos : 0 < a.1 * (a.1 + 3) := by positivity
        have hlt : a.1 * (a.1 + 3) / 2 < a.1 * (a.1 + 3) :=
          Nat.div_lt_self hpos (by omega)
        exact (ne_of_lt hlt) hv
      simp [neutralUpperStarts, hsm, hsp, hmp, add_assoc]
    rw [hL, hU]
    simpa [neutralQuadratic, neutralShift, neutralMiddleDenominator,
      neutralProduct] using (neutral_grade_one_identity a).symm
  · rw [binaryConfiguration_grade c _ hupp,
      binaryConfiguration_grade c _ hlow,
      neutralUpperStarts_card a ha, neutralLowerStarts_card]
  · rw [binaryConfiguration_value c _ hlow]
    have hne : a ≠ neutralQuadratic a := by
      intro h
      have hv := congrArg Subtype.val h
      simp [neutralQuadratic] at hv
      nlinarith [a.2]
    simp only [neutralLowerStarts, Finset.sum_insert, Finset.mem_singleton,
      hne, not_false_eq_true, Finset.sum_singleton]
    exact add_pos (binaryBlockMass_pos a)
      (binaryBlockMass_pos (neutralQuadratic a))

theorem neutralQuadratic_mass_lt_two_div (a : Denominator) :
    binaryBlockMass (neutralQuadratic a) < 2 / (a.1 : ℚ) := by
  have ha : (0 : ℚ) < a.1 := by exact_mod_cast a.2
  have hq : (0 : ℚ) < (neutralQuadratic a).1 := by
    exact_mod_cast (neutralQuadratic a).2
  have hq1 : (0 : ℚ) < (neutralQuadratic a).1 + 1 := by positivity
  have ha0 : (a.1 : ℚ) ≠ 0 := ne_of_gt ha
  have hq0 : ((neutralQuadratic a).1 : ℚ) ≠ 0 := ne_of_gt hq
  have hq10 : ((neutralQuadratic a).1 : ℚ) + 1 ≠ 0 := ne_of_gt hq1
  have haq : (a.1 : ℚ) < (neutralQuadratic a).1 := by
    simp only [neutralQuadratic]
    exact_mod_cast (show a.1 < a.1 ^ 2 + 3 * a.1 + 1 by nlinarith [a.2])
  unfold binaryBlockMass
  field_simp [ha0, hq0, hq10]
  nlinarith

/-- The concrete lower side tends to zero, with a uniform elementary bound. -/
theorem neutralLower_value_lt_four_div
    (c : PhysicalConstraint) (a : Denominator)
    (hplace : BinaryPlacement c (neutralLowerStarts a)) :
    (binaryConfiguration (neutralLowerStarts a)).value < 4 / (a.1 : ℚ) := by
  rw [binaryConfiguration_value c _ hplace]
  have hne : a ≠ neutralQuadratic a := by
    intro h
    have hv := congrArg Subtype.val h
    simp [neutralQuadratic] at hv
    nlinarith [a.2]
  simp only [neutralLowerStarts, Finset.sum_insert, Finset.mem_singleton,
    hne, not_false_eq_true, Finset.sum_singleton]
  calc
    binaryBlockMass a + binaryBlockMass (neutralQuadratic a) <
        2 / (a.1 : ℚ) + 2 / (a.1 : ℚ) :=
      add_lt_add (binaryBlockMass_lt_two_div a)
        (neutralQuadratic_mass_lt_two_div a)
    _ = 4 / (a.1 : ℚ) := by
      rw [← add_div]
      norm_num

/-- Hard leaf N: the intrinsic neutral fibre has arbitrarily light remote points. -/
theorem remoteLightNeutralGradeOne : RemoteLightNeutralGradeOne := by
  intro c ε hε
  obtain ⟨N, hN⟩ := eventually_neutralBinaryPlacements c
  obtain ⟨n, hn⟩ := exists_nat_gt (max (max (N : ℚ) 1) (4 / ε))
  have hBnQ : (N : ℚ) < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hBn : N < n := by exact_mod_cast hBnQ
  have h1Q : (1 : ℚ) < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h1 : 1 < n := by exact_mod_cast h1Q
  have hnpos : 0 < n := by omega
  let a : Denominator := ⟨n, hnpos⟩
  obtain ⟨hlow, hupp⟩ := hN a hBn
  have ha2 : 2 ≤ a.1 := by change 2 ≤ n; omega
  apply neutralGradeOnePoint_of_placements c ε a ha2 hlow hupp
  have hfour : 4 / ε < (n : ℚ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnQ : (0 : ℚ) < n := by exact_mod_cast hnpos
  have hsmall : 4 / (n : ℚ) < ε := by
    apply (div_lt_iff₀ hnQ).2
    exact (div_lt_iff₀' hε).1 hfour
  exact lt_trans (neutralLower_value_lt_four_div c a hlow) hsmall

end Erdos289
