module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PathSupport
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact reciprocal identities

These coordinate identities are kept at the arithmetic boundary.  Downstream
modules use the fibre points they construct, not the formulas themselves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- The reciprocal mass of the binary path block `{a,a+1}`. -/
def binaryBlockMass (a : ℕ+) : ℚ :=
  1 / (a.1 : ℚ) + 1 / (a.1 + 1 : ℚ)

/-- The exact upper-blockification identity. -/
theorem upper_blockification_identity (n : ℕ+) :
    1 / ((2 * n.1 - 1 : ℕ) : ℚ) + 1 / ((2 * n.1 : ℕ) : ℚ) =
      1 / (n.1 : ℚ) + 1 / ((2 * n.1 * (2 * n.1 - 1) : ℕ) : ℚ) := by
  have hnpos : 0 < n.1 := n.2
  have hle : 1 ≤ 2 * n.1 := by omega
  push_cast [Nat.cast_sub hle]
  have hnqpos : 0 < (n.1 : ℚ) := by exact_mod_cast hnpos
  have hnq : (n.1 : ℚ) ≠ 0 := ne_of_gt hnqpos
  have hoddq : (2 * (n.1 : ℚ) - 1) ≠ 0 := by
    have hoddltNat : 1 < 2 * n.1 := by omega
    have hoddltQ : (1 : ℚ) < 2 * (n.1 : ℚ) := by exact_mod_cast hoddltNat
    exact ne_of_gt (sub_pos.mpr hoddltQ)
  field_simp [hnq, hoddq]
  ring

/-- Auxiliary two-endpoint arithmetic identity; the admissible physical switch is
`endpoint_inclusion_switch` between a binary and a ternary interval. -/
theorem endpoint_switch_identity (a : ℕ+) :
    (1 / ((a.1 + 1 : ℕ) : ℚ) + 1 / ((a.1 + 2 : ℕ) : ℚ)) -
        (1 / (a.1 : ℚ) + 1 / ((a.1 + 2 : ℕ) : ℚ)) =
      -(1 / (a.1 : ℚ) - 1 / ((a.1 + 1 : ℕ) : ℚ)) := by
  ring

/-- Polynomial index appearing in the neutral grade-one identity. -/
def neutralMiddle (a : ℕ+) : ℕ := a.1 * (a.1 + 3) / 2

private def binaryBlockMassQ (x : ℚ) : ℚ :=
  1 / x + 1 / (x + 1)

private theorem neutral_grade_one_identity_rat (x : ℚ) (hx : 0 < x) :
    binaryBlockMassQ x + binaryBlockMassQ (x ^ 2 + 3 * x + 1) =
      binaryBlockMassQ (x + 2) + binaryBlockMassQ (x * (x + 3) / 2) +
        binaryBlockMassQ (x * (x + 3)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by positivity
  have hx2 : x + 2 ≠ 0 := by positivity
  have hx3 : x + 3 ≠ 0 := by positivity
  have hp0 : x ^ 2 + 3 * x + 1 ≠ 0 := by positivity
  have hp1 : x ^ 2 + 3 * x + 1 + 1 ≠ 0 := by positivity
  have hm0 : x * (x + 3) / 2 ≠ 0 := by positivity
  have hm1 : x * (x + 3) / 2 + 1 ≠ 0 := by positivity
  have hq0 : x * (x + 3) ≠ 0 := by positivity
  have hq1 : x * (x + 3) + 1 ≠ 0 := by positivity
  have hp1' : 2 + x * 3 + x ^ 2 ≠ 0 := by positivity
  have hx3' : 3 + x ≠ 0 := by positivity
  unfold binaryBlockMassQ
  field_simp [hx0, hx1, hx2, hx3, hp0, hp1, hm0, hm1, hq0, hq1, hp1', hx3']
  ring

/-- The exact binary-to-ternary neutral identity. -/
theorem neutral_grade_one_identity (a : ℕ+) :
    binaryBlockMass a + binaryBlockMass ⟨a.1 ^ 2 + 3 * a.1 + 1, by omega⟩ =
      binaryBlockMass ⟨a.1 + 2, by omega⟩ +
        binaryBlockMass ⟨neutralMiddle a, by
          simp only [neutralMiddle]
          apply Nat.div_pos
          · exact le_trans (by decide : 2 ≤ 1 * (1 + 3))
              (Nat.mul_le_mul a.2 (Nat.add_le_add_right a.2 3))
          · exact Nat.zero_lt_succ 1⟩ +
        binaryBlockMass ⟨a.1 * (a.1 + 3),
          Nat.mul_pos a.2 (Nat.add_pos_right a.1 (by norm_num))⟩ := by
  have heven : 2 ∣ a.1 * (a.1 + 3) := by
    rcases Nat.even_or_odd a.1 with ha | ha
    · exact dvd_mul_of_dvd_left (even_iff_two_dvd.mp ha) _
    · exact dvd_mul_of_dvd_right
        (even_iff_two_dvd.mp (ha.add_odd (⟨1, by norm_num⟩ : Odd (3 : ℕ)))) _
  have hmiddle_cast : ((neutralMiddle a : ℕ) : ℚ) =
      (a.1 : ℚ) * (a.1 + 3) / 2 := by
    rw [neutralMiddle, Nat.cast_div heven (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  simpa [binaryBlockMass, binaryBlockMassQ, hmiddle_cast, Nat.cast_add,
    Nat.cast_mul, Nat.cast_pow] using
      neutral_grade_one_identity_rat (a.1 : ℚ) (by exact_mod_cast a.2)

end Erdos289
