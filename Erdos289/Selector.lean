module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimePowerFiltration
public import Erdos289.Statement

@[expose] public section

/-!
# The unit selector

Centering by the target replaces the exact value group `ℚ` by `ℚ/ℤ`.  A state
whose centered residue vanishes has integer value, so on the open interval
`(0, 2)` — the two adjacent lifts of the target residue surrounding the target —
the centered condition already pins the value to `1`.

This is the reciprocal specialization of the selector used by the universal
exact-fibre transfer theorem: `(0, 2) ∩ ℤ = {1}`.  Nothing here chooses a
witness; it converts a residue condition into an exact value.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- `(0, 2) ∩ ℤ · 1 = {1}` inside `ℚ`. -/
theorem eq_one_of_mem_zmultiples_of_lt_two {q : ℚ}
    (hmem : q ∈ AddSubgroup.zmultiples (1 : ℚ)) (h0 : 0 < q) (h2 : q < 2) :
    q = 1 := by
  rw [AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨n, hn⟩ := hmem
  have hq : q = (n : ℚ) := by
    rw [← hn, zsmul_eq_mul, mul_one]
  subst hq
  have h0' : (0 : ℤ) < n := by exact_mod_cast h0
  have h2' : n < (2 : ℤ) := by exact_mod_cast h2
  have : n = 1 := by omega
  rw [this]
  norm_num

/--
The selector step: a support whose value lies strictly between `0` and `2` and
whose centered residue vanishes has value exactly `1`.
-/
theorem Support.value_eq_one_of_residue_zero {S : Support}
    (h0 : 0 < S.value) (h2 : S.value < 2) (hres : S.residue = 0) :
    S.value = 1 := by
  refine eq_one_of_mem_zmultiples_of_lt_two ?_ h0 h2
  exact (QuotientAddGroup.eq_zero_iff S.value).1 hres

/--
An admissible support of grade `k` that is centered and lies in the selector
interval is a saturation witness at the unit target.
-/
def saturationWitness_of_residue_zero
    {L : Set ℕ} {c : PhysicalConstraint} {k : ℕ} {S : Support}
    (hadm : S.Admissible L c) (hgrade : S.grade = k)
    (h0 : 0 < S.value) (h2 : S.value < 2) (hres : S.residue = 0) :
    SaturationWitness L 1 c k where
  support := S
  admissible := hadm
  value_eq := Support.value_eq_one_of_residue_zero h0 h2 hres
  grade_eq := hgrade

/--
Cofinite saturation at the unit target follows from a family of centered
admissible supports realizing every sufficiently large grade inside the
selector interval.
-/
theorem cofiniteSaturation_one_of_centered
    {L : Set ℕ} {c : PhysicalConstraint} {N : ℕ}
    (h : ∀ k, N ≤ k → ∃ S : Support, S.Admissible L c ∧
      S.grade = k ∧ 0 < S.value ∧ S.value < 2 ∧ S.residue = 0) :
    CofiniteSaturation L 1 c := by
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨S, hadm, hgrade, h0, h2, hres⟩ := h k hk
  exact ⟨saturationWitness_of_residue_zero hadm hgrade h0 h2 hres⟩

end Erdos289
