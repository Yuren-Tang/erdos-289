module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Minkowski aggregation of local grade intervals

Composing local correction stages adds their grades, so the set of realizable
total grades is the Minkowski sum of the local epi-grade spectra.  When each
local spectrum contains an integer interval, so does the sum, and the endpoints
are the sums of the endpoints.

The statement proved here is the constructive form actually consumed: every
integer in the aggregate interval is a *sum of admissible local grades*, so a
global correction of that exact grade can be assembled stage by stage.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Erdos289

namespace GradeAggregation

/-- Minkowski sum of two integer intervals is the interval of the sums. -/
theorem exists_pair_of_mem_Icc_add {a b c d m : ℕ} (hab : a ≤ b) (hcd : c ≤ d)
    (hlow : a + c ≤ m) (hupp : m ≤ b + d) :
    ∃ x y, a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ∧ x + y = m := by
  refine ⟨max a (m - d), m - max a (m - d), ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/--
Every integer between the sum of the lower endpoints and the sum of the upper
endpoints is a sum of admissible local grades.
-/
theorem exists_grades_of_mem_sum_Icc
    (a b : ℕ → ℕ) (hab : ∀ i, a i ≤ b i) :
    ∀ (n m : ℕ), ∑ i ∈ Finset.range n, a i ≤ m → m ≤ ∑ i ∈ Finset.range n, b i →
      ∃ h : ℕ → ℕ, (∀ i, i < n → a i ≤ h i ∧ h i ≤ b i) ∧
        ∑ i ∈ Finset.range n, h i = m := by
  intro n
  induction n with
  | zero =>
      intro m hlow hupp
      simp only [Finset.range_zero, Finset.sum_empty] at hlow hupp
      refine ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero i), ?_⟩
      simp only [Finset.range_zero, Finset.sum_empty]
      omega
  | succ n ih =>
      intro m hlow hupp
      rw [Finset.sum_range_succ] at hlow hupp
      obtain ⟨x, y, hxa, hxb, hyc, hyd, hxy⟩ :=
        exists_pair_of_mem_Icc_add
          (a := ∑ i ∈ Finset.range n, a i) (b := ∑ i ∈ Finset.range n, b i)
          (c := a n) (d := b n) (m := m)
          (Finset.sum_le_sum fun i _ => hab i) (hab n) hlow hupp
      obtain ⟨h, hmem, hsum⟩ := ih x hxa hxb
      refine ⟨Function.update h n y, ?_, ?_⟩
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
        · rw [Function.update_of_ne (Nat.ne_of_lt hlt)]
          exact hmem i hlt
        · rw [Function.update_self]
          exact ⟨hyc, hyd⟩
      · rw [Finset.sum_range_succ, Function.update_self]
        have hcongr : ∑ i ∈ Finset.range n, Function.update h n y i =
            ∑ i ∈ Finset.range n, h i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          exact Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.1 hi)) _ _
        rw [hcongr, hsum]
        omega

/--
Donor flow: if the cumulative one-use supply strictly before every stage
dominates the cumulative demand up to and including that stage, then the
demands can be served in stage order without ever reusing a donor.

The statement is the running-balance form, which is what an inductive
construction consumes.
-/
theorem donor_flow_nonneg (s d : ℕ → ℕ)
    (h : ∀ j, ∑ i ∈ Finset.range (j + 1), d i ≤ ∑ i ∈ Finset.range j, s i) :
    ∀ j, ∑ i ∈ Finset.range j, d i + d j ≤ ∑ i ∈ Finset.range j, s i := by
  intro j
  have := h j
  rwa [Finset.sum_range_succ] at this

end GradeAggregation

end Erdos289
