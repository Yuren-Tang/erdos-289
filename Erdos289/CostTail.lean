module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Summable local costs give a vanishing tail

The manuscript's uniform vanishing-cost aggregation: if the per-stage cost
bounds are summable, then the whole cost of every finite run of stages beyond a
late enough base is below any prescribed margin.  This is what lets the tail
load be pushed under the core's fixed barrier slack by moving the base stage
outward, and it is the only thing summability is used for.

The statement is asymptotic, and stays asymptotic: no stage index is named.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace Erdos289

/-- Real form: a summable nonnegative cost has arbitrarily cheap tails. -/
theorem exists_tail_sum_lt {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) (hsum : Summable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M : ℕ, ∑ i ∈ Finset.range M, f (i + N) < ε := by
  have htend : Tendsto (fun i => ∑' k, f (k + i)) atTop (nhds 0) :=
    tendsto_sum_nat_add f
  obtain ⟨N, hN⟩ := (Filter.Tendsto.eventually_lt_const hε htend).exists
  refine ⟨N, fun M => ?_⟩
  have hsum' : Summable fun k => f (k + N) := (summable_nat_add_iff N).2 hsum
  calc ∑ i ∈ Finset.range M, f (i + N)
      ≤ ∑' k, f (k + N) := hsum'.sum_le_tsum _ (fun i _ => hf _)
    _ < ε := hN

/-- Rational form, which is what reciprocal masses need. -/
theorem exists_tail_sum_lt_rat {f : ℕ → ℚ} (hf : ∀ i, 0 ≤ f i)
    (hsum : Summable fun i => (f i : ℝ)) {ε : ℚ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ M : ℕ, ∑ i ∈ Finset.range M, f (i + N) < ε := by
  obtain ⟨N, hN⟩ := exists_tail_sum_lt (f := fun i => (f i : ℝ))
    (fun i => by exact_mod_cast hf i) hsum (ε := (ε : ℝ)) (by exact_mod_cast hε)
  refine ⟨N, fun M => ?_⟩
  have := hN M
  exact_mod_cast this

/-! ### Costs that are chosen rather than given -/

/--
A run of stages whose costs are dominated by a geometric sequence stays below
the margin, whatever the length of the run.

This is the form the tail chain uses when the per-stage cost is *chosen* rather
than given: each stage's truncation rank is a free parameter, so its cost can
be prescribed in advance, and the only thing left to check is that the
prescription sums.
-/
private theorem sum_geometric_halves (s : ℚ) :
    ∀ m : ℕ, ∑ i ∈ Finset.range m, s / 2 ^ (i + 2) = s / 2 - s / 2 ^ (m + 1) := by
  intro m
  induction m with
  | zero => norm_num
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (2 : ℚ) ^ (k + 1) ≠ 0 := by positivity
      have h2 : (2 : ℚ) ^ (k + 2) ≠ 0 := by positivity
      field_simp
      ring

theorem sum_lt_of_le_geometric {s : ℚ} (hs : 0 < s) {cost : ℕ → ℚ}
    (hle : ∀ i, cost i ≤ s / 2 ^ (i + 2)) (n : ℕ) :
    ∑ i ∈ Finset.range n, cost i < s := by
  have hpow : (0 : ℚ) < 2 ^ (n + 1) := by positivity
  calc ∑ i ∈ Finset.range n, cost i
      ≤ ∑ i ∈ Finset.range n, s / 2 ^ (i + 2) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = s / 2 - s / 2 ^ (n + 1) := sum_geometric_halves s n
    _ < s := by
        have : (0 : ℚ) < s / 2 ^ (n + 1) := by positivity
        linarith

/--
The cost of one stage is a free parameter: the truncation rank can be raised
until the stage's load is below any prescribed margin.

The rank enters the mass bound only through `2 / (Q t - 1)`, so this is the
statement that raising it costs nothing but band size.
-/
theorem exists_rank_of_cost_le {Q h : ℕ} (hQ : 0 < Q) {ε : ℚ} (hε : 0 < ε) :
    ∃ t : ℕ, 1 < Q * t ∧ (h : ℚ) * (2 / ((Q * t - 1 : ℕ) : ℚ)) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (h : ℚ) / ε + 1)
  refine ⟨N + 2, ?_, ?_⟩
  · calc 1 < 1 * (N + 2) := by omega
      _ ≤ Q * (N + 2) := Nat.mul_le_mul_right _ hQ
  · have hbig : (N : ℚ) ≤ ((Q * (N + 2) - 1 : ℕ) : ℚ) := by
      have hnat : N ≤ Q * (N + 2) - 1 := by
        have : N + 1 ≤ 1 * (N + 2) := by omega
        have : N + 1 ≤ Q * (N + 2) := le_trans this (Nat.mul_le_mul_right _ hQ)
        omega
      exact_mod_cast hnat
    have hNpos : (0 : ℚ) < N := lt_of_le_of_lt (by positivity) hN
    have hden : (0 : ℚ) < ((Q * (N + 2) - 1 : ℕ) : ℚ) := lt_of_lt_of_le hNpos hbig
    have hkey : 2 * (h : ℚ) / ε < ((Q * (N + 2) - 1 : ℕ) : ℚ) := by
      have : 2 * (h : ℚ) / ε < N := by linarith
      linarith
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ hden]
    have hh : (0 : ℚ) ≤ h := Nat.cast_nonneg h
    have := (div_lt_iff₀ hε).1 hkey
    nlinarith [hden, hε]

end Erdos289
