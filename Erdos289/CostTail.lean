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

end Erdos289
