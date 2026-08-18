module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimeSupply
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Leaf `Π` in the form the descent consumes

`Erdos289.comparablePrimeSupply_explicit` is the raw Chebyshev consequence: an
inequality still carrying the `√x log x` error term of the lower bound for the
theta function.  What the descent actually uses is the asymptotic statement

`#{p prime : n < p ≤ 4n}  ≫  n / log n`,

and that is what this module exports.  The statement is asymptotic because the
mathematics is asymptotic; it is *not* replaced by an inequality valid beyond a
hand-chosen numerical threshold.  The error term is absorbed by
`Asymptotics.IsLittleO`, so no constant of the construction is ever named.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics Real

namespace Erdos289

/-! ### One elementary rate -/

private theorem log_isLittleO_sqrt : Real.log =o[atTop] Real.sqrt := by
  refine (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).congr'
    EventuallyEq.rfl ?_
  filter_upwards with x
  rw [Real.sqrt_eq_rpow]

/-! ### The comparable band carries linearly many log-weights -/

/--
The error term of the Chebyshev lower bound for the theta increment over the
band `(x, 4x]` is `o(x)`.
-/
private theorem chebyshev_error_isLittleO :
    (fun x : ℝ => Real.log (4 * x + 1) + 2 * √(4 * x) * Real.log (4 * x)) =o[atTop]
      fun x : ℝ => x := by
  have h4 : Tendsto (fun x : ℝ => 4 * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
  have h4' : Tendsto (fun x : ℝ => 4 * x + 1) atTop atTop := h4.atTop_add tendsto_const_nhds
  -- `log (4x + 1) = o(x)`
  have hlog : (fun x : ℝ => Real.log (4 * x + 1)) =o[atTop] fun x : ℝ => x := by
    refine (Real.isLittleO_log_id_atTop.comp_tendsto h4').trans_isBigO ?_
    refine IsBigO.of_bound 5 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Function.comp_apply, id_eq]
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
    linarith
  -- `√(4x) log (4x) = o(x)`
  have hsqrtlog :
      (fun x : ℝ => 2 * √(4 * x) * Real.log (4 * x)) =o[atTop] fun x : ℝ => x := by
    have hsq : ∀ x : ℝ, 0 ≤ x → √(4 * x) = 2 * √x := by
      intro x hx
      rw [show (4 : ℝ) * x = 2 ^ 2 * x by norm_num, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
    have hA : (fun x : ℝ => 2 * √(4 * x)) =O[atTop] Real.sqrt := by
      refine IsBigO.of_bound 4 ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [hsq x hx, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.sqrt_nonneg x)]
      linarith [Real.sqrt_nonneg x]
    have hB : (fun x : ℝ => Real.log (4 * x)) =o[atTop] Real.sqrt := by
      refine (log_isLittleO_sqrt.comp_tendsto h4).trans_isBigO ?_
      refine IsBigO.of_bound 2 ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [Function.comp_apply]
      rw [hsq x hx, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.sqrt_nonneg x)]
    refine (hA.mul_isLittleO hB).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_self_sqrt hx
  exact hlog.add hsqrtlog

/--
Leaf `Π`, asymptotic form: the comparable band `(n, 4n]` contains at least of
the order of `n / log n` primes.
-/
theorem comparablePrimes_card_isBigO :
    (fun n : ℕ => (n : ℝ) / Real.log n) =O[atTop]
      fun n : ℕ => ((comparablePrimes n).card : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the error term, transported to `ℕ`
  have herr := chebyshev_error_isLittleO.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.log (4 * (n : ℝ) + 1) + 2 * √(4 * (n : ℝ)) * Real.log (4 * (n : ℝ)) ≤
        Real.log 2 * (n : ℝ) := by
    filter_upwards [herr.def hlog2, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      Real.log (4 * (n : ℝ) + 1) + 2 * √(4 * (n : ℝ)) * Real.log (4 * (n : ℝ))
          ≤ ‖Real.log (4 * (n : ℝ) + 1) + 2 * √(4 * (n : ℝ)) * Real.log (4 * (n : ℝ))‖ :=
        le_abs_self _
      _ ≤ Real.log 2 * ‖(n : ℝ)‖ := hn
      _ = Real.log 2 * (n : ℝ) := by rw [Real.norm_of_nonneg hn0]
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  filter_upwards [hsmall, eventually_ge_atTop 4] with n hn hn4
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn4' : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
  -- lower bound for the log mass of the band
  have hband : Real.log 2 * (n : ℝ) ≤ ∑ p ∈ comparablePrimes n, Real.log p := by
    have hge := Chebyshev.theta_ge (4 * n)
    have hle := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) hn0.le
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [sum_log_comparablePrimes]
    rw [hcast] at hge ⊢
    rw [hlog4] at hle
    linarith [hn]
  -- upper bound for the same mass
  have hupper : ∑ p ∈ comparablePrimes n, Real.log p ≤
      (comparablePrimes n).card * (2 * Real.log (n : ℝ)) := by
    refine le_trans (sum_log_comparablePrimes_le n) ?_
    have hle : Real.log (4 * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hn0)]
      have : Real.log 4 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn4'
      linarith
    have hcard : (0 : ℝ) ≤ ((comparablePrimes n).card : ℝ) := Nat.cast_nonneg _
    calc
      ((comparablePrimes n).card : ℝ) * Real.log (4 * (n : ℝ))
          ≤ ((comparablePrimes n).card : ℝ) * (2 * Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hle hcard
      _ = _ := rfl
  have hcard0 : (0 : ℝ) ≤ ((comparablePrimes n).card : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hcard0, div_le_iff₀ hlogn]
  have key := le_trans hband hupper
  have hshape : (2 : ℝ) / Real.log 2 * ((comparablePrimes n).card : ℝ) * Real.log (n : ℝ)
      = (((comparablePrimes n).card : ℝ) * (2 * Real.log (n : ℝ))) / Real.log 2 := by
    field_simp
  rw [hshape, le_div_iff₀ hlog2]
  linarith [key]

end Erdos289
