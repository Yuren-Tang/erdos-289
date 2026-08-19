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
# Comparable prime bands

The statement is existential in the band ratio: there is a ratio `Λ > 1` for which
the band `(n, Λ n]` carries at least of the order of `n / log n` primes.  That
existential statement is `Erdos289.ComparableBand`, and it is what the row
mathematics uses.

A particular ratio is a *witness*, not the definition.
`Erdos289.bandPrimes_card_isBigO` proves that every integer ratio at least
three is one, and `Erdos289.comparableBandThree` is the smallest witness this
mechanism supplies: subtracting mathlib's two Chebyshev estimates leaves the
main term `(Λ - 2)(log 2) n`.

The statement is asymptotic because the mathematics is asymptotic; it is not
replaced by an inequality valid beyond a hand-chosen numerical threshold.  The
`√x log x` error term of the theta lower bound is absorbed by
`Asymptotics.IsLittleO`.
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
The error term of the Chebyshev lower bound for the theta increment over a
band of ratio `Λ` is `o(x)`.
-/
private theorem chebyshev_error_isLittleO {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    (fun x : ℝ => Real.log ((Λ : ℝ) * x + 1)
        + 2 * √((Λ : ℝ) * x) * Real.log ((Λ : ℝ) * x)) =o[atTop]
      fun x : ℝ => x := by
  have hΛR : (1 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by linarith
  have hmul : Tendsto (fun x : ℝ => (Λ : ℝ) * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hΛpos
  have hmul' : Tendsto (fun x : ℝ => (Λ : ℝ) * x + 1) atTop atTop :=
    hmul.atTop_add tendsto_const_nhds
  have hsq : ∀ x : ℝ, 0 ≤ x → √((Λ : ℝ) * x) = √(Λ : ℝ) * √x := fun x hx =>
    Real.sqrt_mul hΛpos.le x
  have hsqrtΛ : (1 : ℝ) ≤ √(Λ : ℝ) := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_le_sqrt hΛR
  -- `log (Λ x + 1) = o(x)`
  have hlog : (fun x : ℝ => Real.log ((Λ : ℝ) * x + 1)) =o[atTop] fun x : ℝ => x := by
    refine (Real.isLittleO_log_id_atTop.comp_tendsto hmul').trans_isBigO ?_
    refine IsBigO.of_bound ((Λ : ℝ) + 1) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simp only [Function.comp_apply, id_eq]
    rw [Real.norm_of_nonneg (by nlinarith), Real.norm_of_nonneg (by linarith)]
    nlinarith
  -- `√(Λ x) log (Λ x) = o(x)`
  have hsqrtlog :
      (fun x : ℝ => 2 * √((Λ : ℝ) * x) * Real.log ((Λ : ℝ) * x)) =o[atTop]
        fun x : ℝ => x := by
    have hA : (fun x : ℝ => 2 * √((Λ : ℝ) * x)) =O[atTop] Real.sqrt := by
      refine IsBigO.of_bound (2 * √(Λ : ℝ)) ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [hsq x hx, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.sqrt_nonneg x)]
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (Λ : ℝ)]
    have hB : (fun x : ℝ => Real.log ((Λ : ℝ) * x)) =o[atTop] Real.sqrt := by
      refine (log_isLittleO_sqrt.comp_tendsto hmul).trans_isBigO ?_
      refine IsBigO.of_bound (√(Λ : ℝ)) ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      simp only [Function.comp_apply]
      rw [hsq x hx, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (Real.sqrt_nonneg x)]
    refine (hA.mul_isLittleO hB).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.mul_self_sqrt hx
  exact hlog.add hsqrtlog

/--
A comparable band: an integer ratio at least two whose band `(n, Λ n]` carries
at least of the order of `n / log n` primes.  The ratio is existentially
quantified, so no particular ratio enters the mathematics downstream.
-/
structure ComparableBand where
  /-- The band ratio. -/
  ratio : ℕ
  two_le_ratio : 2 ≤ ratio
  /-- The band carries `≫ n / log n` primes. -/
  card_isBigO :
    (fun n : ℕ => (n : ℝ) / Real.log n) =O[atTop]
      fun n : ℕ => ((bandPrimes ratio n).card : ℝ)

/--
Every integer ratio at least three is a comparable band.

Three is the smallest ratio this mechanism reaches: subtracting the two
mathlib estimates leaves the main term `(Λ - 2)(log 2) n`, which is positive
exactly from `Λ = 3` on.  Whether a stronger route eventually reaches ratio two
is irrelevant to the statement, which quantifies the ratio away.
-/
theorem bandPrimes_card_isBigO {Λ : ℕ} (hΛ : 3 ≤ Λ) :
    (fun n : ℕ => (n : ℝ) / Real.log n) =O[atTop]
      fun n : ℕ => ((bandPrimes Λ n).card : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hΛR : (3 : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hΛ
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  -- the error term, transported to `ℕ`
  have herr := (chebyshev_error_isLittleO (Λ := Λ) (by omega)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall : ∀ᶠ n : ℕ in atTop,
      Real.log ((Λ : ℝ) * (n : ℝ) + 1)
          + 2 * √((Λ : ℝ) * (n : ℝ)) * Real.log ((Λ : ℝ) * (n : ℝ))
        ≤ (Real.log 2 / 2) * (n : ℝ) := by
    filter_upwards [herr.def (by positivity : (0 : ℝ) < Real.log 2 / 2)] with n hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    calc
      Real.log ((Λ : ℝ) * (n : ℝ) + 1)
            + 2 * √((Λ : ℝ) * (n : ℝ)) * Real.log ((Λ : ℝ) * (n : ℝ))
          ≤ ‖Real.log ((Λ : ℝ) * (n : ℝ) + 1)
              + 2 * √((Λ : ℝ) * (n : ℝ)) * Real.log ((Λ : ℝ) * (n : ℝ))‖ :=
        le_abs_self _
      _ ≤ (Real.log 2 / 2) * ‖(n : ℝ)‖ := hn
      _ = (Real.log 2 / 2) * (n : ℝ) := by rw [Real.norm_of_nonneg hn0]
  refine IsBigO.of_bound (4 / Real.log 2) ?_
  filter_upwards [hsmall, eventually_ge_atTop (max Λ 2)] with n hn hnbig
  have hnΛ : Λ ≤ n := le_trans (le_max_left _ _) hnbig
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hnbig
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnΛ' : (Λ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnΛ
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hcast : ((Λ * n : ℕ) : ℝ) = (Λ : ℝ) * (n : ℝ) := by push_cast; ring
  -- lower bound for the log mass of the band
  have hband : (Real.log 2 / 2) * (n : ℝ) ≤ ∑ p ∈ bandPrimes Λ n, Real.log p := by
    have hge := Chebyshev.theta_ge (Λ * n)
    have hle := Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) hn0.le
    rw [hcast] at hge
    have hmain : Real.log 2 * (n : ℝ)
        ≤ (Λ : ℝ) * (n : ℝ) * Real.log 2 - Real.log 4 * (n : ℝ) := by
      rw [hlog4]
      have hkey : 0 ≤ ((Λ : ℝ) - 3) * ((n : ℝ) * Real.log 2) :=
        mul_nonneg (by linarith) (by positivity)
      nlinarith [hkey]
    rw [sum_log_bandPrimes (by omega : 1 ≤ Λ), hcast]
    linarith
  -- upper bound for the same mass
  have hupper : ∑ p ∈ bandPrimes Λ n, Real.log p ≤
      (bandPrimes Λ n).card * (2 * Real.log (n : ℝ)) := by
    refine le_trans (sum_log_bandPrimes_le Λ n) ?_
    have hΛ0 : (0 : ℝ) < (Λ : ℝ) := by linarith
    have hle : Real.log ((Λ : ℝ) * (n : ℝ)) ≤ 2 * Real.log (n : ℝ) := by
      rw [Real.log_mul (ne_of_gt hΛ0) (ne_of_gt hn0)]
      have : Real.log (Λ : ℝ) ≤ Real.log (n : ℝ) := Real.log_le_log hΛ0 hnΛ'
      linarith
    exact mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
  have hcard0 : (0 : ℝ) ≤ ((bandPrimes Λ n).card : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hcard0, div_le_iff₀ hlogn]
  have key := le_trans hband hupper
  have hshape : (4 : ℝ) / Real.log 2 * ((bandPrimes Λ n).card : ℝ) * Real.log (n : ℝ)
      = (((bandPrimes Λ n).card : ℝ) * (2 * Real.log (n : ℝ))) / (Real.log 2 / 2) := by
    field_simp
    ring
  rw [hshape, le_div_iff₀ (by positivity : (0 : ℝ) < Real.log 2 / 2)]
  linarith [key]

/-- The smallest ratio the available Chebyshev bounds supply. -/
def comparableBandThree : ComparableBand where
  ratio := 3
  two_le_ratio := by norm_num
  card_isBigO := bandPrimes_card_isBigO (by norm_num)

end Erdos289
