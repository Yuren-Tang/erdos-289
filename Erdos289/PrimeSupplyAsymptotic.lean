module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.PrimeSupply
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The comparable-prime count in the form consumed downstream

`Erdos289.comparablePrimeSupply_explicit` is the raw Chebyshev consequence: an
inequality still carrying the `√x log x` error term of the theta lower bound.
Everything downstream instead consumes

`n / (2 log n) ≤ #{p prime : n < p ≤ 4n}`

from an explicit threshold.  Absorbing the error term is the only content of
this module; no new arithmetic input is used, and in particular no
prime-number-theorem input.

The threshold `50 ^ 4` is not optimal.  It is chosen so that the estimates stay
elementary: `log x ≤ 4 x^{1/4}` is enough to make the error term lower order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

namespace Erdos289

/-- `log x ≤ 4 x^{1/4}`, written through iterated square roots. -/
theorem log_le_four_mul_quarticRoot {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hssx : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.2 hsx
  have h1 : Real.log (Real.sqrt (Real.sqrt x)) ≤ Real.sqrt (Real.sqrt x) - 1 :=
    Real.log_le_sub_one_of_pos hssx
  have h2 : Real.log (Real.sqrt (Real.sqrt x)) = Real.log x / 4 := by
    rw [Real.log_sqrt hsx.le, Real.log_sqrt hx.le]
    ring
  rw [h2] at h1
  linarith

/-- The fourth root of a real number at least `50 ^ 4` is at least `50`. -/
theorem fifty_le_quarticRoot {x : ℝ} (hx : (50 : ℝ) ^ 4 ≤ x) :
    (50 : ℝ) ≤ Real.sqrt (Real.sqrt x) := by
  have h1 : ((50 : ℝ) ^ 2) ≤ Real.sqrt x := by
    rw [show ((50 : ℝ) ^ 2) = Real.sqrt (((50 : ℝ) ^ 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  rw [show (50 : ℝ) = Real.sqrt ((50 : ℝ) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt h1

/-- The fourth power of the fourth root. -/
theorem quarticRoot_pow_four {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) ^ 4 = x := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  calc
    Real.sqrt (Real.sqrt x) ^ 4 = (Real.sqrt (Real.sqrt x) ^ 2) ^ 2 := by ring
    _ = Real.sqrt x ^ 2 := by rw [Real.sq_sqrt hsx]
    _ = x := Real.sq_sqrt hx

/-- `√x` is the square of the fourth root. -/
theorem sqrt_eq_quarticRoot_sq (x : ℝ) :
    Real.sqrt x = Real.sqrt (Real.sqrt x) ^ 2 :=
  (Real.sq_sqrt (Real.sqrt_nonneg x)).symm

/--
The Chebyshev numerator dominates `n` once `n ≥ 50 ^ 4`.  This is the step that
absorbs the `√x log x` error term of the theta lower bound.
-/
theorem chebyshev_numerator_ge (n : ℕ) (hn : 50 ^ 4 ≤ n) :
    (n : ℝ) ≤
      ((4 * n : ℕ) : ℝ) * Real.log 2 - Real.log ((4 * n + 1 : ℕ) : ℝ) -
        2 * √((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) -
        Real.log 4 * (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnbig : (50 : ℝ) ^ 4 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
  have hcast1 : ((4 * n + 1 : ℕ) : ℝ) = 4 * (n : ℝ) + 1 := by push_cast; ring
  rw [hcast, hcast1]
  set s : ℝ := Real.sqrt (Real.sqrt (n : ℝ)) with hs
  have hs50 : (50 : ℝ) ≤ s := fifty_le_quarticRoot hnbig
  have hs0 : (0 : ℝ) < s := by linarith
  have hs4 : s ^ 4 = (n : ℝ) := quarticRoot_pow_four hn0.le
  have hsqrtn : Real.sqrt (n : ℝ) = s ^ 2 := sqrt_eq_quarticRoot_sq (n : ℝ)
  have hsqrt4n : √(4 * (n : ℝ)) = 2 * s ^ 2 := by
    rw [show (4 : ℝ) * (n : ℝ) = 2 ^ 2 * (n : ℝ) by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), hsqrtn]
  -- elementary logarithm bounds
  have hlog2gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlogn : Real.log (n : ℝ) ≤ 4 * s := log_le_four_mul_quarticRoot hn0
  have hlog4n : Real.log (4 * (n : ℝ)) ≤ 2 + 4 * s := by
    rw [Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 4 ≤ 2 := by rw [hlog4eq]; linarith
    linarith
  have hlog4n_nonneg : 0 ≤ Real.log (4 * (n : ℝ)) := by
    apply Real.log_nonneg
    nlinarith
  have hlog4n1 : Real.log (4 * (n : ℝ) + 1) ≤ 3 + 4 * s := by
    have hle : (4 : ℝ) * (n : ℝ) + 1 ≤ 8 * (n : ℝ) := by nlinarith
    have h8 : Real.log 8 ≤ 3 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast; linarith
    calc
      Real.log (4 * (n : ℝ) + 1) ≤ Real.log (8 * (n : ℝ)) :=
        Real.log_le_log (by positivity) hle
      _ = Real.log 8 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 3 + 4 * s := by linarith
  -- the polynomial inequality that makes the error term lower order
  have h1 : (50 : ℝ) * s ^ 3 ≤ s ^ 4 := by nlinarith [pow_pos hs0 3]
  have h2 : (50 : ℝ) * s ^ 2 ≤ s ^ 3 := by nlinarith [pow_pos hs0 2]
  have h3 : (50 : ℝ) * s ≤ s ^ 2 := by nlinarith
  have hmain : 8 * s ^ 2 + 16 * s ^ 3 + 3 + 4 * s ≤ 0.386 * (n : ℝ) := by
    rw [← hs4]
    linarith
  have herror :
      2 * √(4 * (n : ℝ)) * Real.log (4 * (n : ℝ)) ≤ 8 * s ^ 2 + 16 * s ^ 3 := by
    rw [hsqrt4n]
    have hmul := mul_le_mul_of_nonneg_left hlog4n (show (0 : ℝ) ≤ 4 * s ^ 2 by positivity)
    nlinarith [hmul]
  have hcoef : (0 : ℝ) ≤ (2 * Real.log 2 - 1 - 0.386) * (n : ℝ) :=
    mul_nonneg (by linarith) hn0.le
  rw [hlog4eq]
  nlinarith [hcoef, hmain, herror, hlog4n1]

/-- The comparable-prime count in the form consumed downstream. -/
theorem card_comparablePrimes_ge (n : ℕ) (hn : 50 ^ 4 ≤ n) :
    (n : ℝ) / (2 * Real.log n) ≤ (comparablePrimes n).card := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by
    have : (4 : ℕ) ≤ n := by omega
    exact_mod_cast this
  have hcast : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by push_cast; ring
  have hL : Real.log ((4 * n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    rw [hcast, Real.log_mul (by norm_num) (by positivity)]
    have : Real.log 4 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn4
    linarith
  have hLpos : 0 < Real.log ((4 * n : ℕ) : ℝ) := by
    rw [hcast]
    apply Real.log_pos
    linarith
  calc
    (n : ℝ) / (2 * Real.log (n : ℝ)) ≤ (n : ℝ) / Real.log ((4 * n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hn0.le hLpos hL
    _ ≤ (((4 * n : ℕ) : ℝ) * Real.log 2 - Real.log ((4 * n + 1 : ℕ) : ℝ) -
          2 * √((4 * n : ℕ) : ℝ) * Real.log ((4 * n : ℕ) : ℝ) -
          Real.log 4 * (n : ℝ)) / Real.log ((4 * n : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right (chebyshev_numerator_ge n hn) hLpos.le
    _ ≤ (comparablePrimes n).card :=
      comparablePrimeSupply_explicit n (by omega)

end Erdos289
