import Reciprocal.CurrentFiltration
import Reciprocal.Filters
import Universal.Asymptotics

import Mathlib.NumberTheory.Chebyshev

/-!
# Leaf Π — Chebyshev prime-log growth

The endpoint-scale prime-log function `θ(X) = ∑_{p ≤ X} log p` and the
prime-power-log function `ψ(X) = ∑_{p^a ≤ X} log p`, together with the two-sided
linear Chebyshev bounds packaged as the public object `PrimeLogBounds`.
-/

open Filter Real

namespace Erdos289

/-- The endpoint-scale prime-log function `θ(X) = ∑_{p ≤ X} log p`. -/
noncomputable def primeLogTheta (X : ℕ) : ℝ := Chebyshev.theta X

/-- The endpoint-scale prime-power-log function `ψ(X) = ∑_{p^a ≤ X} log p`. -/
noncomputable def primeLogPsi (X : ℕ) : ℝ := Chebyshev.psi X

theorem primeLogTheta_nonneg (X : ℕ) : 0 ≤ primeLogTheta X := Chebyshev.theta_nonneg _

theorem primeLogPsi_nonneg (X : ℕ) : 0 ≤ primeLogPsi X := Chebyshev.psi_nonneg _

theorem primeLogTheta_le_primeLogPsi (X : ℕ) : primeLogTheta X ≤ primeLogPsi X :=
  Chebyshev.theta_le_psi _

theorem primeLogTheta_mono : Monotone primeLogTheta := fun _ _ h ↦
  Chebyshev.theta_mono (by exact_mod_cast h)

/-- Π.1: the linear lower bound for `ψ`, from the divisibility of the central
binomial coefficient by `lcm(1,…,2n)`. -/
theorem primeLogPsi_ge (X : ℕ) :
    (X : ℝ) * log 2 - log ((X : ℝ) + 1) ≤ primeLogPsi X :=
  Chebyshev.psi_ge X

/-- Π.2: the linear upper bound for `θ`. -/
theorem primeLogTheta_le (X : ℕ) : primeLogTheta X ≤ log 4 * X :=
  Chebyshev.theta_le_log4_mul_x (by positivity)

/-- Π.3: the linear upper bound for `ψ`. -/
theorem primeLogPsi_le (X : ℕ) : primeLogPsi X ≤ (log 4 + 4) * X :=
  Chebyshev.psi_le_const_mul_self (by positivity)

/-- Π.4: the prime powers of exponent at least two contribute at most
`2√X log X`. -/
theorem primeLogPsi_sub_primeLogTheta_le {X : ℕ} (hX : 1 ≤ X) :
    primeLogPsi X - primeLogTheta X ≤ 2 * √(X : ℝ) * log (X : ℝ) :=
  Chebyshev.psi_sub_theta_le (by exact_mod_cast hX)

/-- Π.4: the resulting linear lower bound for `θ`, before absorbing the error
term. -/
theorem primeLogTheta_ge (X : ℕ) :
    (X : ℝ) * log 2 - log ((X : ℝ) + 1) - 2 * √(X : ℝ) * log (X : ℝ) ≤ primeLogTheta X :=
  Chebyshev.theta_ge X

/-! ## The Chebyshev error term is sublinear -/

private theorem sqrtLog_isLittleO :
    (fun x : ℝ ↦ √x * log x) =o[atTop] (id : ℝ → ℝ) := by
  have h : (fun x : ℝ ↦ √x * log x) =o[atTop] (fun x : ℝ ↦ √x * x ^ (1 / 2 : ℝ)) :=
    (Asymptotics.isBigO_refl Real.sqrt atTop).mul_isLittleO
      (isLittleO_log_rpow_atTop (by norm_num))
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  norm_num

private theorem logSucc_isLittleO :
    (fun x : ℝ ↦ log (x + 1)) =o[atTop] (id : ℝ → ℝ) := by
  have h1 : (fun x : ℝ ↦ log (x + 1)) =o[atTop] (fun x : ℝ ↦ x + 1) :=
    Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  refine h1.trans_isBigO (Asymptotics.IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (by simp only [id]; linarith)]
  simp only [id]
  linarith

private theorem chebyshevError_isLittleO :
    (fun X : ℕ ↦ log ((X : ℝ) + 1) + 2 * √(X : ℝ) * log (X : ℝ)) =o[atTop]
      (fun X : ℕ ↦ (X : ℝ)) := by
  have h : (fun x : ℝ ↦ log (x + 1) + 2 * √x * log x) =o[atTop] (id : ℝ → ℝ) := by
    refine logSucc_isLittleO.add ?_
    have := sqrtLog_isLittleO.const_mul_left (2 : ℝ)
    simpa [mul_assoc] using this
  exact h.comp_tendsto tendsto_natCast_atTop_atTop

/-! ## The public prime-log bounds object -/

/-- `PrimeLogBounds`: real constants `0 < cθ < Cθ` together with the eventual
two-sided linear Chebyshev bound for `θ` along the endpoint index filter. -/
structure PrimeLogBounds where
  /-- The lower Chebyshev constant. -/
  lower : ℝ
  /-- The upper Chebyshev constant. -/
  upper : ℝ
  /-- The lower constant is positive. -/
  lower_pos : 0 < lower
  /-- The lower constant is smaller than the upper constant. -/
  lower_lt_upper : lower < upper
  /-- The eventual two-sided linear bound along the endpoint index filter. -/
  eventually_bounds :
    ∀ᶠ X in EndpointIndexFilter, lower * X ≤ primeLogTheta X ∧ primeLogTheta X ≤ upper * X

/-- The eventual two-sided bound, restated along `atTop` on the endpoint index
so that consumers need not name the endpoint index filter. -/
theorem PrimeLogBounds.eventually_atTop (B : PrimeLogBounds) :
    ∀ᶠ X : ℕ in atTop, B.lower * X ≤ primeLogTheta X ∧ primeLogTheta X ≤ B.upper * X :=
  B.eventually_bounds

/-- Π.1–Π.4: the two-sided linear Chebyshev bound exists. -/
theorem primeLogBounds_exists : Nonempty PrimeLogBounds := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos (by norm_num)
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hc : (0 : ℝ) < log 2 / 2 := by positivity
  have herr := chebyshevError_isLittleO.def hc
  refine ⟨{ lower := log 2 / 2
            upper := log 4
            lower_pos := hc
            lower_lt_upper := by rw [hlog4]; linarith
            eventually_bounds := ?_ }⟩
  rw [EndpointIndexFilter]
  filter_upwards [herr, eventually_ge_atTop 1] with X hX hX1
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hlogX : 0 ≤ log (X : ℝ) := Real.log_nonneg hXR
  have hlogX1 : 0 ≤ log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hsqrt : 0 ≤ √(X : ℝ) := Real.sqrt_nonneg _
  have hpos : 0 ≤ log ((X : ℝ) + 1) + 2 * √(X : ℝ) * log (X : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hpos,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (X : ℝ))] at hX
  refine ⟨?_, primeLogTheta_le X⟩
  have hge := primeLogTheta_ge X
  nlinarith [hge, hX]

/-- The eventual two-sided bound makes `θ` an eventual asymptotic companion of
the endpoint index, in the structural sense of `Universal.Asymptotics`. -/
theorem primeLogTheta_isTheta (B : PrimeLogBounds) :
    Erdos289.IsTheta atTop (fun X : ℕ ↦ primeLogTheta X) (fun X : ℕ ↦ (X : ℝ)) := by
  have hB := B.eventually_bounds
  rw [EndpointIndexFilter] at hB
  constructor
  · refine Asymptotics.IsBigO.of_bound B.upper ?_
    filter_upwards [hB, eventually_ge_atTop 1] with X hX hX1
    have hXR : (0 : ℝ) ≤ (X : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primeLogTheta_nonneg X),
      abs_of_nonneg hXR]
    exact hX.2
  · refine Asymptotics.IsBigO.of_bound B.lower⁻¹ ?_
    filter_upwards [hB, eventually_ge_atTop 1] with X hX hX1
    have hXR : (0 : ℝ) ≤ (X : ℝ) := by positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (primeLogTheta_nonneg X),
      abs_of_nonneg hXR]
    rw [inv_mul_eq_div, le_div_iff₀ B.lower_pos]
    calc (X : ℝ) * B.lower = B.lower * X := by ring
      _ ≤ primeLogTheta X := hX.1

end Erdos289
