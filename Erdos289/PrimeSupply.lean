module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Comparable prime supply from Mathlib's Chebyshev bounds

The provider is derived locally from `Chebyshev.theta_ge` and
`Chebyshev.theta_le_log4_mul_x`.  It introduces no prime-number-theorem
dependency or additional assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Nat.Prime
open Finset Real

namespace Erdos289

/-- The primes of the band `(n, Λ n]`. -/
def bandPrimes (Λ n : ℕ) : Finset ℕ :=
  Nat.primesLE (Λ * n) \ Nat.primesLE n

theorem mem_bandPrimes {Λ n p : ℕ} :
    p ∈ bandPrimes Λ n ↔ n < p ∧ p ≤ Λ * n ∧ p.Prime := by
  rw [bandPrimes, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp4, hpprime⟩, hpn⟩
    exact ⟨lt_of_not_ge fun h => hpn ⟨h, hpprime⟩, hp4, hpprime⟩
  · rintro ⟨hnp, hp4, hpprime⟩
    exact ⟨⟨hp4, hpprime⟩, fun h => (not_le_of_gt hnp) h.1⟩

/-- The Chebyshev theta increment is exactly the log mass of a band. -/
theorem sum_log_bandPrimes {Λ : ℕ} (hΛ : 1 ≤ Λ) (n : ℕ) :
    ∑ p ∈ bandPrimes Λ n, log p =
      Chebyshev.theta ((Λ * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) := by
  have hsub : Nat.primesLE n ⊆ Nat.primesLE (Λ * n) :=
    Nat.primesLE_mono (Nat.le_mul_of_pos_left n hΛ)
  rw [Chebyshev.theta_eq_sum_primesLE_log (Λ * n),
    Chebyshev.theta_eq_sum_primesLE_log n]
  unfold bandPrimes
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => log p) hsub
  linarith

/-- Every log weight in a band is bounded by the log of its top. -/
theorem sum_log_bandPrimes_le (Λ n : ℕ) :
    ∑ p ∈ bandPrimes Λ n, log p ≤
      (bandPrimes Λ n).card * log (Λ * n) := by
  calc
    ∑ p ∈ bandPrimes Λ n, log p ≤
        ∑ _p ∈ bandPrimes Λ n, log (Λ * n) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by
          exact_mod_cast (mem_bandPrimes.mp hp).2.2.pos)
        (by exact_mod_cast (mem_bandPrimes.mp hp).2.1)
    _ = (bandPrimes Λ n).card * log (Λ * n) := by simp

/--
The Chebyshev bound at the witness ratio four, in raw form.  The `4` here is a
witness: it is the ratio at which the available mathlib bounds already give a
positive main term.  The statement consumed downstream is the parametric
`Erdos289.ComparableBand`.
-/
theorem bandPrimeSupply_explicit_four (n : ℕ) (hn : 0 < n) :
    (((4 * n : ℕ) : ℝ) * log 2 - log ((4 * n + 1 : ℕ) : ℝ) -
          2 * √((4 * n : ℕ) : ℝ) * log ((4 * n : ℕ) : ℝ) -
        log 4 * (n : ℝ)) /
        log ((4 * n : ℕ) : ℝ) ≤
      (bandPrimes 4 n).card := by
  have hlog : 0 < log ((4 * n : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < 4 * n by omega)
  apply (div_le_iff₀ hlog).2
  calc
    ((4 * n : ℕ) : ℝ) * log 2 - log ((4 * n + 1 : ℕ) : ℝ) -
          2 * √((4 * n : ℕ) : ℝ) * log ((4 * n : ℕ) : ℝ) -
        log 4 * (n : ℝ)
        ≤ Chebyshev.theta ((4 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) := by
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
            sub_le_sub (Chebyshev.theta_ge (4 * n))
              (Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity))
    _ = ∑ p ∈ bandPrimes 4 n, log p := by
      rw [sum_log_bandPrimes (by norm_num)]
    _ ≤ (bandPrimes 4 n).card * log (4 * n) :=
      sum_log_bandPrimes_le 4 n
    _ = ((bandPrimes 4 n).card : ℝ) * log ((4 * n : ℕ) : ℝ) := by
      norm_num

end Erdos289
