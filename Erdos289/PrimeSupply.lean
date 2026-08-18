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

/-- Primes in the comparable interval `(n,4n]`. -/
def comparablePrimes (n : ℕ) : Finset ℕ :=
  Nat.primesLE (4 * n) \ Nat.primesLE n

theorem mem_comparablePrimes {n p : ℕ} :
    p ∈ comparablePrimes n ↔ n < p ∧ p ≤ 4 * n ∧ p.Prime := by
  rw [comparablePrimes, Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hp4, hpprime⟩, hpn⟩
    exact ⟨lt_of_not_ge fun h => hpn ⟨h, hpprime⟩, hp4, hpprime⟩
  · rintro ⟨hnp, hp4, hpprime⟩
    exact ⟨⟨hp4, hpprime⟩, fun h => (not_le_of_gt hnp) h.1⟩

/-- The Chebyshev theta increment is exactly the log mass of the comparable band. -/
theorem sum_log_comparablePrimes (n : ℕ) :
    ∑ p ∈ comparablePrimes n, log p =
      Chebyshev.theta ((4 * n : ℕ) : ℝ) - Chebyshev.theta (n : ℝ) := by
  have hsub : Nat.primesLE n ⊆ Nat.primesLE (4 * n) :=
    Nat.primesLE_mono (by omega)
  rw [Chebyshev.theta_eq_sum_primesLE_log (4 * n),
    Chebyshev.theta_eq_sum_primesLE_log n]
  unfold comparablePrimes
  have hsum := Finset.sum_sdiff (f := fun p : ℕ => log p) hsub
  linarith

/-- Every log weight in the comparable band is bounded by `log(4n)`. -/
theorem sum_log_comparablePrimes_le (n : ℕ) :
    ∑ p ∈ comparablePrimes n, log p ≤
      (comparablePrimes n).card * log (4 * n) := by
  calc
    ∑ p ∈ comparablePrimes n, log p ≤
        ∑ _p ∈ comparablePrimes n, log (4 * n) := by
      apply Finset.sum_le_sum
      intro p hp
      exact Real.log_le_log (by
          exact_mod_cast (mem_comparablePrimes.mp hp).2.2.pos)
        (by exact_mod_cast (mem_comparablePrimes.mp hp).2.1)
    _ = (comparablePrimes n).card * log (4 * n) := by simp

/-- An explicit kernel-checked lower bound for the number of primes in `(n,4n]`. -/
theorem comparablePrimeSupply_explicit (n : ℕ) (hn : 0 < n) :
    (((4 * n : ℕ) : ℝ) * log 2 - log ((4 * n + 1 : ℕ) : ℝ) -
          2 * √((4 * n : ℕ) : ℝ) * log ((4 * n : ℕ) : ℝ) -
        log 4 * (n : ℝ)) /
        log ((4 * n : ℕ) : ℝ) ≤
      (comparablePrimes n).card := by
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
    _ = ∑ p ∈ comparablePrimes n, log p := by
      rw [sum_log_comparablePrimes]
    _ ≤ (comparablePrimes n).card * log (4 * n) :=
      sum_log_comparablePrimes_le n
    _ = ((comparablePrimes n).card : ℝ) * log ((4 * n : ℕ) : ℝ) := by
      norm_num

end Erdos289
