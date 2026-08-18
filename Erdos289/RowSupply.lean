module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.SignedInverseReservoir
public import Erdos289.PrimeSupplyAsymptotic

@[expose] public section

/-!
# The carrier band of a prime-power current

The signed-inverse construction draws its carriers from a comparable prime band
below the current `Q`.  Choosing the band as `(⌊(Q-1)/4⌋, 4⌊(Q-1)/4⌋]` makes the
condition `b < Q` automatic, so the only carrier lost to the current-stage
exclusions is `p` itself.

Two consequences are recorded here, and they are of different kinds.  The
comparison between the band and the carrier set is exact finite combinatorics.
The growth of the band is asymptotic, and stays asymptotic: it is inherited
from `Erdos289.comparablePrimes_card_isBigO`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics

namespace Erdos289
namespace SignedInverse

/-- The base of the comparable band used at current `Q`. -/
def bandBase (Q : ℕ) : ℕ := (Q - 1) / 4

theorem four_mul_bandBase_lt {Q : ℕ} (hQ : 0 < Q) : 4 * bandBase Q < Q := by
  unfold bandBase
  omega

theorem bandBase_le {Q : ℕ} : 4 * bandBase Q ≤ Q := by
  unfold bandBase
  omega

/-- Inside the chosen band the bound `b < Q` is automatic. -/
theorem carrierPrimes_eq_erase {Q p : ℕ} (hQ : 0 < Q) :
    carrierPrimes Q p (bandBase Q) = (comparablePrimes (bandBase Q)).erase p := by
  classical
  ext b
  rw [mem_carrierPrimes_iff, Finset.mem_erase, mem_comparablePrimes]
  constructor
  · rintro ⟨h1, h2, h3, -, h5⟩
    exact ⟨h5, h1, h2, h3⟩
  · rintro ⟨h5, h1, h2, h3⟩
    have := four_mul_bandBase_lt (Q := Q) hQ
    exact ⟨h1, h2, h3, by omega, h5⟩

/--
Exactly one carrier can be lost to the current-stage exclusions: the current
prime itself.
-/
theorem card_carrierPrimes_ge {Q p : ℕ} (hQ : 0 < Q) :
    (comparablePrimes (bandBase Q)).card - 1 ≤ (carrierPrimes Q p (bandBase Q)).card := by
  classical
  rw [carrierPrimes_eq_erase hQ]
  by_cases hp : p ∈ comparablePrimes (bandBase Q)
  · rw [Finset.card_erase_of_mem hp]
  · rw [Finset.erase_eq_of_notMem hp]
    omega

/-- The band base grows linearly in the current. -/
theorem bandBase_isBigO :
    (fun Q : ℕ => (Q : ℝ)) =O[atTop] fun Q : ℕ => ((bandBase Q : ℕ) : ℝ) := by
  refine IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 8] with Q hQ
  have hb : 1 ≤ bandBase Q := by unfold bandBase; omega
  have hQb : Q ≤ 8 * bandBase Q := by unfold bandBase; omega
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast hQb

theorem tendsto_bandBase : Filter.Tendsto bandBase atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨4 * b + 1, fun a ha => ?_⟩
  unfold bandBase
  omega

/--
The band carries `≫ Q / log Q` primes.  The growth is asymptotic and stays
asymptotic: it is `Erdos289.comparablePrimes_card_isBigO` reindexed along the
band base.
-/
theorem bandCard_isBigO :
    (fun Q : ℕ => (Q : ℝ) / Real.log Q) =O[atTop]
      fun Q : ℕ => ((comparablePrimes (bandBase Q)).card : ℝ) := by
  have hcomp :
      (fun Q : ℕ => ((bandBase Q : ℕ) : ℝ) / Real.log (bandBase Q)) =O[atTop]
        fun Q : ℕ => ((comparablePrimes (bandBase Q)).card : ℝ) :=
    comparablePrimes_card_isBigO.comp_tendsto tendsto_bandBase
  refine IsBigO.trans ?_ hcomp
  refine IsBigO.of_bound 8 ?_
  filter_upwards [eventually_ge_atTop 16] with Q hQ
  have hb : 3 ≤ bandBase Q := by unfold bandBase; omega
  have hQb : Q ≤ 8 * bandBase Q := by unfold bandBase; omega
  have hble : bandBase Q ≤ Q := by unfold bandBase; omega
  have hbR : (3 : ℝ) ≤ ((bandBase Q : ℕ) : ℝ) := by exact_mod_cast hb
  have hQR : (16 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlogb : 0 < Real.log (bandBase Q) := Real.log_pos (by linarith)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log (bandBase Q) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hble)
  have hQbR : (Q : ℝ) ≤ 8 * ((bandBase Q : ℕ) : ℝ) := by exact_mod_cast hQb
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  rw [div_le_iff₀ hlogQ, mul_comm (8 : ℝ), mul_assoc, div_mul_eq_mul_div,
    le_div_iff₀ hlogb]
  nlinarith [hlogb, hlogQ, hbR, hQR]

end SignedInverse
end Erdos289
