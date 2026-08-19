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

The signed-inverse construction draws its carriers from a band below the
current `Q`.  For a band of ratio `Λ` the base is `⌊(Q-1)/Λ⌋`, which is exactly
the largest base whose band stays below `Q`; the condition `b < Q` is then
automatic and the only carrier lost to the current-stage exclusions is `p`
itself.

Two consequences are recorded, and they are of different kinds.  The comparison
between the band and the carrier set is exact finite combinatorics.  The growth
of the band is asymptotic and stays asymptotic: it is inherited from
`Erdos289.ComparableBand`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Asymptotics

namespace Erdos289
namespace SignedInverse

/-- The base of the band of ratio `Λ` used at current `Q`. -/
def bandBase (Λ Q : ℕ) : ℕ := (Q - 1) / Λ

/-- The band stays strictly below the current. -/
theorem ratio_mul_bandBase_lt {Λ Q : ℕ} (hQ : 0 < Q) :
    Λ * bandBase Λ Q < Q := by
  have h : bandBase Λ Q * Λ ≤ Q - 1 := Nat.div_mul_le_self (Q - 1) Λ
  have h' : Λ * bandBase Λ Q = bandBase Λ Q * Λ := Nat.mul_comm _ _
  omega

/-- The base is the largest one with that property, up to the ratio. -/
theorem le_ratio_mul_bandBase_add {Λ Q : ℕ} (hΛ : 0 < Λ) :
    Q ≤ Λ * bandBase Λ Q + Λ := by
  have h := Nat.div_add_mod (Q - 1) Λ
  have hm : (Q - 1) % Λ < Λ := Nat.mod_lt _ hΛ
  unfold bandBase
  omega

/-- Inside the chosen band the bound `b < Q` is automatic. -/
theorem carrierPrimes_eq_erase {Λ Q p : ℕ} (hQ : 0 < Q) :
    carrierPrimes Λ Q p (bandBase Λ Q)
      = (bandPrimes Λ (bandBase Λ Q)).erase p := by
  classical
  ext b
  rw [mem_carrierPrimes_iff, Finset.mem_erase, mem_bandPrimes]
  constructor
  · rintro ⟨h1, h2, h3, -, h5⟩
    exact ⟨h5, h1, h2, h3⟩
  · rintro ⟨h5, h1, h2, h3⟩
    have := ratio_mul_bandBase_lt (Λ := Λ) (Q := Q) hQ
    exact ⟨h1, h2, h3, by omega, h5⟩

/--
Exactly one carrier can be lost to the current-stage exclusions: the current
prime itself.
-/
theorem card_carrierPrimes_ge {Λ Q p : ℕ} (hQ : 0 < Q) :
    (bandPrimes Λ (bandBase Λ Q)).card - 1
      ≤ (carrierPrimes Λ Q p (bandBase Λ Q)).card := by
  classical
  rw [carrierPrimes_eq_erase hQ]
  by_cases hp : p ∈ bandPrimes Λ (bandBase Λ Q)
  · rw [Finset.card_erase_of_mem hp]
  · rw [Finset.erase_eq_of_notMem hp]
    omega

/-- The band base grows linearly in the current. -/
theorem bandBase_isBigO {Λ : ℕ} (hΛ : 0 < Λ) :
    (fun Q : ℕ => (Q : ℝ)) =O[atTop] fun Q : ℕ => ((bandBase Λ Q : ℕ) : ℝ) := by
  refine IsBigO.of_bound (2 * Λ) ?_
  filter_upwards [eventually_ge_atTop (2 * Λ)] with Q hQ
  have h1 : Q ≤ Λ * bandBase Λ Q + Λ := le_ratio_mul_bandBase_add hΛ
  have hQb : Q ≤ 2 * (Λ * bandBase Λ Q) := by omega
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have h2 : Q ≤ 2 * Λ * bandBase Λ Q := by
    have hassoc : 2 * (Λ * bandBase Λ Q) = 2 * Λ * bandBase Λ Q := by ring
    omega
  exact_mod_cast h2

theorem tendsto_bandBase {Λ : ℕ} (hΛ : 0 < Λ) :
    Filter.Tendsto (bandBase Λ) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ⟨Λ * b + 1, fun a ha => ?_⟩
  refine (Nat.le_div_iff_mul_le hΛ).2 ?_
  have : b * Λ = Λ * b := Nat.mul_comm _ _
  omega

/--
The band carries `≫ Q / log Q` primes.  The growth is asymptotic and stays
asymptotic: it is `Erdos289.ComparableBand` reindexed along the band base.
-/
theorem bandCard_isBigO (band : ComparableBand) :
    (fun Q : ℕ => (Q : ℝ) / Real.log Q) =O[atTop]
      fun Q : ℕ => ((bandPrimes band.ratio (bandBase band.ratio Q)).card : ℝ) := by
  have hΛ2 := band.two_le_ratio
  have hΛ : 0 < band.ratio := by omega
  have hcomp :
      (fun Q : ℕ => ((bandBase band.ratio Q : ℕ) : ℝ)
          / Real.log (bandBase band.ratio Q)) =O[atTop]
        fun Q : ℕ => ((bandPrimes band.ratio (bandBase band.ratio Q)).card : ℝ) :=
    band.card_isBigO.comp_tendsto (tendsto_bandBase hΛ)
  refine IsBigO.trans ?_ hcomp
  refine IsBigO.of_bound (2 * band.ratio) ?_
  filter_upwards [eventually_ge_atTop (4 * band.ratio + 4)] with Q hQ
  have h1 : Q ≤ band.ratio * bandBase band.ratio Q + band.ratio :=
    le_ratio_mul_bandBase_add hΛ
  have hb3 : 3 ≤ bandBase band.ratio Q := by
    by_contra hcon
    have : bandBase band.ratio Q ≤ 2 := by omega
    have : band.ratio * bandBase band.ratio Q ≤ band.ratio * 2 :=
      Nat.mul_le_mul_left _ this
    omega
  have hQb : Q ≤ 2 * (band.ratio * bandBase band.ratio Q) := by omega
  have hble : bandBase band.ratio Q ≤ Q := by
    have := ratio_mul_bandBase_lt (Λ := band.ratio) (Q := Q) (by omega)
    have h2 : bandBase band.ratio Q ≤ band.ratio * bandBase band.ratio Q :=
      Nat.le_mul_of_pos_left _ hΛ
    omega
  have hbR : (3 : ℝ) ≤ ((bandBase band.ratio Q : ℕ) : ℝ) := by exact_mod_cast hb3
  have hQR : (4 : ℝ) ≤ (Q : ℝ) := by
    have : (4 : ℕ) ≤ Q := by omega
    exact_mod_cast this
  have hlogb : 0 < Real.log (bandBase band.ratio Q) := Real.log_pos (by linarith)
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log (bandBase band.ratio Q) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log (by linarith) (by exact_mod_cast hble)
  have hQbR : (Q : ℝ) ≤ 2 * (band.ratio : ℝ) * ((bandBase band.ratio Q : ℕ) : ℝ) := by
    have : ((Q : ℕ) : ℝ) ≤ ((2 * (band.ratio * bandBase band.ratio Q) : ℕ) : ℝ) := by
      exact_mod_cast hQb
    calc (Q : ℝ) ≤ ((2 * (band.ratio * bandBase band.ratio Q) : ℕ) : ℝ) := this
      _ = 2 * (band.ratio : ℝ) * ((bandBase band.ratio Q : ℕ) : ℝ) := by push_cast; ring
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hstep : (Q : ℝ) / Real.log (Q : ℝ)
      ≤ (2 * (band.ratio : ℝ) * ((bandBase band.ratio Q : ℕ) : ℝ)) / Real.log (Q : ℝ) := by
    gcongr
  refine hstep.trans ?_
  rw [mul_div_assoc]
  gcongr

end SignedInverse
end Erdos289
