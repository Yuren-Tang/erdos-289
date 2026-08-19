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

/-- The carrier family is indexed by the retained band primes, one carrier
each. -/
theorem card_carrierFamily {Λ Q p e n : ℕ} (hp : p.Prime) (hQ : Q = p ^ e) :
    (carrierFamily (Λ := Λ) (n := n) hp hQ).card = (carrierPrimes Λ Q p n).card := by
  classical
  rw [carrierFamily, Finset.card_image_of_injOn, Finset.card_attach]
  intro a _ b _ hab
  exact Subtype.ext (congrArg Carrier.b hab)

/-- A sufficient finite threshold for the scale inequality.  The threshold is a
proof witness; the public statement is `Erdos289.SignedInverse.eventually_scale_two`. -/
private theorem scale_two_of_lt {Λ Q : ℕ} (hΛ : 0 < Λ) (hQ : 2 * Λ ^ 3 < Q) :
    Q ^ 2 + 1 < (bandBase Λ Q + 1) ^ (2 + 1) := by
  have h1 : Q ≤ Λ * (bandBase Λ Q + 1) := by
    have := le_ratio_mul_bandBase_add (Λ := Λ) (Q := Q) hΛ
    have : Λ * (bandBase Λ Q + 1) = Λ * bandBase Λ Q + Λ := by ring
    omega
  have h2 : Q ^ 3 ≤ Λ ^ 3 * (bandBase Λ Q + 1) ^ 3 := by
    calc Q ^ 3 ≤ (Λ * (bandBase Λ Q + 1)) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = Λ ^ 3 * (bandBase Λ Q + 1) ^ 3 := by ring
  have hQ1 : 1 ≤ Q := by
    have : 1 ≤ Λ ^ 3 := Nat.one_le_pow _ _ hΛ
    omega
  have h3 : Λ ^ 3 * (Q ^ 2 + 1) < Q ^ 3 := by nlinarith [Nat.one_le_pow 2 Q hQ1]
  have hΛ3 : 0 < Λ ^ 3 := Nat.pow_pos hΛ
  have : Λ ^ 3 * (Q ^ 2 + 1) < Λ ^ 3 * (bandBase Λ Q + 1) ^ 3 := lt_of_lt_of_le h3 h2
  simpa using Nat.lt_of_mul_lt_mul_left this

/--
The coefficient-fibre scale can be taken to be the absolute constant two.

The scale inequality of the row certificate is `Q² + 1 < (n+1)^(d+1)` for the
band base `n`.  Since the base is a fixed fraction of the current, the cube of
the base already beats the square of the current for every large current, so
`d = 2` serves them all and the fibre scale never has to grow with the current.
Two is the least fixed exponent for which this is possible: a quadratic band
term cannot dominate `Q²`.
-/
theorem eventually_scale_two {Λ : ℕ} (hΛ : 0 < Λ) :
    ∀ᶠ Q : ℕ in atTop, Q ^ 2 + 1 < (bandBase Λ Q + 1) ^ (2 + 1) := by
  filter_upwards [eventually_gt_atTop (2 * Λ ^ 3)] with Q hQ
  exact scale_two_of_lt hΛ hQ

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

/-! ### The supply theorem -/

private theorem tendsto_natCast_div_log :
    Filter.Tendsto (fun Q : ℕ => (Q : ℝ) / Real.log Q) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun b => ?_
  have hc : (0 : ℝ) < 1 / (|b| + 1) := by positivity
  have hlog : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1 / (|b| + 1)) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.def hc
  obtain ⟨X, hX⟩ := (hlog.and (eventually_ge_atTop (2 : ℝ))).exists_forall_of_atTop
  obtain ⟨N, hN⟩ := exists_nat_gt (max X 2)
  refine ⟨N, fun Q hQ => ?_⟩
  have hQR : max X 2 ≤ (Q : ℝ) := by
    have : (N : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith [hN]
  have hXQ : X ≤ (Q : ℝ) := le_trans (le_max_left _ _) hQR
  have h2Q : (2 : ℝ) ≤ (Q : ℝ) := le_trans (le_max_right _ _) hQR
  obtain ⟨hbound, -⟩ := hX (Q : ℝ) hXQ
  have hlogpos : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg hlogpos.le, Real.norm_of_nonneg (by linarith)] at hbound
  have hkey : Real.log (Q : ℝ) * (|b| + 1) ≤ (Q : ℝ) := by
    have habs : (0 : ℝ) < |b| + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul] at hbound
    calc Real.log (Q : ℝ) * (|b| + 1) ≤ ((Q : ℝ) / (|b| + 1)) * (|b| + 1) := by
          exact mul_le_mul_of_nonneg_right hbound habs.le
      _ = (Q : ℝ) := by field_simp
  have : |b| + 1 ≤ (Q : ℝ) / Real.log (Q : ℝ) := by
    rw [le_div_iff₀ hlogpos]
    linarith [hkey]
  calc b ≤ |b| := le_abs_self b
    _ ≤ |b| + 1 := by linarith
    _ ≤ (Q : ℝ) / Real.log (Q : ℝ) := this

/--
The supply theorem: a demand that grows more slowly than the prime supply is
eventually met by the band.

This is the only place where the asymptotic input `Erdos289.ComparableBand`
meets the finite combinatorics of the row certificate.  The statement is
asymptotic on both sides — no threshold on the current is named, and no
particular band ratio appears.
-/
theorem eventually_demand_le_card_carrierPrimes
    (band : ComparableBand) {M : ℕ → ℕ}
    (hM : (fun Q : ℕ => (M Q : ℝ)) =o[atTop] fun Q : ℕ => (Q : ℝ) / Real.log Q) :
    ∀ᶠ Q : ℕ in atTop, ∀ p : ℕ,
      M Q ≤ (carrierPrimes band.ratio Q p (bandBase band.ratio Q)).card := by
  obtain ⟨C, hCpos, hC⟩ := (bandCard_isBigO band).exists_pos
  have h2 := hM.def (c := 1 / (2 * C)) (by positivity)
  have h3 : ∀ᶠ Q : ℕ in atTop, (4 * C : ℝ) ≤ (Q : ℝ) / Real.log Q :=
    tendsto_natCast_div_log.eventually_ge_atTop _
  filter_upwards [hC.bound, h2, h3, eventually_gt_atTop 0] with Q hQ1 hQ2 hQ3 hQ0 p
  set B := (bandPrimes band.ratio (bandBase band.ratio Q)).card with hB
  have hratio : (0 : ℝ) < (Q : ℝ) / Real.log Q := lt_of_lt_of_le (by positivity) hQ3
  rw [Real.norm_of_nonneg hratio.le, Real.norm_of_nonneg (Nat.cast_nonneg _)] at hQ1
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg hratio.le] at hQ2
  -- the band is large
  have hBR : (4 : ℝ) ≤ (B : ℝ) := by
    have : (4 * C : ℝ) ≤ C * (B : ℝ) := le_trans hQ3 hQ1
    nlinarith
  have hB4 : 4 ≤ B := by exact_mod_cast hBR
  -- the demand is at most half the band
  have hhalf : (M Q : ℝ) ≤ (B : ℝ) / 2 := by
    calc (M Q : ℝ) ≤ (1 / (2 * C)) * ((Q : ℝ) / Real.log Q) := hQ2
      _ ≤ (1 / (2 * C)) * (C * (B : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hQ1 (by positivity)
      _ = (B : ℝ) / 2 := by field_simp
  have hMB : (M Q : ℝ) ≤ (B : ℝ) - 1 := by linarith
  have hMBn : M Q ≤ B - 1 := by
    have : (M Q : ℝ) ≤ ((B - 1 : ℕ) : ℝ) := by
      have : ((B - 1 : ℕ) : ℝ) = (B : ℝ) - 1 := by
        have : (1 : ℕ) ≤ B := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [this]; exact hMB
    exact_mod_cast this
  exact le_trans hMBn (card_carrierPrimes_ge (Λ := band.ratio) (p := p) hQ0)

end SignedInverse
end Erdos289
