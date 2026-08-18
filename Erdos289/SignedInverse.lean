module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Complementary inverse arithmetic

This is the coordinate boundary of the filtered-transverse reservoir proof.
The downstream interface will retain only the resulting intrinsic reservoir;
the inverse representatives and quotient coefficients defined here are witness
technology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-- The two graphs of inversion and negative inversion, with exact quotients. -/
structure ComplementaryPair (Q b : ℕ) where
  cPlus : ℕ
  cMinus : ℕ
  kPlus : ℕ
  kMinus : ℕ
  cPlus_pos : 0 < cPlus
  cPlus_lt : cPlus < Q
  cMinus_pos : 0 < cMinus
  cMinus_lt : cMinus < Q
  plus_eq : b * cPlus = Q * kPlus + 1
  minus_eq : b * cMinus + 1 = Q * kMinus
  kPlus_pos : 0 < kPlus
  kPlus_lt : kPlus < b
  kMinus_pos : 0 < kMinus
  kMinus_lt : kMinus < b
  k_add : kPlus + kMinus = b

/--
Complementary inverse representatives exist canonically up to the chosen least
residue representative.  No extended-Euclidean algorithm is exposed.
-/
noncomputable def complementaryPair
    (Q b : ℕ) (hQ : 1 < Q) (hb : 1 < b) (_hbQ : b < Q)
    (hcop : b.Coprime Q) : ComplementaryPair Q b := by
  letI : NeZero Q := ⟨by omega⟩
  letI : Fact (1 < Q) := ⟨hQ⟩
  have hbunit : IsUnit (b : ZMod Q) :=
    (ZMod.isUnit_iff_coprime b Q).2 hcop
  let u : (ZMod Q)ˣ := hbunit.unit
  let z : ZMod Q := (u⁻¹ : (ZMod Q)ˣ)
  let c : ℕ := z.val
  have hcz : (c : ZMod Q) = z := by
    exact ZMod.natCast_zmod_val z
  have hmulZ : ((b * c : ℕ) : ZMod Q) = 1 := by
    have hbzinv : (b : ZMod Q) * z = 1 := by
      simp [z, u]
    simpa only [Nat.cast_mul, hcz] using hbzinv
  have hmulZ' : ((b * c : ℕ) : ZMod Q) = ((1 : ℕ) : ZMod Q) := by
    simpa using hmulZ
  have hmodEq : b * c ≡ 1 [MOD Q] :=
    (ZMod.natCast_eq_natCast_iff (b * c) 1 Q).mp hmulZ'
  have hmod : (b * c) % Q = 1 := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hQ] using hmodEq
  have hc_lt : c < Q := ZMod.val_lt z
  have hc_pos : 0 < c := by
    by_contra hc
    have hc0 : c = 0 := by omega
    rw [hc0] at hmulZ
    simp at hmulZ
  let kp : ℕ := (b * c) / Q
  have hplus : b * c = Q * kp + 1 := by
    have hdiv := Nat.mod_add_div (b * c) Q
    rw [hmod] at hdiv
    dsimp [kp]
    omega
  have hbc_lt : b * c < b * Q := Nat.mul_lt_mul_of_pos_left hc_lt (by omega)
  have hkp_pos : 0 < kp := by
    by_contra hkp
    have hkp0 : kp = 0 := Nat.eq_zero_of_not_pos hkp
    have hbc1 : b * c = 1 := by
      calc
        b * c = Q * kp + 1 := hplus
        _ = 1 := by rw [hkp0]; simp
    have hble : b ≤ b * c := by
      calc
        b = b * 1 := by simp
        _ ≤ b * c := Nat.mul_le_mul_left b hc_pos
    omega
  have hkp_lt : kp < b := by
    have hmul : Q * kp < Q * b := by
      rw [Nat.mul_comm Q b]
      omega
    exact Nat.lt_of_mul_lt_mul_left hmul
  let cm : ℕ := Q - c
  let km : ℕ := b - kp
  have hcm_pos : 0 < cm := by dsimp [cm]; omega
  have hcm_lt : cm < Q := by dsimp [cm]; omega
  have hkm_pos : 0 < km := by dsimp [km]; omega
  have hkm_lt : km < b := by dsimp [km]; omega
  have hminus : b * cm + 1 = Q * km := by
    dsimp [cm, km]
    calc
      b * (Q - c) + 1 = (b * Q - b * c) + 1 := by
        rw [Nat.mul_sub_left_distrib]
      _ = b * Q - Q * kp := by omega
      _ = Q * b - Q * kp := by rw [Nat.mul_comm b Q]
      _ = Q * (b - kp) := by rw [Nat.mul_sub_left_distrib]
  have hkadd : kp + km = b := by dsimp [km]; omega
  exact
    { cPlus := c
      cMinus := cm
      kPlus := kp
      kMinus := km
      cPlus_pos := hc_pos
      cPlus_lt := hc_lt
      cMinus_pos := hcm_pos
      cMinus_lt := hcm_lt
      plus_eq := hplus
      minus_eq := hminus
      kPlus_pos := hkp_pos
      kPlus_lt := hkp_lt
      kMinus_pos := hkm_pos
      kMinus_lt := hkm_lt
      k_add := hkadd }

/-- At least one complementary quotient coefficient is a `p`-unit. -/
theorem exists_not_dvd_coefficient
    {Q b p : ℕ} (w : ComplementaryPair Q b) (hpb : ¬p ∣ b) :
    ¬p ∣ w.kPlus ∨ ¬p ∣ w.kMinus := by
  by_contra h
  simp only [not_or, not_not] at h
  exact hpb (w.k_add ▸ Nat.dvd_add h.1 h.2)

/-- For a prime current `Q`, both quotient coefficients are current units. -/
theorem both_not_dvd_of_current_prime
    {Q b : ℕ} (w : ComplementaryPair Q b) (_hQ : Q.Prime) (hbQ : b < Q) :
    ¬Q ∣ w.kPlus ∧ ¬Q ∣ w.kMinus := by
  constructor
  · intro hd
    have hkQ : w.kPlus < Q := lt_trans w.kPlus_lt hbQ
    exact (Nat.not_dvd_of_pos_of_lt w.kPlus_pos hkQ) hd
  · intro hd
    have hkQ : w.kMinus < Q := lt_trans w.kMinus_lt hbQ
    exact (Nat.not_dvd_of_pos_of_lt w.kMinus_pos hkQ) hd

end SignedInverse
end Erdos289
