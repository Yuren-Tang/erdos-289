module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Erdos289.RowSupply
public import Erdos289.SquareFibre
public import Erdos289.LocalProfiles

@[expose] public section

/-!
# Carriers of a band that admit no usable orientation

A carrier of the comparable band fails to admit a usable orientation only if it
solves a quadratic congruence modulo the current prime power.  On the band
`(⌊(Q-1)/4⌋, 4⌊(Q-1)/4⌋]` one has `Q ≤ 4 b`, so the multiplier of that
congruence is at most three; and the multiplier is prime to the current, because
a common factor would divide `1`.

Together with the uniform four-point bound for square fibres
(`Erdos289.primePower_squareFibre_card_le_four`) this is the deletion step of
the row certificate: the band supplies `≫ Q / log Q` carriers and only `O(1)`
of them are lost.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289
namespace SignedInverse

/-- On a band of ratio `Λ` the current is at most `Λ` times any carrier. -/
theorem current_le_ratio_mul {Λ Q p b : ℕ} (hΛ : 0 < Λ)
    (hb : b ∈ carrierPrimes Λ Q p (bandBase Λ Q)) :
    Q ≤ Λ * b := by
  have hlow := (mem_carrierPrimes_iff.mp hb).1
  have hstep : Λ * (bandBase Λ Q + 1) ≤ Λ * b :=
    Nat.mul_le_mul_left _ (by omega)
  have hQ := le_ratio_mul_bandBase_add (Λ := Λ) (Q := Q) hΛ
  have hexp : Λ * (bandBase Λ Q + 1) = Λ * bandBase Λ Q + Λ := by ring
  omega

/--
A carrier of a band of ratio `Λ` with no usable orientation solves
`ell * b ^ 2 = ± 1` modulo the current, with `1 ≤ ell < Λ` and `ell` prime to
the current.  The multiplier is bounded by the band ratio and by nothing else.
-/
theorem exists_multiplier_of_goodOrientations_eq_empty
    {Λ Q p : ℕ} (hΛ : 0 < Λ) (hp : p.Prime) (hpQ : p ∣ Q) (hQ1 : 1 < Q)
    (x : Carrier Q p) (hb : x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q))
    (hbad : (x.pair hQ1).goodOrientations p = ∅) :
    ∃ ell : ℕ, 1 ≤ ell ∧ ell < Λ ∧ ¬ p ∣ ell ∧
      ((ell : ZMod Q) * (x.b : ZMod Q) ^ 2 = 1 ∨
        (ell : ZMod Q) * (x.b : ZMod Q) ^ 2 = -1) := by
  classical
  set w := x.pair hQ1 with hw
  have hbprime : x.b.Prime := (mem_carrierPrimes_iff.mp hb).2.2.1
  have hpb : ¬ p ∣ x.b := by
    intro hdvd
    exact (mem_carrierPrimes_iff.mp hb).2.2.2.2
      ((Nat.prime_dvd_prime_iff_eq hp hbprime).1 hdvd).symm
  -- some orientation has a current-unit coefficient
  obtain ⟨s, hs⟩ : ∃ s : Orientation, ¬ p ∣ w.coefficient s := by
    rcases exists_not_dvd_coefficient w hpb with h | h
    · exact ⟨Orientation.plus, h⟩
    · exact ⟨Orientation.minus, h⟩
  -- so that orientation must fail the downwardness condition
  have hcop : ¬ x.b.Coprime (w.inverseRepresentative s) := by
    intro hc
    have hnot : s ∉ w.goodOrientations p := by
      rw [hbad]
      exact Finset.notMem_empty s
    exact hnot ((w.mem_goodOrientations_iff s).2 ⟨hs, hc⟩)
  obtain ⟨ell, hell, hquad⟩ := w.exception_quadratic_shape hbprime s hcop
  -- the multiplier is bounded because the inverse representative is below `Q`
  have hlt : w.inverseRepresentative s < Q := by
    cases s with
    | plus => exact w.cPlus_lt
    | minus => exact w.cMinus_lt
  have hpos : 0 < w.inverseRepresentative s := by
    cases s with
    | plus => exact w.cPlus_pos
    | minus => exact w.cMinus_pos
  have hQ4 : Q ≤ Λ * x.b := current_le_ratio_mul hΛ hb
  have hell1 : 1 ≤ ell := by
    rcases Nat.eq_zero_or_pos ell with h0 | h0
    · rw [h0, Nat.zero_mul] at hell
      omega
    · exact h0
  have hellΛ : ell < Λ := by
    by_contra hcon
    have h4 : Λ * x.b ≤ ell * x.b := Nat.mul_le_mul (by omega) (le_refl x.b)
    rw [hell] at hlt
    omega
  refine ⟨ell, hell1, hellΛ, ?_, ?_⟩
  · -- a common factor with the current would divide one
    intro hpell
    have hdvdell : p ∣ ell * x.b ^ 2 := Dvd.dvd.mul_right hpell _
    have hone : p ∣ 1 := by
      cases s with
      | plus =>
          have heq : ell * x.b ^ 2 = Q * w.kPlus + 1 := by simpa using hquad
          have h2 : p ∣ Q * w.kPlus := Dvd.dvd.mul_right hpQ _
          rw [heq] at hdvdell
          exact (Nat.dvd_add_right h2).1 hdvdell
      | minus =>
          have heq : ell * x.b ^ 2 + 1 = Q * w.kMinus := by simpa using hquad
          have h2 : p ∣ Q * w.kMinus := Dvd.dvd.mul_right hpQ _
          rw [← heq] at h2
          exact (Nat.dvd_add_right hdvdell).1 h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 hone)
  · cases s with
    | plus =>
        left
        have heq : ell * x.b ^ 2 = Q * w.kPlus + 1 := by simpa using hquad
        have := congrArg (fun n : ℕ => (n : ZMod Q)) heq
        push_cast at this
        simpa [ZMod.natCast_self] using this
    | minus =>
        right
        have heq : ell * x.b ^ 2 + 1 = Q * w.kMinus := by simpa using hquad
        have := congrArg (fun n : ℕ => (n : ZMod Q)) heq
        push_cast at this
        simp only [ZMod.natCast_self, zero_mul] at this
        linear_combination this

/-- The unit of the current ring attached to a carrier. -/
noncomputable def Carrier.unit {Q p : ℕ} [NeZero Q] (x : Carrier Q p) : (ZMod Q)ˣ :=
  ZMod.unitOfCoprime x.b x.coprime

@[simp]
theorem Carrier.unit_val {Q p : ℕ} [NeZero Q] (x : Carrier Q p) :
    (x.unit : ZMod Q) = (x.b : ZMod Q) :=
  ZMod.coe_unitOfCoprime _ _

theorem Carrier.unit_injOn {Q p : ℕ} [NeZero Q] :
    Function.Injective (Carrier.unit : Carrier Q p → (ZMod Q)ˣ) := by
  intro a b hab
  have hval : ((a.b : ℕ) : ZMod Q) = ((b.b : ℕ) : ZMod Q) := by
    rw [← Carrier.unit_val, ← Carrier.unit_val, hab]
  have : a.b = b.b := by
    have ha := ZMod.val_cast_of_lt a.b_lt
    have hb := ZMod.val_cast_of_lt b.b_lt
    rw [← ha, ← hb, hval]
  exact Carrier.b_injective this

/--
Only boundedly many carriers of a band admit no usable orientation, and the
bound is forced by the band ratio alone: there are `Λ - 1` admissible
multipliers, two signs, and at most four square roots of each resulting unit,
hence at most `8 (Λ - 1)` bad carriers, independently of the current.
-/
theorem card_badCarriers_le
    {Λ Q p e : ℕ} (hΛ : 0 < Λ) (hp : p.Prime) (hQ : Q = p ^ e) (hQ1 : 1 < Q)
    (A : Finset (Carrier Q p))
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q))
    (hbad : ∀ x ∈ A, (x.pair hQ1).goodOrientations p = ∅) :
    A.card ≤ 8 * (Λ - 1) := by
  classical
  subst hQ
  have : NeZero (p ^ e) := ⟨by omega⟩
  have hpQ : p ∣ p ^ e := dvd_pow_self p (by rintro rfl; simp at hQ1)
  set f : Carrier (p ^ e) p → (ZMod (p ^ e))ˣ := fun x => x.unit ^ 2 with hf
  have hfib : ∀ y ∈ A.image f, (A.filter fun x => f x = y).card ≤ 4 := by
    intro y _
    refine le_trans (Finset.card_le_card_of_injOn Carrier.unit ?_ ?_)
      (primePower_squareFibre_card_le_four hp y)
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2⟩
    · intro a _ b _ hab
      exact Carrier.unit_injOn hab
  have himg : (A.image f).card ≤ 2 * (Λ - 1) := by
    set T : Finset (ZMod (p ^ e)) :=
      ((Finset.Ico 1 Λ).image fun l : ℕ => ((l : ZMod (p ^ e))⁻¹)) ∪
        ((Finset.Ico 1 Λ).image fun l : ℕ => -((l : ZMod (p ^ e))⁻¹)) with hT
    have hIco : (Finset.Ico 1 Λ).card = Λ - 1 := by
      rw [Nat.card_Ico]
    have hTcard : T.card ≤ 2 * (Λ - 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : ((Finset.Ico 1 Λ).image
          fun l : ℕ => ((l : ZMod (p ^ e))⁻¹)).card ≤ Λ - 1 :=
        le_trans Finset.card_image_le (le_of_eq hIco)
      have h2 : ((Finset.Ico 1 Λ).image
          fun l : ℕ => -((l : ZMod (p ^ e))⁻¹)).card ≤ Λ - 1 :=
        le_trans Finset.card_image_le (le_of_eq hIco)
      omega
    have hsub : (A.image f).image (Units.val) ⊆ T := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      obtain ⟨ell, hell1, hellΛ, hpell, hsq⟩ :=
        exists_multiplier_of_goodOrientations_eq_empty hΛ hp hpQ hQ1 x
          (hband x hx) (hbad x hx)
      have hcop : Nat.Coprime ell (p ^ e) :=
        Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpell).symm
      have hunit : IsUnit ((ell : ℕ) : ZMod (p ^ e)) :=
        (ZMod.isUnit_iff_coprime ell (p ^ e)).2 hcop
      have hinv : ((ell : ℕ) : ZMod (p ^ e))⁻¹ * ((ell : ℕ) : ZMod (p ^ e)) = 1 :=
        ZMod.inv_mul_of_unit _ hunit
      have hmem3 : ell ∈ Finset.Ico 1 Λ := Finset.mem_Ico.mpr ⟨hell1, hellΛ⟩
      have hval : ((x.unit ^ 2 : (ZMod (p ^ e))ˣ) : ZMod (p ^ e))
          = (x.b : ZMod (p ^ e)) ^ 2 := by
        rw [Units.val_pow_eq_pow_val, Carrier.unit_val]
      rw [hT, Finset.mem_union]
      rcases hsq with hsq | hsq
      · left
        refine Finset.mem_image.mpr ⟨ell, hmem3, ?_⟩
        rw [hval]
        calc ((ell : ℕ) : ZMod (p ^ e))⁻¹
            = ((ell : ℕ) : ZMod (p ^ e))⁻¹ *
                (((ell : ℕ) : ZMod (p ^ e)) * (x.b : ZMod (p ^ e)) ^ 2) := by
              rw [hsq, mul_one]
          _ = (x.b : ZMod (p ^ e)) ^ 2 := by rw [← mul_assoc, hinv, one_mul]
      · right
        refine Finset.mem_image.mpr ⟨ell, hmem3, ?_⟩
        rw [hval]
        calc -((ell : ℕ) : ZMod (p ^ e))⁻¹
            = ((ell : ℕ) : ZMod (p ^ e))⁻¹ *
                (((ell : ℕ) : ZMod (p ^ e)) * (x.b : ZMod (p ^ e)) ^ 2) := by
              rw [hsq]
              ring
          _ = (x.b : ZMod (p ^ e)) ^ 2 := by rw [← mul_assoc, hinv, one_mul]
    calc (A.image f).card
        = ((A.image f).image (Units.val)).card :=
          (Finset.card_image_of_injective _ Units.val_injective).symm
      _ ≤ T.card := Finset.card_le_card hsub
      _ ≤ 2 * (Λ - 1) := hTcard
  calc A.card ≤ (A.image f).card * 4 :=
        Erdos289.Finset.card_le_card_image_mul_of_fibre_bound A f 4 hfib
    _ ≤ (2 * (Λ - 1)) * 4 := Nat.mul_le_mul_right _ himg
    _ = 8 * (Λ - 1) := by ring

/-- The carriers of a band that admit a usable orientation. -/
noncomputable def goodCarriers {Q p : ℕ} (hQ1 : 1 < Q) (A : Finset (Carrier Q p)) :
    Finset (Carrier Q p) := by
  classical
  exact A.filter fun x => ((x.pair hQ1).goodOrientations p).Nonempty

/--
Assembly of the deletion step: a family of band carriers loses at most
`8 (Λ - 1)` members to downwardness exceptions, where `Λ` is the band ratio.
-/
theorem card_goodCarriers_ge
    {Λ Q p e : ℕ} (hΛ : 0 < Λ) (hp : p.Prime) (hQ : Q = p ^ e) (hQ1 : 1 < Q)
    (A : Finset (Carrier Q p))
    (hband : ∀ x ∈ A, x.b ∈ carrierPrimes Λ Q p (bandBase Λ Q)) :
    A.card - 8 * (Λ - 1) ≤ (goodCarriers hQ1 A).card := by
  classical
  subst hQ
  set P : Carrier (p ^ e) p → Prop :=
    fun x => ((x.pair hQ1).goodOrientations p).Nonempty with hPdef
  have hsplit : (A.filter P).card + (A.filter fun x => ¬ P x).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have hbadle : (A.filter fun x => ¬ P x).card ≤ 8 * (Λ - 1) := by
    refine card_badCarriers_le hΛ hp rfl hQ1 _
      (fun x hx => hband x (Finset.mem_filter.mp hx).1) (fun x hx => ?_)
    have := (Finset.mem_filter.mp hx).2
    rw [hPdef] at this
    exact Finset.not_nonempty_iff_eq_empty.mp this
  have : (goodCarriers hQ1 A).card = (A.filter P).card := rfl
  omega

end SignedInverse
end Erdos289
