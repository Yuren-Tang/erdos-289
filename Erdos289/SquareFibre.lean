module

/-
Copyright (c) 2026 Yuren Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuren Tang
-/

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.ZMod.UnitsCyclic

@[expose] public section

/-!
# Square fibres of prime-power unit groups

A downwardness exception of the signed-inverse construction forces its carrier
to solve a quadratic congruence modulo the current prime power.  What the row
certificate needs from that is only a *uniform* bound on the number of
solutions, and this module supplies it: a square fibre of `(ZMod (p ^ e))ˣ`
has at most four points, whatever the prime `p` and the exponent `e`.

The two branches are genuinely different.  For odd `p` the unit group is
cyclic, so the two-torsion has order at most two.  For `p = 2` the unit group
is not cyclic beyond `e = 2`, and the bound comes from the elementary fact that
an odd square root of one modulo `2 ^ e` is congruent to `±1` modulo
`2 ^ (e - 1)`.  Neither branch is a case distinction of the provider: only the
uniform four-point bound crosses the boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Erdos289

/-- Every nonempty fibre of a homomorphism from a finite group is a coset of
its kernel. -/
theorem card_fibre_eq_card_ker
    {G M : Type*} [Group G] [Fintype G] [Monoid M] [DecidableEq M]
    (f : G →* M) (y : M) (hy : y ∈ Set.range f) :
    (Finset.univ.filter fun x ↦ f x = y).card = Nat.card f.ker := by
  calc
    (Finset.univ.filter fun x ↦ f x = y).card =
        (Finset.univ.filter fun x ↦ f x = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range f hy ⟨1, map_one f⟩
    _ = (f.ker : Set G).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext x
      simp [MonoidHom.mem_ker]
    _ = Nat.card f.ker := (Nat.card_coe_set_eq (f.ker : Set G)).symm

/-- A square fibre in a finite commutative group has cardinality equal to the
two-torsion kernel whenever it is nonempty. -/
theorem card_squareFibre_eq_card_twoTorsion
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] (y : G)
    (hy : ∃ x : G, x ^ 2 = y) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card =
      Nat.card (powMonoidHom 2 : G →* G).ker := by
  apply card_fibre_eq_card_ker (powMonoidHom 2 : G →* G) y
  simpa only [powMonoidHom_apply, Set.mem_range] using hy

/-- Odd prime-power unit square fibres have at most two points. -/
theorem oddPrimePower_squareFibre_card_le_two
    {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (hp2 : p ≠ 2)
    (y : (ZMod (p ^ e))ˣ) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card ≤ 2 := by
  let _ : IsCyclic (ZMod (p ^ e))ˣ :=
    ZMod.isCyclic_units_of_prime_pow p hp hp2 e
  by_cases hy : ∃ x : (ZMod (p ^ e))ˣ, x ^ 2 = y
  · rw [card_squareFibre_eq_card_twoTorsion y hy,
      IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right _ (by omega)
  · simp only [not_exists] at hy
    simp [hy]

/-! ### The `p = 2` branch -/

/-- A power of two dividing a product of consecutive naturals divides one of
them, because the odd one is coprime to it. -/
private theorem two_pow_dvd_consecutive {k m : ℕ} (h : 2 ^ k ∣ m * (m + 1)) :
    2 ^ k ∣ m ∨ 2 ^ k ∣ m + 1 := by
  rcases Nat.even_or_odd m with hm | hm
  · left
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ h
    exact Nat.Coprime.pow_left _
      ((Nat.prime_two.coprime_iff_not_dvd).2 (by
        rcases hm with ⟨t, ht⟩
        omega))
  · right
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ (by rwa [mul_comm] at h)
    exact Nat.Coprime.pow_left _
      ((Nat.prime_two.coprime_iff_not_dvd).2 (by
        rcases hm with ⟨t, ht⟩
        omega))

/-- An odd square root of one modulo `2 ^ e` is `±1` modulo `2 ^ (e - 1)`. -/
private theorem odd_sq_eq_one_mod_two_pow {e v : ℕ} (he : 2 ≤ e)
    (hodd : ¬ 2 ∣ v) (h : 2 ^ e ∣ v ^ 2 - 1) :
    2 ^ (e - 1) ∣ v - 1 ∨ 2 ^ (e - 1) ∣ v + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, v = 2 * m + 1 := ⟨v / 2, by omega⟩
  have hsq : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
  have h4 : 2 ^ e ∣ 4 * (m * (m + 1)) := by
    have : (2 * m + 1) ^ 2 - 1 = 4 * (m * (m + 1)) := by omega
    rwa [this] at h
  have hsplit : 2 ^ (e - 2) ∣ m * (m + 1) := by
    have hpow : (2 : ℕ) ^ 2 * 2 ^ (e - 2) = 2 ^ e := by
      rw [← pow_add]
      congr 1
      omega
    have h4' : (2 : ℕ) ^ 2 * 2 ^ (e - 2) ∣ 2 ^ 2 * (m * (m + 1)) := by
      rw [hpow]
      simpa using h4
    exact (mul_dvd_mul_iff_left (a := (2 : ℕ) ^ 2) (by positivity)).1 h4'
  have hstep : (2 : ℕ) ^ (e - 1) = 2 * 2 ^ (e - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  rcases two_pow_dvd_consecutive hsplit with hm | hm
  · left
    have : (2 * m + 1) - 1 = 2 * m := by omega
    rw [this, hstep]
    exact mul_dvd_mul_left 2 hm
  · right
    have : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    rw [this, hstep]
    exact mul_dvd_mul_left 2 hm

/-- A residue below `2 P` that is `± 1` modulo `P` is one of four values. -/
private theorem eq_of_dvd_pred_or_succ {P v : ℕ} (hPpos : 0 < P) (hv1 : 1 ≤ v)
    (hvlt : v < 2 * P) (hk : P ∣ v - 1 ∨ P ∣ v + 1) :
    v = 1 ∨ v = 1 + P ∨ v = P - 1 ∨ v = 2 * P - 1 := by
  rcases hk with ⟨t, ht⟩ | ⟨t, ht⟩
  · have hmul : P * t < P * 2 := by omega
    have htlt : t < 2 := Nat.lt_of_mul_lt_mul_left hmul
    interval_cases t <;> omega
  · have hmul : P * t ≤ P * 2 := by omega
    have htle : t ≤ 2 := Nat.le_of_mul_le_mul_left hmul hPpos
    have htpos : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at ht; omega
      · exact h0
    interval_cases t <;> omega

/-- The two-torsion of `(ZMod (2 ^ e))ˣ` has at most four elements. -/
private theorem twoPower_twoTorsion_card_le_four {e : ℕ} [NeZero (2 ^ e)] :
    (Finset.univ.filter fun x : (ZMod (2 ^ e))ˣ ↦ x ^ 2 = 1).card ≤ 4 := by
  classical
  rcases Nat.lt_or_ge e 2 with he | he
  · have hsmall : Fintype.card (ZMod (2 ^ e))ˣ ≤ 2 ^ e := by
      refine le_trans (Fintype.card_le_of_injective
        (Units.val : (ZMod (2 ^ e))ˣ → ZMod (2 ^ e)) Units.val_injective) ?_
      exact le_of_eq (ZMod.card (2 ^ e))
    have hle : (2 : ℕ) ^ e ≤ 4 := by
      calc (2 : ℕ) ^ e ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ 4 := by norm_num
    calc (Finset.univ.filter fun x : (ZMod (2 ^ e))ˣ ↦ x ^ 2 = 1).card
        ≤ (Finset.univ : Finset (ZMod (2 ^ e))ˣ).card := Finset.card_filter_le _ _
      _ = Fintype.card (ZMod (2 ^ e))ˣ := Finset.card_univ
      _ ≤ 4 := le_trans hsmall hle
  · set P : ℕ := 2 ^ (e - 1) with hP
    have hPpos : 0 < P := pow_pos (by norm_num) _
    have hPe : (2 : ℕ) ^ e = 2 * P := by
      rw [hP, ← pow_succ']
      congr 1
      omega
    have hinj : Set.InjOn (fun x : (ZMod (2 ^ e))ˣ => (x : ZMod (2 ^ e)).val)
        (Finset.univ.filter fun x : (ZMod (2 ^ e))ˣ ↦ x ^ 2 = 1) := by
      intro a _ b _ hab
      exact Units.val_injective (ZMod.val_injective _ hab)
    have hcard : ({1, 1 + P, P - 1, 2 * P - 1} : Finset ℕ).card ≤ 4 := by
      calc ({1, 1 + P, P - 1, 2 * P - 1} : Finset ℕ).card
          ≤ ({1 + P, P - 1, 2 * P - 1} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
        _ ≤ (({P - 1, 2 * P - 1} : Finset ℕ).card + 1) + 1 :=
            Nat.succ_le_succ (Finset.card_insert_le _ _)
        _ ≤ ((({2 * P - 1} : Finset ℕ).card + 1) + 1) + 1 :=
            Nat.succ_le_succ (Nat.succ_le_succ (Finset.card_insert_le _ _))
        _ = 4 := by simp
    refine le_trans (Finset.card_le_card_of_injOn
      (t := ({1, 1 + P, P - 1, 2 * P - 1} : Finset ℕ)) _ ?_ hinj) hcard
    · intro x hx
      show (x : ZMod (2 ^ e)).val ∈ ({1, 1 + P, P - 1, 2 * P - 1} : Finset ℕ)
      set v : ℕ := (x : ZMod (2 ^ e)).val with hv
      have hvlt : v < 2 ^ e := ZMod.val_lt _
      have hcop : Nat.Coprime v (2 ^ e) := ZMod.val_coe_unit_coprime x
      have hodd : ¬ 2 ∣ v := by
        intro h2
        have hg : (2 : ℕ) ∣ Nat.gcd v (2 ^ e) :=
          Nat.dvd_gcd h2 (dvd_pow_self 2 (by omega))
        rw [hcop] at hg
        omega
      have hv1 : 1 ≤ v := by
        rcases Nat.eq_zero_or_pos v with h0 | h0
        · exact absurd (h0 ▸ dvd_zero 2) hodd
        · exact h0
      have hx2 : (x : ZMod (2 ^ e)) ^ 2 = 1 := by
        have hxx := (Finset.mem_filter.mp hx).2
        calc (x : ZMod (2 ^ e)) ^ 2
            = ((x ^ 2 : (ZMod (2 ^ e))ˣ) : ZMod (2 ^ e)) := by push_cast; ring
          _ = ((1 : (ZMod (2 ^ e))ˣ) : ZMod (2 ^ e)) := by rw [hxx]
          _ = 1 := Units.val_one
      have hcast : ((v ^ 2 : ℕ) : ZMod (2 ^ e)) = ((1 : ℕ) : ZMod (2 ^ e)) := by
        push_cast
        rw [hv, ZMod.natCast_val, ZMod.cast_id]
        simpa using hx2
      have hmod : v ^ 2 ≡ 1 [MOD 2 ^ e] :=
        (ZMod.natCast_eq_natCast_iff _ _ _).1 hcast
      have hone : 1 ≤ v ^ 2 := Nat.one_le_pow 2 v hv1
      have hdvd : 2 ^ e ∣ v ^ 2 - 1 := (Nat.modEq_iff_dvd' hone).1 hmod.symm
      rw [hPe] at hvlt
      have hkey : P ∣ v - 1 ∨ P ∣ v + 1 := by
        rw [hP]
        exact odd_sq_eq_one_mod_two_pow he hodd hdvd
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact eq_of_dvd_pred_or_succ hPpos hv1 hvlt hkey

/-- Two-power unit square fibres have at most four points. -/
theorem twoPower_squareFibre_card_le_four
    {e : ℕ} [NeZero (2 ^ e)] (y : (ZMod (2 ^ e))ˣ) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card ≤ 4 := by
  classical
  by_cases hy : ∃ x : (ZMod (2 ^ e))ˣ, x ^ 2 = y
  · rw [card_squareFibre_eq_card_twoTorsion y hy,
      ← card_squareFibre_eq_card_twoTorsion (1 : (ZMod (2 ^ e))ˣ) ⟨1, one_pow 2⟩]
    exact twoPower_twoTorsion_card_le_four
  · simp only [not_exists] at hy
    simp [hy]

/-- Uniform four-point bound for prime-power unit square fibres. -/
theorem primePower_squareFibre_card_le_four
    {p e : ℕ} [NeZero (p ^ e)] (hp : p.Prime) (y : (ZMod (p ^ e))ˣ) :
    (Finset.univ.filter fun x ↦ x ^ 2 = y).card ≤ 4 := by
  by_cases hp2 : p = 2
  · subst hp2
    exact twoPower_squareFibre_card_le_four y
  · exact le_trans (oddPrimePower_squareFibre_card_le_two hp hp2 y) (by norm_num)

end Erdos289
